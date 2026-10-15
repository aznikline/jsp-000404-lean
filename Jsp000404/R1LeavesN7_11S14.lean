import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_11S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 16818000 in
set_option maxHeartbeats 16818000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s1 m hb0 hb2 hb3 hb5 h0 h1
  · rcases m.htr 0 1 5 (by decide) (by decide) with h7715 | h7715
    · rcases m.htr 0 2 3 (by decide) (by decide) with h7716 | h7716
      · linarith only [h0, h1, h7716, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h7718 | h7718
        · rcases m.htr 0 2 5 (by decide) (by decide) with h7719 | h7719
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7720 | h7720
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7721 | h7721
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7722 | h7722
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7723 | h7723
                  · linarith only [h7716, h7723, hc12, hlam, hphi, ht01, u0ehi1]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7725 | h7725
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7726 | h7726
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7727 | h7727
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7728 | h7728
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7729 | h7729
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7730 | h7730
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7731 | h7731
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7732 | h7732
                                  · rcases h2bigk with h7733c | h7733c | h7733c | h7733c | h7733c | h7733c | h7733c | h7733c | h7733c | h7733c | h7733c | h7733c | h7733c | h7733c | h7733c | h7733c | h7733c | h7733c | h7733c | h7733c | h7733c | h7733c | h7733c | h7733c | h7733c
                                    · have p7733_0 := h7733c.1
                                      have p7733_1 := h7733c.2.1
                                      have p7733_2 := h7733c.2.2.1
                                      have p7733_3 := h7733c.2.2.2
                                      linarith only [hlam, p7733_0]
                                    · have p7733_0 := h7733c.1
                                      have p7733_1 := h7733c.2.1
                                      have p7733_2 := h7733c.2.2.1
                                      have p7733_3 := h7733c.2.2.2
                                      linarith only [h0, h1, h7723, hc12, hc23, hlam, hphi, p7733_1]
                                    · have p7733_0 := h7733c.1
                                      have p7733_1 := h7733c.2.1
                                      have p7733_2 := h7733c.2.2.1
                                      have p7733_3 := h7733c.2.2.2
                                      linarith only [h7716, hlam, p7733_0]
                                    · have p7733_0 := h7733c.1
                                      have p7733_1 := h7733c.2.1
                                      have p7733_2 := h7733c.2.2.1
                                      have p7733_3 := h7733c.2.2.2
                                      linarith only [h0, h1, h7723, h7729, h7732, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7733_1]
                                    · have p7733_0 := h7733c.1
                                      have p7733_1 := h7733c.2.1
                                      have p7733_2 := h7733c.2.2.1
                                      have p7733_3 := h7733c.2.2.2
                                      rcases p7733_3 (m.d 0 2) (by simp) with h7738 | h7738
                                      · rcases p7733_3 (m.d 1 2) (by simp) with h7739 | h7739
                                        · linarith only [h0, h7739, hlam]
                                        · linarith only [h7725, h7739, hlam]
                                      · linarith only [h7738, hlam, p7733_0]
                                    · have p7733_0 := h7733c.1
                                      have p7733_1 := h7733c.2.1
                                      have p7733_2 := h7733c.2.2.1
                                      have p7733_3 := h7733c.2.2.2
                                      linarith only [h0, hlam, p7733_0]
                                    · have p7733_0 := h7733c.1
                                      have p7733_1 := h7733c.2.1
                                      have p7733_2 := h7733c.2.2.1
                                      have p7733_3 := h7733c.2.2.2
                                      linarith only [hlam, p7733_0]
                                    · have p7733_0 := h7733c.1
                                      have p7733_1 := h7733c.2.1
                                      have p7733_2 := h7733c.2.2.1
                                      have p7733_3 := h7733c.2.2.2
                                      linarith only [h7723, hlam, p7733_0]
                                    · have p7733_0 := h7733c.1
                                      have p7733_1 := h7733c.2.1
                                      have p7733_2 := h7733c.2.2.1
                                      have p7733_3 := h7733c.2.2.2
                                      linarith only [h0, h1, h7723, h7729, h7732, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7733_1]
                                    · have p7733_0 := h7733c.1
                                      have p7733_1 := h7733c.2.1
                                      have p7733_2 := h7733c.2.2.1
                                      have p7733_3 := h7733c.2.2.2
                                      linarith only [h0, h1, h7723, h7730, h7732, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7733_1]
                                    · have p7733_0 := h7733c.1
                                      have p7733_1 := h7733c.2.1
                                      have p7733_2 := h7733c.2.2.1
                                      have p7733_3 := h7733c.2.2.2
                                      linarith only [hc23, hlam, hphi, ht01, ht12, p7733_1, u0ehi1]
                                    · have p7733_0 := h7733c.1
                                      have p7733_1 := h7733c.2.1
                                      have p7733_2 := h7733c.2.2.1
                                      have p7733_3 := h7733c.2.2.2
                                      rcases p7733_3 (m.d 0 2) (by simp) with h7749 | h7749
                                      · linarith only [h7716, h7749, hlam]
                                      · linarith only [h0, h7749, hlam]
                                    · have p7733_0 := h7733c.1
                                      have p7733_1 := h7733c.2.1
                                      have p7733_2 := h7733c.2.2.1
                                      have p7733_3 := h7733c.2.2.2
                                      linarith only [hlam, p7733_0]
                                    · have p7733_0 := h7733c.1
                                      have p7733_1 := h7733c.2.1
                                      have p7733_2 := h7733c.2.2.1
                                      have p7733_3 := h7733c.2.2.2
                                      rcases p7733_3 (m.d 0 2) (by simp) with h7753 | h7753
                                      · linarith only [h7716, h7753, hlam]
                                      · linarith only [h7718, h7753, hlam]
                                    · have p7733_0 := h7733c.1
                                      have p7733_1 := h7733c.2.1
                                      have p7733_2 := h7733c.2.2.1
                                      have p7733_3 := h7733c.2.2.2
                                      linarith only [h0, h1, h7723, h7725, hlam, p7733_2]
                                    · have p7733_0 := h7733c.1
                                      have p7733_1 := h7733c.2.1
                                      have p7733_2 := h7733c.2.2.1
                                      have p7733_3 := h7733c.2.2.2
                                      linarith only [h7718, hlam, p7733_0]
                                    · have p7733_0 := h7733c.1
                                      have p7733_1 := h7733c.2.1
                                      have p7733_2 := h7733c.2.2.1
                                      have p7733_3 := h7733c.2.2.2
                                      linarith only [h7718, h7725, hc02, hc25, hlam, hphi, ht0b, ht5b, p7733_1]
                                    · have p7733_0 := h7733c.1
                                      have p7733_1 := h7733c.2.1
                                      have p7733_2 := h7733c.2.2.1
                                      have p7733_3 := h7733c.2.2.2
                                      linarith only [h7729, hlam, p7733_1]
                                    · have p7733_0 := h7733c.1
                                      have p7733_1 := h7733c.2.1
                                      have p7733_2 := h7733c.2.2.1
                                      have p7733_3 := h7733c.2.2.2
                                      linarith only [hlam, p7733_0]
                                    · have p7733_0 := h7733c.1
                                      have p7733_1 := h7733c.2.1
                                      have p7733_2 := h7733c.2.2.1
                                      have p7733_3 := h7733c.2.2.2
                                      linarith only [h0, h1, h7718, h7723, h7730, h7732, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7733_1]
                                    · have p7733_0 := h7733c.1
                                      have p7733_1 := h7733c.2.1
                                      have p7733_2 := h7733c.2.2.1
                                      have p7733_3 := h7733c.2.2.2
                                      linarith only [h7719, hlam, p7733_0]
                                    · have p7733_0 := h7733c.1
                                      have p7733_1 := h7733c.2.1
                                      have p7733_2 := h7733c.2.2.1
                                      have p7733_3 := h7733c.2.2.2
                                      linarith only [h7725, hlam, p7733_0]
                                    · have p7733_0 := h7733c.1
                                      have p7733_1 := h7733c.2.1
                                      have p7733_2 := h7733c.2.2.1
                                      have p7733_3 := h7733c.2.2.2
                                      linarith only [h7730, hlam, p7733_1]
                                    · have p7733_0 := h7733c.1
                                      have p7733_1 := h7733c.2.1
                                      have p7733_2 := h7733c.2.2.1
                                      have p7733_3 := h7733c.2.2.2
                                      linarith only [h7731, hlam, p7733_0]
                                    · have p7733_0 := h7733c.1
                                      have p7733_1 := h7733c.2.1
                                      have p7733_2 := h7733c.2.2.1
                                      have p7733_3 := h7733c.2.2.2
                                      linarith only [hlam, p7733_0]
                                  · linarith only [h0, h1, h7718, h7723, h7731, h7732, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7768 | h7768
                                  · linarith only [h7729, h7731, h7768, hlam]
                                  · rcases h2bigk with h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c | h7770c
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [hlam, p7770_0]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [h0, h1, h7723, h7725, h7728, h7729, h7731, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7770_1]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [h7716, hlam, p7770_0]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      rcases p7770_3 (m.d 0 2) (by simp) with h7774 | h7774
                                      · rcases p7770_3 (m.d 1 2) (by simp) with h7775 | h7775
                                        · linarith only [h0, h7775, hlam]
                                        · linarith only [h7725, h7728, h7731, h7775, hlam]
                                      · linarith only [h7774, hlam, p7770_0]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      rcases p7770_3 (m.d 0 2) (by simp) with h7779 | h7779
                                      · rcases p7770_3 (m.d 1 2) (by simp) with h7780 | h7780
                                        · linarith only [h0, h7780, hlam]
                                        · linarith only [h7725, h7780, hlam]
                                      · linarith only [h7779, hlam, p7770_0]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [h0, hlam, p7770_0]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [hlam, p7770_0]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [h7723, hlam, p7770_0]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [h0, h1, h7723, h7729, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7770_1]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [h0, h1, h7723, h7729, h7731, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7770_1]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [hc23, hlam, hphi, ht01, ht12, p7770_1, u0ehi1]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      rcases p7770_3 (m.d 0 2) (by simp) with h7790 | h7790
                                      · linarith only [h7716, h7790, hlam]
                                      · linarith only [h0, h7790, hlam]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [hlam, p7770_0]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [h0, h1, h7718, h7722, h7723, h7731, hlam, p7770_2]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [h0, h1, h7723, h7725, hlam, p7770_2]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [h7718, hlam, p7770_0]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [h0, h7718, h7722, h7731, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7770_1]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [h7729, hlam, p7770_1]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [hlam, p7770_0]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [h7731, hlam, p7770_1]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [h7719, hlam, p7770_0]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [h7725, hlam, p7770_0]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [h7730, hlam, p7770_1]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [h0, h1, h7719, h7723, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7770_1]
                                    · have p7770_0 := h7770c.1
                                      have p7770_1 := h7770c.2.1
                                      have p7770_2 := h7770c.2.2.1
                                      have p7770_3 := h7770c.2.2.2
                                      linarith only [hlam, p7770_0]
                              · linarith only [h1, h7723, h7730, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                            · linarith only [h0, h1, h7718, h7722, h7723, h7729, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7808 | h7808
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7809 | h7809
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7810 | h7810
                                · linarith only [h0, h1, h7718, h7726, h7728, h7810, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7812 | h7812
                                  · linarith only [h7726, h7728, h7812, hlam]
                                  · rcases h2bigk with h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c
                                    · have p7814_0 := h7814c.1
                                      have p7814_1 := h7814c.2.1
                                      have p7814_2 := h7814c.2.2.1
                                      have p7814_3 := h7814c.2.2.2
                                      linarith only [hlam, p7814_0]
                                    · have p7814_0 := h7814c.1
                                      have p7814_1 := h7814c.2.1
                                      have p7814_2 := h7814c.2.2.1
                                      have p7814_3 := h7814c.2.2.2
                                      linarith only [h0, h1, h7723, hc12, hc23, hlam, hphi, p7814_1]
                                    · have p7814_0 := h7814c.1
                                      have p7814_1 := h7814c.2.1
                                      have p7814_2 := h7814c.2.2.1
                                      have p7814_3 := h7814c.2.2.2
                                      linarith only [h7716, hlam, p7814_0]
                                    · have p7814_0 := h7814c.1
                                      have p7814_1 := h7814c.2.1
                                      have p7814_2 := h7814c.2.2.1
                                      have p7814_3 := h7814c.2.2.2
                                      rcases p7814_3 (m.d 0 2) (by simp) with h7818 | h7818
                                      · rcases p7814_3 (m.d 1 2) (by simp) with h7819 | h7819
                                        · linarith only [h0, h7819, hlam]
                                        · linarith only [h7725, h7810, h7819, hlam]
                                      · linarith only [h7818, hlam, p7814_0]
                                    · have p7814_0 := h7814c.1
                                      have p7814_1 := h7814c.2.1
                                      have p7814_2 := h7814c.2.2.1
                                      have p7814_3 := h7814c.2.2.2
                                      rcases p7814_3 (m.d 0 2) (by simp) with h7823 | h7823
                                      · rcases p7814_3 (m.d 1 2) (by simp) with h7824 | h7824
                                        · linarith only [h0, h7824, hlam]
                                        · linarith only [h7725, h7824, hlam]
                                      · linarith only [h7823, hlam, p7814_0]
                                    · have p7814_0 := h7814c.1
                                      have p7814_1 := h7814c.2.1
                                      have p7814_2 := h7814c.2.2.1
                                      have p7814_3 := h7814c.2.2.2
                                      linarith only [h0, hlam, p7814_0]
                                    · have p7814_0 := h7814c.1
                                      have p7814_1 := h7814c.2.1
                                      have p7814_2 := h7814c.2.2.1
                                      have p7814_3 := h7814c.2.2.2
                                      linarith only [hlam, p7814_0]
                                    · have p7814_0 := h7814c.1
                                      have p7814_1 := h7814c.2.1
                                      have p7814_2 := h7814c.2.2.1
                                      have p7814_3 := h7814c.2.2.2
                                      linarith only [h7723, hlam, p7814_0]
                                    · have p7814_0 := h7814c.1
                                      have p7814_1 := h7814c.2.1
                                      have p7814_2 := h7814c.2.2.1
                                      have p7814_3 := h7814c.2.2.2
                                      linarith only [h0, h1, h7723, h7808, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7814_1]
                                    · have p7814_0 := h7814c.1
                                      have p7814_1 := h7814c.2.1
                                      have p7814_2 := h7814c.2.2.1
                                      have p7814_3 := h7814c.2.2.2
                                      linarith only [h0, h1, h7723, h7808, h7810, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7814_1]
                                    · have p7814_0 := h7814c.1
                                      have p7814_1 := h7814c.2.1
                                      have p7814_2 := h7814c.2.2.1
                                      have p7814_3 := h7814c.2.2.2
                                      linarith only [hc23, hlam, hphi, ht01, ht12, p7814_1, u0ehi1]
                                    · have p7814_0 := h7814c.1
                                      have p7814_1 := h7814c.2.1
                                      have p7814_2 := h7814c.2.2.1
                                      have p7814_3 := h7814c.2.2.2
                                      rcases p7814_3 (m.d 0 2) (by simp) with h7834 | h7834
                                      · linarith only [h7716, h7834, hlam]
                                      · linarith only [h0, h7834, hlam]
                                    · have p7814_0 := h7814c.1
                                      have p7814_1 := h7814c.2.1
                                      have p7814_2 := h7814c.2.2.1
                                      have p7814_3 := h7814c.2.2.2
                                      linarith only [hlam, p7814_0]
                                    · have p7814_0 := h7814c.1
                                      have p7814_1 := h7814c.2.1
                                      have p7814_2 := h7814c.2.2.1
                                      have p7814_3 := h7814c.2.2.2
                                      linarith only [h0, h1, h7723, h7725, h7810, hlam, p7814_2]
                                    · have p7814_0 := h7814c.1
                                      have p7814_1 := h7814c.2.1
                                      have p7814_2 := h7814c.2.2.1
                                      have p7814_3 := h7814c.2.2.2
                                      linarith only [h0, h1, h7723, h7725, hlam, p7814_2]
                                    · have p7814_0 := h7814c.1
                                      have p7814_1 := h7814c.2.1
                                      have p7814_2 := h7814c.2.2.1
                                      have p7814_3 := h7814c.2.2.2
                                      linarith only [h7718, hlam, p7814_0]
                                    · have p7814_0 := h7814c.1
                                      have p7814_1 := h7814c.2.1
                                      have p7814_2 := h7814c.2.2.1
                                      have p7814_3 := h7814c.2.2.2
                                      linarith only [h7718, h7722, h7810, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p7814_1]
                                    · have p7814_0 := h7814c.1
                                      have p7814_1 := h7814c.2.1
                                      have p7814_2 := h7814c.2.2.1
                                      have p7814_3 := h7814c.2.2.2
                                      linarith only [h7808, hlam, p7814_1]
                                    · have p7814_0 := h7814c.1
                                      have p7814_1 := h7814c.2.1
                                      have p7814_2 := h7814c.2.2.1
                                      have p7814_3 := h7814c.2.2.2
                                      linarith only [hlam, p7814_0]
                                    · have p7814_0 := h7814c.1
                                      have p7814_1 := h7814c.2.1
                                      have p7814_2 := h7814c.2.2.1
                                      have p7814_3 := h7814c.2.2.2
                                      linarith only [h7810, hlam, p7814_1]
                                    · have p7814_0 := h7814c.1
                                      have p7814_1 := h7814c.2.1
                                      have p7814_2 := h7814c.2.2.1
                                      have p7814_3 := h7814c.2.2.2
                                      linarith only [h7719, hlam, p7814_0]
                                    · have p7814_0 := h7814c.1
                                      have p7814_1 := h7814c.2.1
                                      have p7814_2 := h7814c.2.2.1
                                      have p7814_3 := h7814c.2.2.2
                                      linarith only [h7725, hlam, p7814_0]
                                    · have p7814_0 := h7814c.1
                                      have p7814_1 := h7814c.2.1
                                      have p7814_2 := h7814c.2.2.1
                                      have p7814_3 := h7814c.2.2.2
                                      linarith only [h7809, hlam, p7814_1]
                                    · have p7814_0 := h7814c.1
                                      have p7814_1 := h7814c.2.1
                                      have p7814_2 := h7814c.2.2.1
                                      have p7814_3 := h7814c.2.2.2
                                      linarith only [h0, h1, h7723, h7725, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7814_1]
                                    · have p7814_0 := h7814c.1
                                      have p7814_1 := h7814c.2.1
                                      have p7814_2 := h7814c.2.2.1
                                      have p7814_3 := h7814c.2.2.2
                                      linarith only [hlam, p7814_0]
                              · linarith only [h0, h1, h7723, h7809, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h1, h7718, h7722, h7723, h7726, h7728, h7808, hlam]
                        · linarith only [h0, h1, h7727, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h0, h1, h7718, h7722, h7726, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi4]
                    · linarith only [h0, h1, h7719, h7723, h7725, hc12, hc23, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7855 | h7855
                  · linarith only [h7716, h7855, hc12, hlam, hphi, ht01, u0ehi1]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7857 | h7857
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7858 | h7858
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7859 | h7859
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7860 | h7860
                          · linarith only [h7722, h7860, hc14, hlam, hphi, ht01, u0ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7862 | h7862
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7863 | h7863
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7864 | h7864
                                · linarith only [h7722, h7864, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7866 | h7866
                                  · linarith only [h0, h7722, h7857, h7862, h7864, h7866, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases h2bigk with h7868c | h7868c | h7868c | h7868c | h7868c | h7868c | h7868c | h7868c | h7868c | h7868c | h7868c | h7868c | h7868c | h7868c | h7868c | h7868c | h7868c | h7868c | h7868c | h7868c | h7868c | h7868c | h7868c | h7868c | h7868c
                                    · have p7868_0 := h7868c.1
                                      have p7868_1 := h7868c.2.1
                                      have p7868_2 := h7868c.2.2.1
                                      have p7868_3 := h7868c.2.2.2
                                      linarith only [hlam, p7868_0]
                                    · have p7868_0 := h7868c.1
                                      have p7868_1 := h7868c.2.1
                                      have p7868_2 := h7868c.2.2.1
                                      have p7868_3 := h7868c.2.2.2
                                      linarith only [h0, h1, h7855, hc12, hc23, hlam, hphi, p7868_1]
                                    · have p7868_0 := h7868c.1
                                      have p7868_1 := h7868c.2.1
                                      have p7868_2 := h7868c.2.2.1
                                      have p7868_3 := h7868c.2.2.2
                                      linarith only [h7716, hlam, p7868_0]
                                    · have p7868_0 := h7868c.1
                                      have p7868_1 := h7868c.2.1
                                      have p7868_2 := h7868c.2.2.1
                                      have p7868_3 := h7868c.2.2.2
                                      rcases p7868_3 (m.d 0 2) (by simp) with h7872 | h7872
                                      · rcases p7868_3 (m.d 1 2) (by simp) with h7873 | h7873
                                        · linarith only [h0, h7873, hlam]
                                        · linarith only [h0, h1, h7855, h7873, hc12, hc23, hlam, hphi, p7868_1]
                                      · linarith only [h7872, hlam, p7868_0]
                                    · have p7868_0 := h7868c.1
                                      have p7868_1 := h7868c.2.1
                                      have p7868_2 := h7868c.2.2.1
                                      have p7868_3 := h7868c.2.2.2
                                      rcases p7868_3 (m.d 0 2) (by simp) with h7877 | h7877
                                      · rcases p7868_3 (m.d 1 2) (by simp) with h7878 | h7878
                                        · linarith only [h0, h7878, hlam]
                                        · linarith only [h7857, h7878, hlam]
                                      · linarith only [h7877, hlam, p7868_0]
                                    · have p7868_0 := h7868c.1
                                      have p7868_1 := h7868c.2.1
                                      have p7868_2 := h7868c.2.2.1
                                      have p7868_3 := h7868c.2.2.2
                                      linarith only [h0, hlam, p7868_0]
                                    · have p7868_0 := h7868c.1
                                      have p7868_1 := h7868c.2.1
                                      have p7868_2 := h7868c.2.2.1
                                      have p7868_3 := h7868c.2.2.2
                                      linarith only [hlam, p7868_0]
                                    · have p7868_0 := h7868c.1
                                      have p7868_1 := h7868c.2.1
                                      have p7868_2 := h7868c.2.2.1
                                      have p7868_3 := h7868c.2.2.2
                                      linarith only [h7855, hlam, p7868_0]
                                    · have p7868_0 := h7868c.1
                                      have p7868_1 := h7868c.2.1
                                      have p7868_2 := h7868c.2.2.1
                                      have p7868_3 := h7868c.2.2.2
                                      linarith only [h0, h1, h7855, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7868_1]
                                    · have p7868_0 := h7868c.1
                                      have p7868_1 := h7868c.2.1
                                      have p7868_2 := h7868c.2.2.1
                                      have p7868_3 := h7868c.2.2.2
                                      linarith only [h0, h1, h7855, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p7868_1]
                                    · have p7868_0 := h7868c.1
                                      have p7868_1 := h7868c.2.1
                                      have p7868_2 := h7868c.2.2.1
                                      have p7868_3 := h7868c.2.2.2
                                      linarith only [hc23, hlam, hphi, ht01, ht12, p7868_1, u0ehi1]
                                    · have p7868_0 := h7868c.1
                                      have p7868_1 := h7868c.2.1
                                      have p7868_2 := h7868c.2.2.1
                                      have p7868_3 := h7868c.2.2.2
                                      rcases p7868_3 (m.d 0 2) (by simp) with h7888 | h7888
                                      · linarith only [h7716, h7888, hlam]
                                      · linarith only [h0, h7888, hlam]
                                    · have p7868_0 := h7868c.1
                                      have p7868_1 := h7868c.2.1
                                      have p7868_2 := h7868c.2.2.1
                                      have p7868_3 := h7868c.2.2.2
                                      linarith only [hlam, p7868_0]
                                    · have p7868_0 := h7868c.1
                                      have p7868_1 := h7868c.2.1
                                      have p7868_2 := h7868c.2.2.1
                                      have p7868_3 := h7868c.2.2.2
                                      linarith only [h0, h1, h7855, h7857, h7864, hlam, p7868_2]
                                    · have p7868_0 := h7868c.1
                                      have p7868_1 := h7868c.2.1
                                      have p7868_2 := h7868c.2.2.1
                                      have p7868_3 := h7868c.2.2.2
                                      linarith only [h0, h1, h7855, h7857, hlam, p7868_2]
                                    · have p7868_0 := h7868c.1
                                      have p7868_1 := h7868c.2.1
                                      have p7868_2 := h7868c.2.2.1
                                      have p7868_3 := h7868c.2.2.2
                                      linarith only [h7718, hlam, p7868_0]
                                    · have p7868_0 := h7868c.1
                                      have p7868_1 := h7868c.2.1
                                      have p7868_2 := h7868c.2.2.1
                                      have p7868_3 := h7868c.2.2.2
                                      linarith only [h7857, h7864, hlam, p7868_1]
                                    · have p7868_0 := h7868c.1
                                      have p7868_1 := h7868c.2.1
                                      have p7868_2 := h7868c.2.2.1
                                      have p7868_3 := h7868c.2.2.2
                                      linarith only [h7862, hlam, p7868_1]
                                    · have p7868_0 := h7868c.1
                                      have p7868_1 := h7868c.2.1
                                      have p7868_2 := h7868c.2.2.1
                                      have p7868_3 := h7868c.2.2.2
                                      linarith only [hlam, p7868_0]
                                    · have p7868_0 := h7868c.1
                                      have p7868_1 := h7868c.2.1
                                      have p7868_2 := h7868c.2.2.1
                                      have p7868_3 := h7868c.2.2.2
                                      linarith only [h7864, hlam, p7868_1]
                                    · have p7868_0 := h7868c.1
                                      have p7868_1 := h7868c.2.1
                                      have p7868_2 := h7868c.2.2.1
                                      have p7868_3 := h7868c.2.2.2
                                      linarith only [h7719, hlam, p7868_0]
                                    · have p7868_0 := h7868c.1
                                      have p7868_1 := h7868c.2.1
                                      have p7868_2 := h7868c.2.2.1
                                      have p7868_3 := h7868c.2.2.2
                                      linarith only [h7857, hlam, p7868_0]
                                    · have p7868_0 := h7868c.1
                                      have p7868_1 := h7868c.2.1
                                      have p7868_2 := h7868c.2.2.1
                                      have p7868_3 := h7868c.2.2.2
                                      linarith only [h7863, hlam, p7868_1]
                                    · have p7868_0 := h7868c.1
                                      have p7868_1 := h7868c.2.1
                                      have p7868_2 := h7868c.2.2.1
                                      have p7868_3 := h7868c.2.2.2
                                      linarith only [h0, h1, h7855, h7857, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7868_1]
                                    · have p7868_0 := h7868c.1
                                      have p7868_1 := h7868c.2.1
                                      have p7868_2 := h7868c.2.2.1
                                      have p7868_3 := h7868c.2.2.2
                                      linarith only [hlam, p7868_0]
                              · linarith only [h0, h1, h7855, h7863, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h1, h7719, h7722, h7855, h7862, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h0, h1, h7719, h7722, h7859, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                      · linarith only [h0, h1, h7719, h7720, h7722, h7858, hc03, hlam, hphi, u0ehi3]
                    · linarith only [h0, h1, h7719, h7855, h7857, hc12, hc23, hlam, hphi]
              · linarith only [h1, h7715, h7721, hlam]
            · linarith only [h0, h1, h7718, h7720, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7911 | h7911
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7912 | h7912
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7913 | h7913
                · linarith only [h7718, h7719, h7913, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7915 | h7915
                  · linarith only [h0, h7716, h7718, h7915, hc01, hlam, hphi, u0ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7917 | h7917
                    · linarith only [h0, h1, h7718, h7719, h7915, h7917, hc23, hlam, hphi, ht01, ht12, u0ehi3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7919 | h7919
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7920 | h7920
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7921 | h7921
                          · linarith only [h7913, h7921, hc14, hlam, hphi, ht01, u0ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7923 | h7923
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7924 | h7924
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7925 | h7925
                                · linarith only [h7718, h7913, h7925, hc02, hlam, hphi, u0ehi3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7927 | h7927
                                  · linarith only [h7718, h7719, h7923, h7925, h7927, hlam]
                                  · rcases h2bigk with h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c | h7929c
                                    · have p7929_0 := h7929c.1
                                      have p7929_1 := h7929c.2.1
                                      have p7929_2 := h7929c.2.2.1
                                      have p7929_3 := h7929c.2.2.2
                                      linarith only [hlam, p7929_0]
                                    · have p7929_0 := h7929c.1
                                      have p7929_1 := h7929c.2.1
                                      have p7929_2 := h7929c.2.2.1
                                      have p7929_3 := h7929c.2.2.2
                                      linarith only [h1, h7715, h7719, h7915, hc12, hc23, hlam, hphi, p7929_1]
                                    · have p7929_0 := h7929c.1
                                      have p7929_1 := h7929c.2.1
                                      have p7929_2 := h7929c.2.2.1
                                      have p7929_3 := h7929c.2.2.2
                                      linarith only [h7716, hlam, p7929_0]
                                    · have p7929_0 := h7929c.1
                                      have p7929_1 := h7929c.2.1
                                      have p7929_2 := h7929c.2.2.1
                                      have p7929_3 := h7929c.2.2.2
                                      linarith only [h7719, h7923, h7925, hc34, hc45, hlam, hphi, p7929_1]
                                    · have p7929_0 := h7929c.1
                                      have p7929_1 := h7929c.2.1
                                      have p7929_2 := h7929c.2.2.1
                                      have p7929_3 := h7929c.2.2.2
                                      linarith only [h7719, hlam, p7929_0]
                                    · have p7929_0 := h7929c.1
                                      have p7929_1 := h7929c.2.1
                                      have p7929_2 := h7929c.2.2.1
                                      have p7929_3 := h7929c.2.2.2
                                      linarith only [h0, hlam, p7929_0]
                                    · have p7929_0 := h7929c.1
                                      have p7929_1 := h7929c.2.1
                                      have p7929_2 := h7929c.2.2.1
                                      have p7929_3 := h7929c.2.2.2
                                      linarith only [hlam, p7929_0]
                                    · have p7929_0 := h7929c.1
                                      have p7929_1 := h7929c.2.1
                                      have p7929_2 := h7929c.2.2.1
                                      have p7929_3 := h7929c.2.2.2
                                      linarith only [h7915, hlam, p7929_0]
                                    · have p7929_0 := h7929c.1
                                      have p7929_1 := h7929c.2.1
                                      have p7929_2 := h7929c.2.2.1
                                      have p7929_3 := h7929c.2.2.2
                                      linarith only [h0, h1, h7915, h7923, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7929_1]
                                    · have p7929_0 := h7929c.1
                                      have p7929_1 := h7929c.2.1
                                      have p7929_2 := h7929c.2.2.1
                                      have p7929_3 := h7929c.2.2.2
                                      linarith only [h7917, hlam, p7929_0]
                                    · have p7929_0 := h7929c.1
                                      have p7929_1 := h7929c.2.1
                                      have p7929_2 := h7929c.2.2.1
                                      have p7929_3 := h7929c.2.2.2
                                      linarith only [hc23, hlam, hphi, ht01, ht12, p7929_1, u0ehi1]
                                    · have p7929_0 := h7929c.1
                                      have p7929_1 := h7929c.2.1
                                      have p7929_2 := h7929c.2.2.1
                                      have p7929_3 := h7929c.2.2.2
                                      rcases p7929_3 (m.d 0 2) (by simp) with h7941 | h7941
                                      · linarith only [h7716, h7941, hlam]
                                      · linarith only [h0, h7941, hlam]
                                    · have p7929_0 := h7929c.1
                                      have p7929_1 := h7929c.2.1
                                      have p7929_2 := h7929c.2.2.1
                                      have p7929_3 := h7929c.2.2.2
                                      linarith only [hlam, p7929_0]
                                    · have p7929_0 := h7929c.1
                                      have p7929_1 := h7929c.2.1
                                      have p7929_2 := h7929c.2.2.1
                                      have p7929_3 := h7929c.2.2.2
                                      rcases p7929_3 (m.d 0 2) (by simp) with h7945 | h7945
                                      · linarith only [h7716, h7945, hlam]
                                      · linarith only [h7718, h7945, hlam]
                                    · have p7929_0 := h7929c.1
                                      have p7929_1 := h7929c.2.1
                                      have p7929_2 := h7929c.2.2.1
                                      have p7929_3 := h7929c.2.2.2
                                      linarith only [h7718, h7719, hc23, hlam, hphi, ht01, ht12, p7929_1, u0ehi3]
                                    · have p7929_0 := h7929c.1
                                      have p7929_1 := h7929c.2.1
                                      have p7929_2 := h7929c.2.2.1
                                      have p7929_3 := h7929c.2.2.2
                                      linarith only [h7718, hlam, p7929_0]
                                    · have p7929_0 := h7929c.1
                                      have p7929_1 := h7929c.2.1
                                      have p7929_2 := h7929c.2.2.1
                                      have p7929_3 := h7929c.2.2.2
                                      linarith only [h7718, h7719, h7925, hc12, hc45, hlam, hphi, ht23, ht34, p7929_1]
                                    · have p7929_0 := h7929c.1
                                      have p7929_1 := h7929c.2.1
                                      have p7929_2 := h7929c.2.2.1
                                      have p7929_3 := h7929c.2.2.2
                                      linarith only [h7923, hlam, p7929_1]
                                    · have p7929_0 := h7929c.1
                                      have p7929_1 := h7929c.2.1
                                      have p7929_2 := h7929c.2.2.1
                                      have p7929_3 := h7929c.2.2.2
                                      linarith only [hlam, p7929_0]
                                    · have p7929_0 := h7929c.1
                                      have p7929_1 := h7929c.2.1
                                      have p7929_2 := h7929c.2.2.1
                                      have p7929_3 := h7929c.2.2.2
                                      linarith only [h7925, hlam, p7929_1]
                                    · have p7929_0 := h7929c.1
                                      have p7929_1 := h7929c.2.1
                                      have p7929_2 := h7929c.2.2.1
                                      have p7929_3 := h7929c.2.2.2
                                      linarith only [h7718, h7925, hc24, hc45, hlam, hphi, p7929_1]
                                    · have p7929_0 := h7929c.1
                                      have p7929_1 := h7929c.2.1
                                      have p7929_2 := h7929c.2.2.1
                                      have p7929_3 := h7929c.2.2.2
                                      rcases p7929_3 (m.d 0 2) (by simp) with h7955 | h7955
                                      · linarith only [h7719, h7955, hlam]
                                      · linarith only [h0, h7955, hlam]
                                    · have p7929_0 := h7929c.1
                                      have p7929_1 := h7929c.2.1
                                      have p7929_2 := h7929c.2.2.1
                                      have p7929_3 := h7929c.2.2.2
                                      linarith only [h7924, hlam, p7929_1]
                                    · have p7929_0 := h7929c.1
                                      have p7929_1 := h7929c.2.1
                                      have p7929_2 := h7929c.2.2.1
                                      have p7929_3 := h7929c.2.2.2
                                      rcases p7929_3 (m.d 0 2) (by simp) with h7959 | h7959
                                      · linarith only [h7719, h7959, hlam]
                                      · linarith only [h7718, h7959, hlam]
                                    · have p7929_0 := h7929c.1
                                      have p7929_1 := h7929c.2.1
                                      have p7929_2 := h7929c.2.2.1
                                      have p7929_3 := h7929c.2.2.2
                                      linarith only [hlam, p7929_0]
                              · linarith only [h1, h7715, h7915, h7920, h7924, hlam]
                            · linarith only [h1, h7915, h7923, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                        · linarith only [h1, h7715, h7718, h7719, h7920, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                      · linarith only [h1, h7715, h7718, h7719, h7911, h7919, hlam]
              · linarith only [h1, h7715, h7912, hlam]
            · linarith only [h1, h7715, h7718, h7719, h7911, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h7969 | h7969
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7970 | h7970
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7971 | h7971
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7972 | h7972
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7973 | h7973
                  · linarith only [h0, h7716, h7969, h7973, hc01, hlam, hphi, u0ehi4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7975 | h7975
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7976 | h7976
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h7977 | h7977
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h7978 | h7978
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h7979 | h7979
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h7980 | h7980
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h7981 | h7981
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h7982 | h7982
                                  · rcases h2bigk with h7983c | h7983c | h7983c | h7983c | h7983c | h7983c | h7983c | h7983c | h7983c | h7983c | h7983c | h7983c | h7983c | h7983c | h7983c | h7983c | h7983c | h7983c | h7983c | h7983c | h7983c | h7983c | h7983c | h7983c | h7983c
                                    · have p7983_0 := h7983c.1
                                      have p7983_1 := h7983c.2.1
                                      have p7983_2 := h7983c.2.2.1
                                      have p7983_3 := h7983c.2.2.2
                                      linarith only [hlam, p7983_0]
                                    · have p7983_0 := h7983c.1
                                      have p7983_1 := h7983c.2.1
                                      have p7983_2 := h7983c.2.2.1
                                      have p7983_3 := h7983c.2.2.2
                                      linarith only [h7718, hc12, hc24, hlam, hphi, p7983_1]
                                    · have p7983_0 := h7983c.1
                                      have p7983_1 := h7983c.2.1
                                      have p7983_2 := h7983c.2.2.1
                                      have p7983_3 := h7983c.2.2.2
                                      linarith only [h7716, hlam, p7983_0]
                                    · have p7983_0 := h7983c.1
                                      have p7983_1 := h7983c.2.1
                                      have p7983_2 := h7983c.2.2.1
                                      have p7983_3 := h7983c.2.2.2
                                      linarith only [h7718, hlam, p7983_0]
                                    · have p7983_0 := h7983c.1
                                      have p7983_1 := h7983c.2.1
                                      have p7983_2 := h7983c.2.2.1
                                      have p7983_3 := h7983c.2.2.2
                                      rcases p7983_3 (m.d 0 2) (by simp) with h7988 | h7988
                                      · rcases p7983_3 (m.d 1 2) (by simp) with h7989 | h7989
                                        · linarith only [h0, h7989, hlam]
                                        · linarith only [h7975, h7989, hlam]
                                      · linarith only [h7988, hlam, p7983_0]
                                    · have p7983_0 := h7983c.1
                                      have p7983_1 := h7983c.2.1
                                      have p7983_2 := h7983c.2.2.1
                                      have p7983_3 := h7983c.2.2.2
                                      linarith only [h0, hlam, p7983_0]
                                    · have p7983_0 := h7983c.1
                                      have p7983_1 := h7983c.2.1
                                      have p7983_2 := h7983c.2.2.1
                                      have p7983_3 := h7983c.2.2.2
                                      linarith only [hlam, p7983_0]
                                    · have p7983_0 := h7983c.1
                                      have p7983_1 := h7983c.2.1
                                      have p7983_2 := h7983c.2.2.1
                                      have p7983_3 := h7983c.2.2.2
                                      linarith only [h7973, hlam, p7983_0]
                                    · have p7983_0 := h7983c.1
                                      have p7983_1 := h7983c.2.1
                                      have p7983_2 := h7983c.2.2.1
                                      have p7983_3 := h7983c.2.2.2
                                      linarith only [h0, h1, h7973, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7983_1]
                                    · have p7983_0 := h7983c.1
                                      have p7983_1 := h7983c.2.1
                                      have p7983_2 := h7983c.2.2.1
                                      have p7983_3 := h7983c.2.2.2
                                      linarith only [h0, h1, h7973, h7980, h7982, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7983_1]
                                    · have p7983_0 := h7983c.1
                                      have p7983_1 := h7983c.2.1
                                      have p7983_2 := h7983c.2.2.1
                                      have p7983_3 := h7983c.2.2.2
                                      linarith only [hc23, hlam, hphi, ht01, ht12, p7983_1, u0ehi1]
                                    · have p7983_0 := h7983c.1
                                      have p7983_1 := h7983c.2.1
                                      have p7983_2 := h7983c.2.2.1
                                      have p7983_3 := h7983c.2.2.2
                                      rcases p7983_3 (m.d 0 2) (by simp) with h7999 | h7999
                                      · linarith only [h7716, h7999, hlam]
                                      · linarith only [h0, h7999, hlam]
                                    · have p7983_0 := h7983c.1
                                      have p7983_1 := h7983c.2.1
                                      have p7983_2 := h7983c.2.2.1
                                      have p7983_3 := h7983c.2.2.2
                                      linarith only [hlam, p7983_0]
                                    · have p7983_0 := h7983c.1
                                      have p7983_1 := h7983c.2.1
                                      have p7983_2 := h7983c.2.2.1
                                      have p7983_3 := h7983c.2.2.2
                                      linarith only [h7718, h7969, hc23, hlam, hphi, ht01, ht12, p7983_1, u0ehi4]
                                    · have p7983_0 := h7983c.1
                                      have p7983_1 := h7983c.2.1
                                      have p7983_2 := h7983c.2.2.1
                                      have p7983_3 := h7983c.2.2.2
                                      linarith only [h0, h1, h7973, h7975, hlam, p7983_2]
                                    · have p7983_0 := h7983c.1
                                      have p7983_1 := h7983c.2.1
                                      have p7983_2 := h7983c.2.2.1
                                      have p7983_3 := h7983c.2.2.2
                                      linarith only [h7969, hc24, hlam, hphi, ht01, ht12, p7983_1, u0ehi4]
                                    · have p7983_0 := h7983c.1
                                      have p7983_1 := h7983c.2.1
                                      have p7983_2 := h7983c.2.2.1
                                      have p7983_3 := h7983c.2.2.2
                                      rcases p7983_3 (m.d 0 2) (by simp) with h8006 | h8006
                                      · linarith only [h7718, h8006, hlam]
                                      · linarith only [h0, h8006, hlam]
                                    · have p7983_0 := h7983c.1
                                      have p7983_1 := h7983c.2.1
                                      have p7983_2 := h7983c.2.2.1
                                      have p7983_3 := h7983c.2.2.2
                                      linarith only [h7979, hlam, p7983_1]
                                    · have p7983_0 := h7983c.1
                                      have p7983_1 := h7983c.2.1
                                      have p7983_2 := h7983c.2.2.1
                                      have p7983_3 := h7983c.2.2.2
                                      linarith only [hlam, p7983_0]
                                    · have p7983_0 := h7983c.1
                                      have p7983_1 := h7983c.2.1
                                      have p7983_2 := h7983c.2.2.1
                                      have p7983_3 := h7983c.2.2.2
                                      rcases p7983_3 (m.d 0 2) (by simp) with h8011 | h8011
                                      · linarith only [h7718, h8011, hlam]
                                      · linarith only [h7969, h8011, hlam]
                                    · have p7983_0 := h7983c.1
                                      have p7983_1 := h7983c.2.1
                                      have p7983_2 := h7983c.2.2.1
                                      have p7983_3 := h7983c.2.2.2
                                      linarith only [h7969, hlam, p7983_0]
                                    · have p7983_0 := h7983c.1
                                      have p7983_1 := h7983c.2.1
                                      have p7983_2 := h7983c.2.2.1
                                      have p7983_3 := h7983c.2.2.2
                                      linarith only [h7975, hlam, p7983_0]
                                    · have p7983_0 := h7983c.1
                                      have p7983_1 := h7983c.2.1
                                      have p7983_2 := h7983c.2.2.1
                                      have p7983_3 := h7983c.2.2.2
                                      linarith only [h7980, hlam, p7983_1]
                                    · have p7983_0 := h7983c.1
                                      have p7983_1 := h7983c.2.1
                                      have p7983_2 := h7983c.2.2.1
                                      have p7983_3 := h7983c.2.2.2
                                      linarith only [h7981, hlam, p7983_0]
                                    · have p7983_0 := h7983c.1
                                      have p7983_1 := h7983c.2.1
                                      have p7983_2 := h7983c.2.2.1
                                      have p7983_3 := h7983c.2.2.2
                                      linarith only [hlam, p7983_0]
                                  · linarith only [h0, h1, h7973, h7975, h7981, h7982, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h7718, h7969, h7978, h7981, hc14, hlam, hphi, ht01, u0ehi4]
                              · linarith only [h0, h1, h7973, h7980, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h1, h7969, h7973, h7979, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8023 | h8023
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8024 | h8024
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8025 | h8025
                                · linarith only [h0, h1, h7975, h7978, h8025, hc13, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h7718, h8025, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                              · linarith only [h0, h1, h7973, h8024, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h1, h7969, h7973, h7976, h8023, hc14, hlam, hphi, ht01, u0ehi4]
                        · linarith only [h0, h1, h7969, h7977, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi4]
                      · linarith only [h0, h1, h7969, h7970, h7976, hc03, hlam, hphi, u0ehi4]
                    · linarith only [h7718, h7969, h7975, hc12, hc24, hlam, hphi]
                · linarith only [h7718, h7969, h7972, hlam]
              · linarith only [h0, h1, h7969, h7971, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h8035 | h8035
              · rcases m.htr 0 4 5 (by decide) (by decide) with h8036 | h8036
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8037 | h8037
                  · linarith only [h0, h1, h7970, h8037, hc23, hc34, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8039 | h8039
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8040 | h8040
                      · linarith only [h0, h1, h7970, h8037, h8040, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h7969, h8040, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi4]
                    · linarith only [h7716, h7969, h8039, hc12, hc23, hlam, hphi]
                · linarith only [h0, h1, h7969, h7970, h8036, hlam]
              · linarith only [h0, h1, h7969, h8035, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h8046 | h8046
            · rcases m.htr 0 3 5 (by decide) (by decide) with h8047 | h8047
              · rcases m.htr 0 4 5 (by decide) (by decide) with h8048 | h8048
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8049 | h8049
                  · linarith only [h7716, h8049, hc12, hlam, hphi, ht01, u0ehi1]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8051 | h8051
                    · linarith only [h0, h7969, h8051, hc01, hlam, hphi, u0ehi1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8053 | h8053
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8054 | h8054
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8055 | h8055
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8056 | h8056
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8057 | h8057
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8058 | h8058
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8059 | h8059
                                  · rcases h2bigk with h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c | h8060c
                                    · have p8060_0 := h8060c.1
                                      have p8060_1 := h8060c.2.1
                                      have p8060_2 := h8060c.2.2.1
                                      have p8060_3 := h8060c.2.2.2
                                      linarith only [hlam, p8060_0]
                                    · have p8060_0 := h8060c.1
                                      have p8060_1 := h8060c.2.1
                                      have p8060_2 := h8060c.2.2.1
                                      have p8060_3 := h8060c.2.2.2
                                      linarith only [h7969, hc12, hc25, hlam, hphi, p8060_1]
                                    · have p8060_0 := h8060c.1
                                      have p8060_1 := h8060c.2.1
                                      have p8060_2 := h8060c.2.2.1
                                      have p8060_3 := h8060c.2.2.2
                                      linarith only [h7716, hlam, p8060_0]
                                    · have p8060_0 := h8060c.1
                                      have p8060_1 := h8060c.2.1
                                      have p8060_2 := h8060c.2.2.1
                                      have p8060_3 := h8060c.2.2.2
                                      linarith only [h7718, hlam, p8060_0]
                                    · have p8060_0 := h8060c.1
                                      have p8060_1 := h8060c.2.1
                                      have p8060_2 := h8060c.2.2.1
                                      have p8060_3 := h8060c.2.2.2
                                      linarith only [h7969, hlam, p8060_0]
                                    · have p8060_0 := h8060c.1
                                      have p8060_1 := h8060c.2.1
                                      have p8060_2 := h8060c.2.2.1
                                      have p8060_3 := h8060c.2.2.2
                                      linarith only [h0, hlam, p8060_0]
                                    · have p8060_0 := h8060c.1
                                      have p8060_1 := h8060c.2.1
                                      have p8060_2 := h8060c.2.2.1
                                      have p8060_3 := h8060c.2.2.2
                                      linarith only [hlam, p8060_0]
                                    · have p8060_0 := h8060c.1
                                      have p8060_1 := h8060c.2.1
                                      have p8060_2 := h8060c.2.2.1
                                      have p8060_3 := h8060c.2.2.2
                                      linarith only [h8049, hlam, p8060_0]
                                    · have p8060_0 := h8060c.1
                                      have p8060_1 := h8060c.2.1
                                      have p8060_2 := h8060c.2.2.1
                                      have p8060_3 := h8060c.2.2.2
                                      linarith only [h0, h1, h8049, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8060_1]
                                    · have p8060_0 := h8060c.1
                                      have p8060_1 := h8060c.2.1
                                      have p8060_2 := h8060c.2.2.1
                                      have p8060_3 := h8060c.2.2.2
                                      linarith only [h8051, hlam, p8060_0]
                                    · have p8060_0 := h8060c.1
                                      have p8060_1 := h8060c.2.1
                                      have p8060_2 := h8060c.2.2.1
                                      have p8060_3 := h8060c.2.2.2
                                      linarith only [hc23, hlam, hphi, ht01, ht12, p8060_1, u0ehi1]
                                    · have p8060_0 := h8060c.1
                                      have p8060_1 := h8060c.2.1
                                      have p8060_2 := h8060c.2.2.1
                                      have p8060_3 := h8060c.2.2.2
                                      rcases p8060_3 (m.d 0 2) (by simp) with h8072 | h8072
                                      · linarith only [h7716, h8072, hlam]
                                      · linarith only [h0, h8072, hlam]
                                    · have p8060_0 := h8060c.1
                                      have p8060_1 := h8060c.2.1
                                      have p8060_2 := h8060c.2.2.1
                                      have p8060_3 := h8060c.2.2.2
                                      linarith only [hlam, p8060_0]
                                    · have p8060_0 := h8060c.1
                                      have p8060_1 := h8060c.2.1
                                      have p8060_2 := h8060c.2.2.1
                                      have p8060_3 := h8060c.2.2.2
                                      linarith only [h7718, hc23, hlam, hphi, ht01, ht12, p8060_1, u0ehi3]
                                    · have p8060_0 := h8060c.1
                                      have p8060_1 := h8060c.2.1
                                      have p8060_2 := h8060c.2.2.1
                                      have p8060_3 := h8060c.2.2.2
                                      linarith only [h7969, hc23, hlam, hphi, ht01, ht12, p8060_1, u0ehi1]
                                    · have p8060_0 := h8060c.1
                                      have p8060_1 := h8060c.2.1
                                      have p8060_2 := h8060c.2.2.1
                                      have p8060_3 := h8060c.2.2.2
                                      linarith only [hc24, hlam, hphi, ht01, ht12, p8060_1, u0ehi1]
                                    · have p8060_0 := h8060c.1
                                      have p8060_1 := h8060c.2.1
                                      have p8060_2 := h8060c.2.2.1
                                      have p8060_3 := h8060c.2.2.2
                                      rcases p8060_3 (m.d 0 2) (by simp) with h8079 | h8079
                                      · linarith only [h7718, h8079, hlam]
                                      · linarith only [h0, h8079, hlam]
                                    · have p8060_0 := h8060c.1
                                      have p8060_1 := h8060c.2.1
                                      have p8060_2 := h8060c.2.2.1
                                      have p8060_3 := h8060c.2.2.2
                                      linarith only [h8056, hlam, p8060_1]
                                    · have p8060_0 := h8060c.1
                                      have p8060_1 := h8060c.2.1
                                      have p8060_2 := h8060c.2.2.1
                                      have p8060_3 := h8060c.2.2.2
                                      linarith only [hlam, p8060_0]
                                    · have p8060_0 := h8060c.1
                                      have p8060_1 := h8060c.2.1
                                      have p8060_2 := h8060c.2.2.1
                                      have p8060_3 := h8060c.2.2.2
                                      linarith only [h7969, h8056, hc23, hlam, hphi, ht01, ht12, p8060_1, u0ehi1]
                                    · have p8060_0 := h8060c.1
                                      have p8060_1 := h8060c.2.1
                                      have p8060_2 := h8060c.2.2.1
                                      have p8060_3 := h8060c.2.2.2
                                      linarith only [hc25, hlam, hphi, ht01, ht12, p8060_1, u0ehi1]
                                    · have p8060_0 := h8060c.1
                                      have p8060_1 := h8060c.2.1
                                      have p8060_2 := h8060c.2.2.1
                                      have p8060_3 := h8060c.2.2.2
                                      rcases p8060_3 (m.d 0 2) (by simp) with h8086 | h8086
                                      · linarith only [h7969, h8086, hlam]
                                      · linarith only [h0, h8086, hlam]
                                    · have p8060_0 := h8060c.1
                                      have p8060_1 := h8060c.2.1
                                      have p8060_2 := h8060c.2.2.1
                                      have p8060_3 := h8060c.2.2.2
                                      linarith only [h8057, hlam, p8060_1]
                                    · have p8060_0 := h8060c.1
                                      have p8060_1 := h8060c.2.1
                                      have p8060_2 := h8060c.2.2.1
                                      have p8060_3 := h8060c.2.2.2
                                      linarith only [h8058, hlam, p8060_0]
                                    · have p8060_0 := h8060c.1
                                      have p8060_1 := h8060c.2.1
                                      have p8060_2 := h8060c.2.2.1
                                      have p8060_3 := h8060c.2.2.2
                                      linarith only [hlam, p8060_0]
                                  · rcases h2bigk with h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c | h8092c
                                    · have p8092_0 := h8092c.1
                                      have p8092_1 := h8092c.2.1
                                      have p8092_2 := h8092c.2.2.1
                                      have p8092_3 := h8092c.2.2.2
                                      linarith only [hlam, p8092_0]
                                    · have p8092_0 := h8092c.1
                                      have p8092_1 := h8092c.2.1
                                      have p8092_2 := h8092c.2.2.1
                                      have p8092_3 := h8092c.2.2.2
                                      linarith only [h0, h1, h8049, hc12, hc23, hlam, hphi, p8092_1]
                                    · have p8092_0 := h8092c.1
                                      have p8092_1 := h8092c.2.1
                                      have p8092_2 := h8092c.2.2.1
                                      have p8092_3 := h8092c.2.2.2
                                      linarith only [h7716, hlam, p8092_0]
                                    · have p8092_0 := h8092c.1
                                      have p8092_1 := h8092c.2.1
                                      have p8092_2 := h8092c.2.2.1
                                      have p8092_3 := h8092c.2.2.2
                                      linarith only [h7718, hlam, p8092_0]
                                    · have p8092_0 := h8092c.1
                                      have p8092_1 := h8092c.2.1
                                      have p8092_2 := h8092c.2.2.1
                                      have p8092_3 := h8092c.2.2.2
                                      linarith only [h7969, hlam, p8092_0]
                                    · have p8092_0 := h8092c.1
                                      have p8092_1 := h8092c.2.1
                                      have p8092_2 := h8092c.2.2.1
                                      have p8092_3 := h8092c.2.2.2
                                      linarith only [h0, hlam, p8092_0]
                                    · have p8092_0 := h8092c.1
                                      have p8092_1 := h8092c.2.1
                                      have p8092_2 := h8092c.2.2.1
                                      have p8092_3 := h8092c.2.2.2
                                      linarith only [hlam, p8092_0]
                                    · have p8092_0 := h8092c.1
                                      have p8092_1 := h8092c.2.1
                                      have p8092_2 := h8092c.2.2.1
                                      have p8092_3 := h8092c.2.2.2
                                      linarith only [h8049, hlam, p8092_0]
                                    · have p8092_0 := h8092c.1
                                      have p8092_1 := h8092c.2.1
                                      have p8092_2 := h8092c.2.2.1
                                      have p8092_3 := h8092c.2.2.2
                                      linarith only [h0, h1, h8049, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8092_1]
                                    · have p8092_0 := h8092c.1
                                      have p8092_1 := h8092c.2.1
                                      have p8092_2 := h8092c.2.2.1
                                      have p8092_3 := h8092c.2.2.2
                                      linarith only [h8051, hlam, p8092_0]
                                    · have p8092_0 := h8092c.1
                                      have p8092_1 := h8092c.2.1
                                      have p8092_2 := h8092c.2.2.1
                                      have p8092_3 := h8092c.2.2.2
                                      linarith only [hc23, hlam, hphi, ht01, ht12, p8092_1, u0ehi1]
                                    · have p8092_0 := h8092c.1
                                      have p8092_1 := h8092c.2.1
                                      have p8092_2 := h8092c.2.2.1
                                      have p8092_3 := h8092c.2.2.2
                                      rcases p8092_3 (m.d 0 2) (by simp) with h8104 | h8104
                                      · linarith only [h7716, h8104, hlam]
                                      · linarith only [h0, h8104, hlam]
                                    · have p8092_0 := h8092c.1
                                      have p8092_1 := h8092c.2.1
                                      have p8092_2 := h8092c.2.2.1
                                      have p8092_3 := h8092c.2.2.2
                                      linarith only [hlam, p8092_0]
                                    · have p8092_0 := h8092c.1
                                      have p8092_1 := h8092c.2.1
                                      have p8092_2 := h8092c.2.2.1
                                      have p8092_3 := h8092c.2.2.2
                                      linarith only [h7969, h8058, hc23, hlam, hphi, ht01, ht12, p8092_1, u0ehi1]
                                    · have p8092_0 := h8092c.1
                                      have p8092_1 := h8092c.2.1
                                      have p8092_2 := h8092c.2.2.1
                                      have p8092_3 := h8092c.2.2.2
                                      linarith only [h7969, hc23, hlam, hphi, ht01, ht12, p8092_1, u0ehi1]
                                    · have p8092_0 := h8092c.1
                                      have p8092_1 := h8092c.2.1
                                      have p8092_2 := h8092c.2.2.1
                                      have p8092_3 := h8092c.2.2.2
                                      linarith only [hc24, hlam, hphi, ht01, ht12, p8092_1, u0ehi1]
                                    · have p8092_0 := h8092c.1
                                      have p8092_1 := h8092c.2.1
                                      have p8092_2 := h8092c.2.2.1
                                      have p8092_3 := h8092c.2.2.2
                                      rcases p8092_3 (m.d 0 2) (by simp) with h8111 | h8111
                                      · linarith only [h7718, h8111, hlam]
                                      · linarith only [h0, h8111, hlam]
                                    · have p8092_0 := h8092c.1
                                      have p8092_1 := h8092c.2.1
                                      have p8092_2 := h8092c.2.2.1
                                      have p8092_3 := h8092c.2.2.2
                                      linarith only [h8056, hlam, p8092_1]
                                    · have p8092_0 := h8092c.1
                                      have p8092_1 := h8092c.2.1
                                      have p8092_2 := h8092c.2.2.1
                                      have p8092_3 := h8092c.2.2.2
                                      linarith only [hlam, p8092_0]
                                    · have p8092_0 := h8092c.1
                                      have p8092_1 := h8092c.2.1
                                      have p8092_2 := h8092c.2.2.1
                                      have p8092_3 := h8092c.2.2.2
                                      linarith only [h7969, h8056, hc23, hlam, hphi, ht01, ht12, p8092_1, u0ehi1]
                                    · have p8092_0 := h8092c.1
                                      have p8092_1 := h8092c.2.1
                                      have p8092_2 := h8092c.2.2.1
                                      have p8092_3 := h8092c.2.2.2
                                      linarith only [hc25, hlam, hphi, ht01, ht12, p8092_1, u0ehi1]
                                    · have p8092_0 := h8092c.1
                                      have p8092_1 := h8092c.2.1
                                      have p8092_2 := h8092c.2.2.1
                                      have p8092_3 := h8092c.2.2.2
                                      rcases p8092_3 (m.d 0 2) (by simp) with h8118 | h8118
                                      · linarith only [h7969, h8118, hlam]
                                      · linarith only [h0, h8118, hlam]
                                    · have p8092_0 := h8092c.1
                                      have p8092_1 := h8092c.2.1
                                      have p8092_2 := h8092c.2.2.1
                                      have p8092_3 := h8092c.2.2.2
                                      linarith only [h8057, hlam, p8092_1]
                                    · have p8092_0 := h8092c.1
                                      have p8092_1 := h8092c.2.1
                                      have p8092_2 := h8092c.2.2.1
                                      have p8092_3 := h8092c.2.2.2
                                      linarith only [h8058, hlam, p8092_0]
                                    · have p8092_0 := h8092c.1
                                      have p8092_1 := h8092c.2.1
                                      have p8092_2 := h8092c.2.2.1
                                      have p8092_3 := h8092c.2.2.2
                                      linarith only [hlam, p8092_0]
                                · linarith only [h7718, h8055, h8058, hc14, hlam, hphi, ht01, u0ehi1]
                              · linarith only [h1, h7715, h8049, h8051, h8057, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h1, h7715, h8049, h8051, h8056, hc12, hc34, hlam, hphi, ht23]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8127 | h8127
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8128 | h8128
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8129 | h8129
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8130 | h8130
                                  · linarith only [h8053, h8055, h8130, hlam]
                                  · rcases h2bigk with h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c | h8132c
                                    · have p8132_0 := h8132c.1
                                      have p8132_1 := h8132c.2.1
                                      have p8132_2 := h8132c.2.2.1
                                      have p8132_3 := h8132c.2.2.2
                                      linarith only [hlam, p8132_0]
                                    · have p8132_0 := h8132c.1
                                      have p8132_1 := h8132c.2.1
                                      have p8132_2 := h8132c.2.2.1
                                      have p8132_3 := h8132c.2.2.2
                                      linarith only [h1, h7715, h7969, h8049, hc12, hc23, hlam, hphi, p8132_1]
                                    · have p8132_0 := h8132c.1
                                      have p8132_1 := h8132c.2.1
                                      have p8132_2 := h8132c.2.2.1
                                      have p8132_3 := h8132c.2.2.2
                                      linarith only [h7716, hlam, p8132_0]
                                    · have p8132_0 := h8132c.1
                                      have p8132_1 := h8132c.2.1
                                      have p8132_2 := h8132c.2.2.1
                                      have p8132_3 := h8132c.2.2.2
                                      linarith only [h7718, hlam, p8132_0]
                                    · have p8132_0 := h8132c.1
                                      have p8132_1 := h8132c.2.1
                                      have p8132_2 := h8132c.2.2.1
                                      have p8132_3 := h8132c.2.2.2
                                      linarith only [h7969, hlam, p8132_0]
                                    · have p8132_0 := h8132c.1
                                      have p8132_1 := h8132c.2.1
                                      have p8132_2 := h8132c.2.2.1
                                      have p8132_3 := h8132c.2.2.2
                                      linarith only [h0, hlam, p8132_0]
                                    · have p8132_0 := h8132c.1
                                      have p8132_1 := h8132c.2.1
                                      have p8132_2 := h8132c.2.2.1
                                      have p8132_3 := h8132c.2.2.2
                                      linarith only [hlam, p8132_0]
                                    · have p8132_0 := h8132c.1
                                      have p8132_1 := h8132c.2.1
                                      have p8132_2 := h8132c.2.2.1
                                      have p8132_3 := h8132c.2.2.2
                                      linarith only [h8049, hlam, p8132_0]
                                    · have p8132_0 := h8132c.1
                                      have p8132_1 := h8132c.2.1
                                      have p8132_2 := h8132c.2.2.1
                                      have p8132_3 := h8132c.2.2.2
                                      linarith only [h0, h1, h8049, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8132_1]
                                    · have p8132_0 := h8132c.1
                                      have p8132_1 := h8132c.2.1
                                      have p8132_2 := h8132c.2.2.1
                                      have p8132_3 := h8132c.2.2.2
                                      linarith only [h8051, hlam, p8132_0]
                                    · have p8132_0 := h8132c.1
                                      have p8132_1 := h8132c.2.1
                                      have p8132_2 := h8132c.2.2.1
                                      have p8132_3 := h8132c.2.2.2
                                      linarith only [hc23, hlam, hphi, ht01, ht12, p8132_1, u0ehi1]
                                    · have p8132_0 := h8132c.1
                                      have p8132_1 := h8132c.2.1
                                      have p8132_2 := h8132c.2.2.1
                                      have p8132_3 := h8132c.2.2.2
                                      rcases p8132_3 (m.d 0 2) (by simp) with h8144 | h8144
                                      · linarith only [h7716, h8144, hlam]
                                      · linarith only [h0, h8144, hlam]
                                    · have p8132_0 := h8132c.1
                                      have p8132_1 := h8132c.2.1
                                      have p8132_2 := h8132c.2.2.1
                                      have p8132_3 := h8132c.2.2.2
                                      linarith only [hlam, p8132_0]
                                    · have p8132_0 := h8132c.1
                                      have p8132_1 := h8132c.2.1
                                      have p8132_2 := h8132c.2.2.1
                                      have p8132_3 := h8132c.2.2.2
                                      linarith only [h7718, h8048, h8055, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8132_1]
                                    · have p8132_0 := h8132c.1
                                      have p8132_1 := h8132c.2.1
                                      have p8132_2 := h8132c.2.2.1
                                      have p8132_3 := h8132c.2.2.2
                                      linarith only [h7969, hc23, hlam, hphi, ht01, ht12, p8132_1, u0ehi1]
                                    · have p8132_0 := h8132c.1
                                      have p8132_1 := h8132c.2.1
                                      have p8132_2 := h8132c.2.2.1
                                      have p8132_3 := h8132c.2.2.2
                                      linarith only [hc24, hlam, hphi, ht01, ht12, p8132_1, u0ehi1]
                                    · have p8132_0 := h8132c.1
                                      have p8132_1 := h8132c.2.1
                                      have p8132_2 := h8132c.2.2.1
                                      have p8132_3 := h8132c.2.2.2
                                      rcases p8132_3 (m.d 0 2) (by simp) with h8151 | h8151
                                      · linarith only [h7718, h8151, hlam]
                                      · linarith only [h0, h8151, hlam]
                                    · have p8132_0 := h8132c.1
                                      have p8132_1 := h8132c.2.1
                                      have p8132_2 := h8132c.2.2.1
                                      have p8132_3 := h8132c.2.2.2
                                      linarith only [h8127, hlam, p8132_1]
                                    · have p8132_0 := h8132c.1
                                      have p8132_1 := h8132c.2.1
                                      have p8132_2 := h8132c.2.2.1
                                      have p8132_3 := h8132c.2.2.2
                                      linarith only [hlam, p8132_0]
                                    · have p8132_0 := h8132c.1
                                      have p8132_1 := h8132c.2.1
                                      have p8132_2 := h8132c.2.2.1
                                      have p8132_3 := h8132c.2.2.2
                                      linarith only [h7969, h8127, hc23, hlam, hphi, ht01, ht12, p8132_1, u0ehi1]
                                    · have p8132_0 := h8132c.1
                                      have p8132_1 := h8132c.2.1
                                      have p8132_2 := h8132c.2.2.1
                                      have p8132_3 := h8132c.2.2.2
                                      linarith only [hc25, hlam, hphi, ht01, ht12, p8132_1, u0ehi1]
                                    · have p8132_0 := h8132c.1
                                      have p8132_1 := h8132c.2.1
                                      have p8132_2 := h8132c.2.2.1
                                      have p8132_3 := h8132c.2.2.2
                                      rcases p8132_3 (m.d 0 2) (by simp) with h8158 | h8158
                                      · linarith only [h7969, h8158, hlam]
                                      · linarith only [h0, h8158, hlam]
                                    · have p8132_0 := h8132c.1
                                      have p8132_1 := h8132c.2.1
                                      have p8132_2 := h8132c.2.2.1
                                      have p8132_3 := h8132c.2.2.2
                                      linarith only [h8128, hlam, p8132_1]
                                    · have p8132_0 := h8132c.1
                                      have p8132_1 := h8132c.2.1
                                      have p8132_2 := h8132c.2.2.1
                                      have p8132_3 := h8132c.2.2.2
                                      linarith only [h8129, hlam, p8132_0]
                                    · have p8132_0 := h8132c.1
                                      have p8132_1 := h8132c.2.1
                                      have p8132_2 := h8132c.2.2.1
                                      have p8132_3 := h8132c.2.2.2
                                      linarith only [hlam, p8132_0]
                                · linarith only [h7718, h8048, h8129, hc04, hlam, hphi, u0ehi1]
                              · linarith only [h1, h7715, h8049, h8054, h8128, hlam]
                            · linarith only [h1, h7715, h8049, h8051, h8127, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h1, h7715, h7969, h8054, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                      · linarith only [h1, h8046, h8053, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8169 | h8169
                  · linarith only [h0, h7716, h8169, hc01, hlam, hphi, u0ehi1]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8171 | h8171
                    · linarith only [h0, h1, h7969, h8169, h8171, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8173 | h8173
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8174 | h8174
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8175 | h8175
                          · linarith only [h7718, h8048, h8175, hc14, hlam, hphi, ht01, u0ehi1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8177 | h8177
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8178 | h8178
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8179 | h8179
                                · linarith only [h7718, h8048, h8179, hc24, hlam, hphi, ht01, ht12, u0ehi1]
                                · linarith only [h7718, h8179, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                              · linarith only [h1, h7715, h8169, h8174, h8178, hlam]
                            · linarith only [h1, h7715, h8169, h8173, h8175, h8177, hlam]
                        · linarith only [h1, h7715, h8171, h8174, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1, h7715, h7718, h8048, h8173, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
              · linarith only [h1, h7715, h8047, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h8187 | h8187
              · rcases m.htr 0 4 5 (by decide) (by decide) with h8188 | h8188
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8189 | h8189
                  · linarith only [h0, h1, h8046, h8189, hc23, hc34, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8191 | h8191
                    · linarith only [h0, h1, h7969, h8046, h8191, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8193 | h8193
                      · linarith only [h1, h7715, h8046, h8189, h8191, h8193, hc12, hc23, hlam, hphi]
                      · linarith only [h1, h7715, h7969, h8193, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                · linarith only [h1, h7715, h8046, h8188, hlam]
              · linarith only [h1, h7715, h8187, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h8198 | h8198
      · linarith only [h0, h1, h8198, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h8200 | h8200
        · rcases m.htr 0 2 5 (by decide) (by decide) with h8201 | h8201
          · linarith only [h0, h7715, h8201, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h8203 | h8203
            · rcases m.htr 0 3 5 (by decide) (by decide) with h8204 | h8204
              · rcases m.htr 0 4 5 (by decide) (by decide) with h8205 | h8205
                · linarith only [h0, h7715, h8200, h8205, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8207 | h8207
                  · linarith only [h8198, h8200, h8207, hc12, hlam, hphi, ht01, u0ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8209 | h8209
                    · linarith only [h0, h8200, h8201, h8209, hc01, hlam, hphi, u0ehi3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8211 | h8211
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8212 | h8212
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8213 | h8213
                          · linarith only [h8205, h8213, hc14, hlam, hphi, ht01, u0ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8215 | h8215
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8216 | h8216
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8217 | h8217
                                · linarith only [h0, h7715, h8200, h8213, h8217, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8219 | h8219
                                  · linarith only [h0, h7715, h8200, h8209, h8215, h8217, h8219, hlam]
                                  · rcases h2bigk with h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c | h8221c
                                    · have p8221_0 := h8221c.1
                                      have p8221_1 := h8221c.2.1
                                      have p8221_2 := h8221c.2.2.1
                                      have p8221_3 := h8221c.2.2.2
                                      linarith only [hlam, p8221_0]
                                    · have p8221_0 := h8221c.1
                                      have p8221_1 := h8221c.2.1
                                      have p8221_2 := h8221c.2.2.1
                                      have p8221_3 := h8221c.2.2.2
                                      linarith only [h0, h7715, h8209, hc12, hc25, hlam, hphi, p8221_1]
                                    · have p8221_0 := h8221c.1
                                      have p8221_1 := h8221c.2.1
                                      have p8221_2 := h8221c.2.2.1
                                      have p8221_3 := h8221c.2.2.2
                                      linarith only [h8198, hlam, p8221_0]
                                    · have p8221_0 := h8221c.1
                                      have p8221_1 := h8221c.2.1
                                      have p8221_2 := h8221c.2.2.1
                                      have p8221_3 := h8221c.2.2.2
                                      linarith only [h0, h7715, h8209, h8215, h8217, hc34, hc45, hlam, hphi, p8221_1]
                                    · have p8221_0 := h8221c.1
                                      have p8221_1 := h8221c.2.1
                                      have p8221_2 := h8221c.2.2.1
                                      have p8221_3 := h8221c.2.2.2
                                      linarith only [h8201, hlam, p8221_0]
                                    · have p8221_0 := h8221c.1
                                      have p8221_1 := h8221c.2.1
                                      have p8221_2 := h8221c.2.2.1
                                      have p8221_3 := h8221c.2.2.2
                                      linarith only [h0, hlam, p8221_0]
                                    · have p8221_0 := h8221c.1
                                      have p8221_1 := h8221c.2.1
                                      have p8221_2 := h8221c.2.2.1
                                      have p8221_3 := h8221c.2.2.2
                                      linarith only [hlam, p8221_0]
                                    · have p8221_0 := h8221c.1
                                      have p8221_1 := h8221c.2.1
                                      have p8221_2 := h8221c.2.2.1
                                      have p8221_3 := h8221c.2.2.2
                                      linarith only [h8207, hlam, p8221_0]
                                    · have p8221_0 := h8221c.1
                                      have p8221_1 := h8221c.2.1
                                      have p8221_2 := h8221c.2.2.1
                                      have p8221_3 := h8221c.2.2.2
                                      linarith only [h0, h7715, h8209, h8215, h8217, hc34, hc45, hlam, hphi, p8221_1]
                                    · have p8221_0 := h8221c.1
                                      have p8221_1 := h8221c.2.1
                                      have p8221_2 := h8221c.2.2.1
                                      have p8221_3 := h8221c.2.2.2
                                      linarith only [h8209, hlam, p8221_0]
                                    · have p8221_0 := h8221c.1
                                      have p8221_1 := h8221c.2.1
                                      have p8221_2 := h8221c.2.2.1
                                      have p8221_3 := h8221c.2.2.2
                                      linarith only [h8200, hc23, hlam, hphi, ht01, ht12, p8221_1, u0ehi3]
                                    · have p8221_0 := h8221c.1
                                      have p8221_1 := h8221c.2.1
                                      have p8221_2 := h8221c.2.2.1
                                      have p8221_3 := h8221c.2.2.2
                                      rcases p8221_3 (m.d 0 2) (by simp) with h8233 | h8233
                                      · linarith only [h8198, h8233, hlam]
                                      · linarith only [h0, h8233, hlam]
                                    · have p8221_0 := h8221c.1
                                      have p8221_1 := h8221c.2.1
                                      have p8221_2 := h8221c.2.2.1
                                      have p8221_3 := h8221c.2.2.2
                                      linarith only [hlam, p8221_0]
                                    · have p8221_0 := h8221c.1
                                      have p8221_1 := h8221c.2.1
                                      have p8221_2 := h8221c.2.2.1
                                      have p8221_3 := h8221c.2.2.2
                                      rcases p8221_3 (m.d 0 2) (by simp) with h8237 | h8237
                                      · linarith only [h8198, h8237, hlam]
                                      · linarith only [h8200, h8237, hlam]
                                    · have p8221_0 := h8221c.1
                                      have p8221_1 := h8221c.2.1
                                      have p8221_2 := h8221c.2.2.1
                                      have p8221_3 := h8221c.2.2.2
                                      linarith only [h7715, h8209, hc01, hc23, hlam, hphi, ht12, p8221_1]
                                    · have p8221_0 := h8221c.1
                                      have p8221_1 := h8221c.2.1
                                      have p8221_2 := h8221c.2.2.1
                                      have p8221_3 := h8221c.2.2.2
                                      linarith only [h8200, hlam, p8221_0]
                                    · have p8221_0 := h8221c.1
                                      have p8221_1 := h8221c.2.1
                                      have p8221_2 := h8221c.2.2.1
                                      have p8221_3 := h8221c.2.2.2
                                      linarith only [h0, h7715, h8200, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p8221_1]
                                    · have p8221_0 := h8221c.1
                                      have p8221_1 := h8221c.2.1
                                      have p8221_2 := h8221c.2.2.1
                                      have p8221_3 := h8221c.2.2.2
                                      linarith only [h8215, hlam, p8221_1]
                                    · have p8221_0 := h8221c.1
                                      have p8221_1 := h8221c.2.1
                                      have p8221_2 := h8221c.2.2.1
                                      have p8221_3 := h8221c.2.2.2
                                      linarith only [hlam, p8221_0]
                                    · have p8221_0 := h8221c.1
                                      have p8221_1 := h8221c.2.1
                                      have p8221_2 := h8221c.2.2.1
                                      have p8221_3 := h8221c.2.2.2
                                      linarith only [h8217, hlam, p8221_1]
                                    · have p8221_0 := h8221c.1
                                      have p8221_1 := h8221c.2.1
                                      have p8221_2 := h8221c.2.2.1
                                      have p8221_3 := h8221c.2.2.2
                                      linarith only [hc25, hlam, hphi, ht01, ht12, p8221_1, u0ehi1]
                                    · have p8221_0 := h8221c.1
                                      have p8221_1 := h8221c.2.1
                                      have p8221_2 := h8221c.2.2.1
                                      have p8221_3 := h8221c.2.2.2
                                      rcases p8221_3 (m.d 0 2) (by simp) with h8247 | h8247
                                      · linarith only [h8201, h8247, hlam]
                                      · linarith only [h0, h8247, hlam]
                                    · have p8221_0 := h8221c.1
                                      have p8221_1 := h8221c.2.1
                                      have p8221_2 := h8221c.2.2.1
                                      have p8221_3 := h8221c.2.2.2
                                      linarith only [h8216, hlam, p8221_1]
                                    · have p8221_0 := h8221c.1
                                      have p8221_1 := h8221c.2.1
                                      have p8221_2 := h8221c.2.2.1
                                      have p8221_3 := h8221c.2.2.2
                                      rcases p8221_3 (m.d 0 2) (by simp) with h8251 | h8251
                                      · linarith only [h8201, h8251, hlam]
                                      · linarith only [h8200, h8251, hlam]
                                    · have p8221_0 := h8221c.1
                                      have p8221_1 := h8221c.2.1
                                      have p8221_2 := h8221c.2.2.1
                                      have p8221_3 := h8221c.2.2.2
                                      linarith only [hlam, p8221_0]
                              · linarith only [h1, h8204, h8207, h8216, hlam]
                            · linarith only [h0, h1, h8200, h8207, h8215, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                        · linarith only [h0, h1, h8200, h8204, h8212, hc03, hlam, hphi, u0ehi3]
                      · linarith only [h0, h1, h8200, h8203, h8211, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h8259 | h8259
                · linarith only [h0, h7715, h8200, h8259, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8261 | h8261
                  · linarith only [h8198, h8261, hc12, hlam, hphi, ht01, u0ehi1]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8263 | h8263
                    · linarith only [h0, h1, h8200, h8201, h8204, h8263, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8265 | h8265
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8266 | h8266
                        · linarith only [h0, h1, h8204, h8261, h8266, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h8200, h8266, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                      · linarith only [h0, h1, h8200, h8203, h8265, hc03, hlam, hphi, u0ehi3]
            · linarith only [h0, h1, h8200, h8203, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h8271 | h8271
          · linarith only [h0, h7715, h8271, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h8273 | h8273
            · rcases m.htr 0 3 5 (by decide) (by decide) with h8274 | h8274
              · rcases m.htr 0 4 5 (by decide) (by decide) with h8275 | h8275
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8276 | h8276
                  · linarith only [h0, h8198, h8276, hc01, hlam, hphi, u0ehi1]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8278 | h8278
                    · linarith only [h0, h1, h8271, h8276, h8278, hc23, hlam, hphi, ht01, ht12, u0ehi4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8280 | h8280
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8281 | h8281
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8282 | h8282
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8283 | h8283
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8284 | h8284
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8285 | h8285
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8286 | h8286
                                  · rcases h2bigk with h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c | h8287c
                                    · have p8287_0 := h8287c.1
                                      have p8287_1 := h8287c.2.1
                                      have p8287_2 := h8287c.2.2.1
                                      have p8287_3 := h8287c.2.2.2
                                      linarith only [hlam, p8287_0]
                                    · have p8287_0 := h8287c.1
                                      have p8287_1 := h8287c.2.1
                                      have p8287_2 := h8287c.2.2.1
                                      have p8287_3 := h8287c.2.2.2
                                      linarith only [h0, h1, h8276, hc12, hc23, hlam, hphi, p8287_1]
                                    · have p8287_0 := h8287c.1
                                      have p8287_1 := h8287c.2.1
                                      have p8287_2 := h8287c.2.2.1
                                      have p8287_3 := h8287c.2.2.2
                                      linarith only [h8198, hlam, p8287_0]
                                    · have p8287_0 := h8287c.1
                                      have p8287_1 := h8287c.2.1
                                      have p8287_2 := h8287c.2.2.1
                                      have p8287_3 := h8287c.2.2.2
                                      linarith only [h8200, hlam, p8287_0]
                                    · have p8287_0 := h8287c.1
                                      have p8287_1 := h8287c.2.1
                                      have p8287_2 := h8287c.2.2.1
                                      have p8287_3 := h8287c.2.2.2
                                      linarith only [h8271, hlam, p8287_0]
                                    · have p8287_0 := h8287c.1
                                      have p8287_1 := h8287c.2.1
                                      have p8287_2 := h8287c.2.2.1
                                      have p8287_3 := h8287c.2.2.2
                                      linarith only [h0, hlam, p8287_0]
                                    · have p8287_0 := h8287c.1
                                      have p8287_1 := h8287c.2.1
                                      have p8287_2 := h8287c.2.2.1
                                      have p8287_3 := h8287c.2.2.2
                                      linarith only [hlam, p8287_0]
                                    · have p8287_0 := h8287c.1
                                      have p8287_1 := h8287c.2.1
                                      have p8287_2 := h8287c.2.2.1
                                      have p8287_3 := h8287c.2.2.2
                                      linarith only [h8276, hlam, p8287_0]
                                    · have p8287_0 := h8287c.1
                                      have p8287_1 := h8287c.2.1
                                      have p8287_2 := h8287c.2.2.1
                                      have p8287_3 := h8287c.2.2.2
                                      linarith only [h0, h7715, h8276, h8280, h8282, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8287_1]
                                    · have p8287_0 := h8287c.1
                                      have p8287_1 := h8287c.2.1
                                      have p8287_2 := h8287c.2.2.1
                                      have p8287_3 := h8287c.2.2.2
                                      linarith only [h8278, hlam, p8287_0]
                                    · have p8287_0 := h8287c.1
                                      have p8287_1 := h8287c.2.1
                                      have p8287_2 := h8287c.2.2.1
                                      have p8287_3 := h8287c.2.2.2
                                      linarith only [hc23, hlam, hphi, ht01, ht12, p8287_1, u0ehi1]
                                    · have p8287_0 := h8287c.1
                                      have p8287_1 := h8287c.2.1
                                      have p8287_2 := h8287c.2.2.1
                                      have p8287_3 := h8287c.2.2.2
                                      rcases p8287_3 (m.d 0 2) (by simp) with h8299 | h8299
                                      · linarith only [h8198, h8299, hlam]
                                      · linarith only [h0, h8299, hlam]
                                    · have p8287_0 := h8287c.1
                                      have p8287_1 := h8287c.2.1
                                      have p8287_2 := h8287c.2.2.1
                                      have p8287_3 := h8287c.2.2.2
                                      linarith only [hlam, p8287_0]
                                    · have p8287_0 := h8287c.1
                                      have p8287_1 := h8287c.2.1
                                      have p8287_2 := h8287c.2.2.1
                                      have p8287_3 := h8287c.2.2.2
                                      linarith only [h7715, h8278, h8285, hc01, hc23, hlam, hphi, ht12, p8287_1]
                                    · have p8287_0 := h8287c.1
                                      have p8287_1 := h8287c.2.1
                                      have p8287_2 := h8287c.2.2.1
                                      have p8287_3 := h8287c.2.2.2
                                      linarith only [h0, h7715, h8278, hc23, hlam, hphi, ht01, ht12, p8287_1, u0ehi1]
                                    · have p8287_0 := h8287c.1
                                      have p8287_1 := h8287c.2.1
                                      have p8287_2 := h8287c.2.2.1
                                      have p8287_3 := h8287c.2.2.2
                                      linarith only [hc24, hlam, hphi, ht01, ht12, p8287_1, u0ehi1]
                                    · have p8287_0 := h8287c.1
                                      have p8287_1 := h8287c.2.1
                                      have p8287_2 := h8287c.2.2.1
                                      have p8287_3 := h8287c.2.2.2
                                      rcases p8287_3 (m.d 0 2) (by simp) with h8306 | h8306
                                      · linarith only [h8200, h8306, hlam]
                                      · linarith only [h0, h8306, hlam]
                                    · have p8287_0 := h8287c.1
                                      have p8287_1 := h8287c.2.1
                                      have p8287_2 := h8287c.2.2.1
                                      have p8287_3 := h8287c.2.2.2
                                      linarith only [h8283, hlam, p8287_1]
                                    · have p8287_0 := h8287c.1
                                      have p8287_1 := h8287c.2.1
                                      have p8287_2 := h8287c.2.2.1
                                      have p8287_3 := h8287c.2.2.2
                                      linarith only [hlam, p8287_0]
                                    · have p8287_0 := h8287c.1
                                      have p8287_1 := h8287c.2.1
                                      have p8287_2 := h8287c.2.2.1
                                      have p8287_3 := h8287c.2.2.2
                                      linarith only [h0, h7715, h8278, h8283, hc23, hlam, hphi, ht01, ht12, p8287_1, u0ehi1]
                                    · have p8287_0 := h8287c.1
                                      have p8287_1 := h8287c.2.1
                                      have p8287_2 := h8287c.2.2.1
                                      have p8287_3 := h8287c.2.2.2
                                      linarith only [hc25, hlam, hphi, ht01, ht12, p8287_1, u0ehi1]
                                    · have p8287_0 := h8287c.1
                                      have p8287_1 := h8287c.2.1
                                      have p8287_2 := h8287c.2.2.1
                                      have p8287_3 := h8287c.2.2.2
                                      rcases p8287_3 (m.d 0 2) (by simp) with h8313 | h8313
                                      · linarith only [h8271, h8313, hlam]
                                      · linarith only [h0, h8313, hlam]
                                    · have p8287_0 := h8287c.1
                                      have p8287_1 := h8287c.2.1
                                      have p8287_2 := h8287c.2.2.1
                                      have p8287_3 := h8287c.2.2.2
                                      linarith only [h8284, hlam, p8287_1]
                                    · have p8287_0 := h8287c.1
                                      have p8287_1 := h8287c.2.1
                                      have p8287_2 := h8287c.2.2.1
                                      have p8287_3 := h8287c.2.2.2
                                      linarith only [h8285, hlam, p8287_0]
                                    · have p8287_0 := h8287c.1
                                      have p8287_1 := h8287c.2.1
                                      have p8287_2 := h8287c.2.2.1
                                      have p8287_3 := h8287c.2.2.2
                                      linarith only [hlam, p8287_0]
                                  · rcases h2bigk with h8319c | h8319c | h8319c | h8319c | h8319c | h8319c | h8319c | h8319c | h8319c | h8319c | h8319c | h8319c | h8319c | h8319c | h8319c | h8319c | h8319c | h8319c | h8319c | h8319c | h8319c | h8319c | h8319c | h8319c | h8319c
                                    · have p8319_0 := h8319c.1
                                      have p8319_1 := h8319c.2.1
                                      have p8319_2 := h8319c.2.2.1
                                      have p8319_3 := h8319c.2.2.2
                                      linarith only [hlam, p8319_0]
                                    · have p8319_0 := h8319c.1
                                      have p8319_1 := h8319c.2.1
                                      have p8319_2 := h8319c.2.2.1
                                      have p8319_3 := h8319c.2.2.2
                                      linarith only [h0, h1, h8276, hc12, hc23, hlam, hphi, p8319_1]
                                    · have p8319_0 := h8319c.1
                                      have p8319_1 := h8319c.2.1
                                      have p8319_2 := h8319c.2.2.1
                                      have p8319_3 := h8319c.2.2.2
                                      linarith only [h8198, hlam, p8319_0]
                                    · have p8319_0 := h8319c.1
                                      have p8319_1 := h8319c.2.1
                                      have p8319_2 := h8319c.2.2.1
                                      have p8319_3 := h8319c.2.2.2
                                      linarith only [h8200, hlam, p8319_0]
                                    · have p8319_0 := h8319c.1
                                      have p8319_1 := h8319c.2.1
                                      have p8319_2 := h8319c.2.2.1
                                      have p8319_3 := h8319c.2.2.2
                                      linarith only [h8271, hlam, p8319_0]
                                    · have p8319_0 := h8319c.1
                                      have p8319_1 := h8319c.2.1
                                      have p8319_2 := h8319c.2.2.1
                                      have p8319_3 := h8319c.2.2.2
                                      linarith only [h0, hlam, p8319_0]
                                    · have p8319_0 := h8319c.1
                                      have p8319_1 := h8319c.2.1
                                      have p8319_2 := h8319c.2.2.1
                                      have p8319_3 := h8319c.2.2.2
                                      linarith only [hlam, p8319_0]
                                    · have p8319_0 := h8319c.1
                                      have p8319_1 := h8319c.2.1
                                      have p8319_2 := h8319c.2.2.1
                                      have p8319_3 := h8319c.2.2.2
                                      linarith only [h8276, hlam, p8319_0]
                                    · have p8319_0 := h8319c.1
                                      have p8319_1 := h8319c.2.1
                                      have p8319_2 := h8319c.2.2.1
                                      have p8319_3 := h8319c.2.2.2
                                      linarith only [h0, h7715, h8278, h8285, hc12, hlam, hphi, ht01, p8319_1, u0ehi1]
                                    · have p8319_0 := h8319c.1
                                      have p8319_1 := h8319c.2.1
                                      have p8319_2 := h8319c.2.2.1
                                      have p8319_3 := h8319c.2.2.2
                                      linarith only [h8278, hlam, p8319_0]
                                    · have p8319_0 := h8319c.1
                                      have p8319_1 := h8319c.2.1
                                      have p8319_2 := h8319c.2.2.1
                                      have p8319_3 := h8319c.2.2.2
                                      linarith only [hc23, hlam, hphi, ht01, ht12, p8319_1, u0ehi1]
                                    · have p8319_0 := h8319c.1
                                      have p8319_1 := h8319c.2.1
                                      have p8319_2 := h8319c.2.2.1
                                      have p8319_3 := h8319c.2.2.2
                                      rcases p8319_3 (m.d 0 2) (by simp) with h8331 | h8331
                                      · linarith only [h8198, h8331, hlam]
                                      · linarith only [h0, h8331, hlam]
                                    · have p8319_0 := h8319c.1
                                      have p8319_1 := h8319c.2.1
                                      have p8319_2 := h8319c.2.2.1
                                      have p8319_3 := h8319c.2.2.2
                                      linarith only [hlam, p8319_0]
                                    · have p8319_0 := h8319c.1
                                      have p8319_1 := h8319c.2.1
                                      have p8319_2 := h8319c.2.2.1
                                      have p8319_3 := h8319c.2.2.2
                                      linarith only [h7715, h8278, h8285, hc01, hc23, hlam, hphi, ht12, p8319_1]
                                    · have p8319_0 := h8319c.1
                                      have p8319_1 := h8319c.2.1
                                      have p8319_2 := h8319c.2.2.1
                                      have p8319_3 := h8319c.2.2.2
                                      linarith only [h0, h7715, h8278, hc23, hlam, hphi, ht01, ht12, p8319_1, u0ehi1]
                                    · have p8319_0 := h8319c.1
                                      have p8319_1 := h8319c.2.1
                                      have p8319_2 := h8319c.2.2.1
                                      have p8319_3 := h8319c.2.2.2
                                      linarith only [hc24, hlam, hphi, ht01, ht12, p8319_1, u0ehi1]
                                    · have p8319_0 := h8319c.1
                                      have p8319_1 := h8319c.2.1
                                      have p8319_2 := h8319c.2.2.1
                                      have p8319_3 := h8319c.2.2.2
                                      rcases p8319_3 (m.d 0 2) (by simp) with h8338 | h8338
                                      · linarith only [h8200, h8338, hlam]
                                      · linarith only [h0, h8338, hlam]
                                    · have p8319_0 := h8319c.1
                                      have p8319_1 := h8319c.2.1
                                      have p8319_2 := h8319c.2.2.1
                                      have p8319_3 := h8319c.2.2.2
                                      linarith only [h8283, hlam, p8319_1]
                                    · have p8319_0 := h8319c.1
                                      have p8319_1 := h8319c.2.1
                                      have p8319_2 := h8319c.2.2.1
                                      have p8319_3 := h8319c.2.2.2
                                      linarith only [hlam, p8319_0]
                                    · have p8319_0 := h8319c.1
                                      have p8319_1 := h8319c.2.1
                                      have p8319_2 := h8319c.2.2.1
                                      have p8319_3 := h8319c.2.2.2
                                      linarith only [h0, h7715, h8278, h8283, hc23, hlam, hphi, ht01, ht12, p8319_1, u0ehi1]
                                    · have p8319_0 := h8319c.1
                                      have p8319_1 := h8319c.2.1
                                      have p8319_2 := h8319c.2.2.1
                                      have p8319_3 := h8319c.2.2.2
                                      linarith only [hc25, hlam, hphi, ht01, ht12, p8319_1, u0ehi1]
                                    · have p8319_0 := h8319c.1
                                      have p8319_1 := h8319c.2.1
                                      have p8319_2 := h8319c.2.2.1
                                      have p8319_3 := h8319c.2.2.2
                                      rcases p8319_3 (m.d 0 2) (by simp) with h8345 | h8345
                                      · linarith only [h8271, h8345, hlam]
                                      · linarith only [h0, h8345, hlam]
                                    · have p8319_0 := h8319c.1
                                      have p8319_1 := h8319c.2.1
                                      have p8319_2 := h8319c.2.2.1
                                      have p8319_3 := h8319c.2.2.2
                                      linarith only [h8284, hlam, p8319_1]
                                    · have p8319_0 := h8319c.1
                                      have p8319_1 := h8319c.2.1
                                      have p8319_2 := h8319c.2.2.1
                                      have p8319_3 := h8319c.2.2.2
                                      linarith only [h8285, hlam, p8319_0]
                                    · have p8319_0 := h8319c.1
                                      have p8319_1 := h8319c.2.1
                                      have p8319_2 := h8319c.2.2.1
                                      have p8319_3 := h8319c.2.2.2
                                      linarith only [hlam, p8319_0]
                                · linarith only [h8200, h8285, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                              · linarith only [h8198, h8284, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                            · linarith only [h0, h7715, h8276, h8280, h8282, h8283, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                          · linarith only [h7715, h8275, h8282, hlam]
                        · linarith only [h1, h8274, h8281, hlam]
                      · linarith only [h0, h1, h8280, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8357 | h8357
                  · linarith only [h0, h8198, h8357, hc01, hlam, hphi, u0ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8359 | h8359
                    · linarith only [h0, h8271, h8359, hc01, hlam, hphi, u0ehi1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8361 | h8361
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8362 | h8362
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8363 | h8363
                          · linarith only [h8275, h8363, hc14, hlam, hphi, ht01, u0ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8365 | h8365
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8366 | h8366
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8367 | h8367
                                · linarith only [h0, h7715, h8363, h8365, h8367, hc12, hc23, hlam, hphi]
                                · linarith only [h8200, h8367, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                              · linarith only [h8198, h8366, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                            · linarith only [h0, h7715, h8273, h8357, h8362, h8365, hc03, hlam, hphi, u0ehi1]
                        · linarith only [h0, h1, h8362, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                      · linarith only [h0, h1, h8273, h8361, hc03, hlam, hphi, u0ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h8374 | h8374
                · linarith only [h8273, h8274, h8374, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8376 | h8376
                  · linarith only [h0, h8198, h8376, hc01, hlam, hphi, u0ehi1]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8378 | h8378
                    · linarith only [h0, h1, h8271, h8274, h8378, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8380 | h8380
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8381 | h8381
                        · linarith only [h0, h1, h8274, h8376, h8381, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h8381, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                      · linarith only [h0, h1, h8273, h8380, hc03, hlam, hphi, u0ehi1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h8385 | h8385
              · rcases m.htr 0 4 5 (by decide) (by decide) with h8386 | h8386
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8387 | h8387
                  · linarith only [h0, h1, h8273, h8387, hc23, hc34, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8389 | h8389
                    · linarith only [h0, h7715, h8271, h8273, h8385, h8389, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8391 | h8391
                      · linarith only [h0, h7715, h8273, h8385, h8387, h8391, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h8391, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                · linarith only [h8273, h8385, h8386, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h8395 | h8395
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8396 | h8396
                  · linarith only [h0, h1, h8385, h8396, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8398 | h8398
                    · linarith only [h0, h1, h8271, h8385, h8398, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8400 | h8400
                      · linarith only [h0, h1, h8273, h8396, h8400, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h8400, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8403 | h8403
                  · linarith only [h0, h1, h8385, h8403, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8405 | h8405
                    · linarith only [h0, h1, h8271, h8405, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8407 | h8407
                      · linarith only [h0, h1, h8273, h8403, h8407, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h8407, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]

end R2N4
