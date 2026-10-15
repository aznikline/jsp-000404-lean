import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_47S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5924000 in
set_option maxHeartbeats 5924000 in
theorem r1l7_20_12_14_H_I_L_I_L_0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h644 | h644
  · rcases m.htr 0 2 5 (by decide) (by decide) with h645 | h645
    · rcases m.htr 0 3 4 (by decide) (by decide) with h646 | h646
      · rcases m.htr 0 3 5 (by decide) (by decide) with h647 | h647
        · rcases m.htr 0 4 5 (by decide) (by decide) with h648 | h648
          · rcases m.htr 1 2 3 (by decide) (by decide) with h649 | h649
            · linarith only [h0, h4, h644, h649, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h651 | h651
              · rcases m.htr 1 2 5 (by decide) (by decide) with h652 | h652
                · rcases m.htr 1 4 5 (by decide) (by decide) with h653 | h653
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h654 | h654
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h655 | h655
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h656 | h656
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h657 | h657
                          · rcases h0bigk with h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c | h658c
                            · have p658_0 := h658c.1
                              have p658_1 := h658c.2.1
                              have p658_2 := h658c.2.2.1
                              have p658_3 := h658c.2.2.2
                              linarith only [hlam, p658_0]
                            · have p658_0 := h658c.1
                              have p658_1 := h658c.2.1
                              have p658_2 := h658c.2.2.1
                              have p658_3 := h658c.2.2.2
                              linarith only [h0, h651, h654, h657, hc01, hc45, hlam, hphi, ht0b, ht5b, p658_1]
                            · have p658_0 := h658c.1
                              have p658_1 := h658c.2.1
                              have p658_2 := h658c.2.2.1
                              have p658_3 := h658c.2.2.2
                              linarith only [h0, h4, h651, h654, h657, hc01, hc45, hlam, hphi, ht0b, ht5b, p658_1]
                            · have p658_0 := h658c.1
                              have p658_1 := h658c.2.1
                              have p658_2 := h658c.2.2.1
                              have p658_3 := h658c.2.2.2
                              linarith only [h2, h651, h654, h657, hc01, hc45, hlam, hphi, ht0b, ht5b, p658_1]
                            · have p658_0 := h658c.1
                              have p658_1 := h658c.2.1
                              have p658_2 := h658c.2.2.1
                              have p658_3 := h658c.2.2.2
                              rcases p658_3 (m.d 0 1) (by simp) with h663 | h663
                              · rcases p658_3 (m.d 0 2) (by simp) with h664 | h664
                                · linarith only [h0, h664, hlam]
                                · linarith only [h645, h664, hlam]
                              · linarith only [h3, h663, hlam]
                            · have p658_0 := h658c.1
                              have p658_1 := h658c.2.1
                              have p658_2 := h658c.2.2.1
                              have p658_3 := h658c.2.2.2
                              linarith only [h0, hlam, p658_0]
                            · have p658_0 := h658c.1
                              have p658_1 := h658c.2.1
                              have p658_2 := h658c.2.2.1
                              have p658_3 := h658c.2.2.2
                              linarith only [hlam, p658_0]
                            · have p658_0 := h658c.1
                              have p658_1 := h658c.2.1
                              have p658_2 := h658c.2.2.1
                              have p658_3 := h658c.2.2.2
                              linarith only [h4, hlam, p658_0]
                            · have p658_0 := h658c.1
                              have p658_1 := h658c.2.1
                              have p658_2 := h658c.2.2.1
                              have p658_3 := h658c.2.2.2
                              linarith only [h2, h651, h654, h657, hc02, hc45, hlam, hphi, ht0b, ht5b, p658_1]
                            · have p658_0 := h658c.1
                              have p658_1 := h658c.2.1
                              have p658_2 := h658c.2.2.1
                              have p658_3 := h658c.2.2.2
                              linarith only [h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p658_1]
                            · have p658_0 := h658c.1
                              have p658_1 := h658c.2.1
                              have p658_2 := h658c.2.2.1
                              have p658_3 := h658c.2.2.2
                              linarith only [h1, hlam, p658_1]
                            · have p658_0 := h658c.1
                              have p658_1 := h658c.2.1
                              have p658_2 := h658c.2.2.1
                              have p658_3 := h658c.2.2.2
                              linarith only [h4, hc02, hc23, hlam, hphi, p658_1]
                            · have p658_0 := h658c.1
                              have p658_1 := h658c.2.1
                              have p658_2 := h658c.2.2.1
                              have p658_3 := h658c.2.2.2
                              linarith only [hlam, p658_0]
                            · have p658_0 := h658c.1
                              have p658_1 := h658c.2.1
                              have p658_2 := h658c.2.2.1
                              have p658_3 := h658c.2.2.2
                              linarith only [h2, h4, h651, h654, h657, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p658_1]
                            · have p658_0 := h658c.1
                              have p658_1 := h658c.2.1
                              have p658_2 := h658c.2.2.1
                              have p658_3 := h658c.2.2.2
                              rcases p658_3 (m.d 0 1) (by simp) with h677 | h677
                              · rcases p658_3 (m.d 0 2) (by simp) with h678 | h678
                                · linarith only [h4, h678, hlam]
                                · linarith only [h645, h678, hlam]
                              · linarith only [h3, h677, hlam]
                            · have p658_0 := h658c.1
                              have p658_1 := h658c.2.1
                              have p658_2 := h658c.2.2.1
                              have p658_3 := h658c.2.2.2
                              linarith only [h2, hlam, p658_0]
                            · have p658_0 := h658c.1
                              have p658_1 := h658c.2.1
                              have p658_2 := h658c.2.2.1
                              have p658_3 := h658c.2.2.2
                              linarith only [h644, hlam, p658_0]
                            · have p658_0 := h658c.1
                              have p658_1 := h658c.2.1
                              have p658_2 := h658c.2.2.1
                              have p658_3 := h658c.2.2.2
                              linarith only [h646, hlam, p658_0]
                            · have p658_0 := h658c.1
                              have p658_1 := h658c.2.1
                              have p658_2 := h658c.2.2.1
                              have p658_3 := h658c.2.2.2
                              linarith only [hlam, p658_0]
                            · have p658_0 := h658c.1
                              have p658_1 := h658c.2.1
                              have p658_2 := h658c.2.2.1
                              have p658_3 := h658c.2.2.2
                              linarith only [h3, h652, h655, h657, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p658_1, u4elo0]
                            · have p658_0 := h658c.1
                              have p658_1 := h658c.2.1
                              have p658_2 := h658c.2.2.1
                              have p658_3 := h658c.2.2.2
                              linarith only [h3, hlam, p658_0]
                            · have p658_0 := h658c.1
                              have p658_1 := h658c.2.1
                              have p658_2 := h658c.2.2.1
                              have p658_3 := h658c.2.2.2
                              linarith only [h645, hlam, p658_1]
                            · have p658_0 := h658c.1
                              have p658_1 := h658c.2.1
                              have p658_2 := h658c.2.2.1
                              have p658_3 := h658c.2.2.2
                              linarith only [h647, hlam, p658_0]
                            · have p658_0 := h658c.1
                              have p658_1 := h658c.2.1
                              have p658_2 := h658c.2.2.1
                              have p658_3 := h658c.2.2.2
                              linarith only [h648, hlam, p658_1]
                            · have p658_0 := h658c.1
                              have p658_1 := h658c.2.1
                              have p658_2 := h658c.2.2.1
                              have p658_3 := h658c.2.2.2
                              linarith only [hlam, p658_0]
                          · linarith only [h648, h657, hc34, hlam, hphi, u4elo0]
                        · linarith only [h648, h656, hc24, hlam, hphi, u4elo0]
                      · linarith only [h4, h647, h655, hlam]
                    · linarith only [h4, h654, hc02, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h648, h651, h653, hc24, hlam, hphi, u4elo0]
                · linarith only [h4, h645, h651, h652, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · linarith only [h4, h644, h651, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h699 | h699
            · linarith only [h0, h4, h645, h699, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h701 | h701
              · rcases m.htr 1 2 5 (by decide) (by decide) with h702 | h702
                · rcases m.htr 1 4 5 (by decide) (by decide) with h703 | h703
                  · linarith only [h2, h648, h703, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h705 | h705
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h706 | h706
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h707 | h707
                        · linarith only [h2, h648, h707, hc14, hlam, hphi, u4elo2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h709 | h709
                          · linarith only [h2, h648, h701, h705, h709, hlam]
                          · rcases h0bigk with h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c | h711c
                            · have p711_0 := h711c.1
                              have p711_1 := h711c.2.1
                              have p711_2 := h711c.2.2.1
                              have p711_3 := h711c.2.2.2
                              linarith only [hlam, p711_0]
                            · have p711_0 := h711c.1
                              have p711_1 := h711c.2.1
                              have p711_2 := h711c.2.2.1
                              have p711_3 := h711c.2.2.2
                              linarith only [h0, h702, h707, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p711_1]
                            · have p711_0 := h711c.1
                              have p711_1 := h711c.2.1
                              have p711_2 := h711c.2.2.1
                              have p711_3 := h711c.2.2.2
                              linarith only [h0, h4, h702, h705, h707, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p711_1]
                            · have p711_0 := h711c.1
                              have p711_1 := h711c.2.1
                              have p711_2 := h711c.2.2.1
                              have p711_3 := h711c.2.2.2
                              rcases p711_3 (m.d 0 1) (by simp) with h715 | h715
                              · rcases p711_3 (m.d 0 2) (by simp) with h716 | h716
                                · linarith only [h0, h716, hlam]
                                · linarith only [h644, h716, hlam]
                              · linarith only [h2, h715, hlam]
                            · have p711_0 := h711c.1
                              have p711_1 := h711c.2.1
                              have p711_2 := h711c.2.2.1
                              have p711_3 := h711c.2.2.2
                              rcases p711_3 (m.d 0 1) (by simp) with h720 | h720
                              · rcases p711_3 (m.d 0 2) (by simp) with h721 | h721
                                · linarith only [h0, h721, hlam]
                                · linarith only [h645, h721, hlam]
                              · linarith only [h3, h720, hlam]
                            · have p711_0 := h711c.1
                              have p711_1 := h711c.2.1
                              have p711_2 := h711c.2.2.1
                              have p711_3 := h711c.2.2.2
                              linarith only [h0, hlam, p711_0]
                            · have p711_0 := h711c.1
                              have p711_1 := h711c.2.1
                              have p711_2 := h711c.2.2.1
                              have p711_3 := h711c.2.2.2
                              linarith only [hlam, p711_0]
                            · have p711_0 := h711c.1
                              have p711_1 := h711c.2.1
                              have p711_2 := h711c.2.2.1
                              have p711_3 := h711c.2.2.2
                              linarith only [h4, hlam, p711_0]
                            · have p711_0 := h711c.1
                              have p711_1 := h711c.2.1
                              have p711_2 := h711c.2.2.1
                              have p711_3 := h711c.2.2.2
                              linarith only [h2, h4, h701, h705, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p711_1]
                            · have p711_0 := h711c.1
                              have p711_1 := h711c.2.1
                              have p711_2 := h711c.2.2.1
                              have p711_3 := h711c.2.2.2
                              linarith only [h2, h4, h648, h701, h705, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p711_1]
                            · have p711_0 := h711c.1
                              have p711_1 := h711c.2.1
                              have p711_2 := h711c.2.2.1
                              have p711_3 := h711c.2.2.2
                              linarith only [h1, hlam, p711_1]
                            · have p711_0 := h711c.1
                              have p711_1 := h711c.2.1
                              have p711_2 := h711c.2.2.1
                              have p711_3 := h711c.2.2.2
                              linarith only [h0, h702, h705, h707, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p711_1]
                            · have p711_0 := h711c.1
                              have p711_1 := h711c.2.1
                              have p711_2 := h711c.2.2.1
                              have p711_3 := h711c.2.2.2
                              linarith only [hlam, p711_0]
                            · have p711_0 := h711c.1
                              have p711_1 := h711c.2.1
                              have p711_2 := h711c.2.2.1
                              have p711_3 := h711c.2.2.2
                              rcases p711_3 (m.d 0 1) (by simp) with h733 | h733
                              · rcases p711_3 (m.d 0 2) (by simp) with h734 | h734
                                · linarith only [h4, h734, hlam]
                                · linarith only [h644, h734, hlam]
                              · linarith only [h2, h733, hlam]
                            · have p711_0 := h711c.1
                              have p711_1 := h711c.2.1
                              have p711_2 := h711c.2.2.1
                              have p711_3 := h711c.2.2.2
                              rcases p711_3 (m.d 0 1) (by simp) with h738 | h738
                              · rcases p711_3 (m.d 0 2) (by simp) with h739 | h739
                                · linarith only [h4, h739, hlam]
                                · linarith only [h645, h739, hlam]
                              · linarith only [h3, h738, hlam]
                            · have p711_0 := h711c.1
                              have p711_1 := h711c.2.1
                              have p711_2 := h711c.2.2.1
                              have p711_3 := h711c.2.2.2
                              linarith only [h2, hlam, p711_0]
                            · have p711_0 := h711c.1
                              have p711_1 := h711c.2.1
                              have p711_2 := h711c.2.2.1
                              have p711_3 := h711c.2.2.2
                              linarith only [h644, hlam, p711_0]
                            · have p711_0 := h711c.1
                              have p711_1 := h711c.2.1
                              have p711_2 := h711c.2.2.1
                              have p711_3 := h711c.2.2.2
                              linarith only [h646, hlam, p711_0]
                            · have p711_0 := h711c.1
                              have p711_1 := h711c.2.1
                              have p711_2 := h711c.2.2.1
                              have p711_3 := h711c.2.2.2
                              linarith only [hlam, p711_0]
                            · have p711_0 := h711c.1
                              have p711_1 := h711c.2.1
                              have p711_2 := h711c.2.2.1
                              have p711_3 := h711c.2.2.2
                              linarith only [h648, hlam, p711_0]
                            · have p711_0 := h711c.1
                              have p711_1 := h711c.2.1
                              have p711_2 := h711c.2.2.1
                              have p711_3 := h711c.2.2.2
                              linarith only [h3, hlam, p711_0]
                            · have p711_0 := h711c.1
                              have p711_1 := h711c.2.1
                              have p711_2 := h711c.2.2.1
                              have p711_3 := h711c.2.2.2
                              linarith only [h645, hlam, p711_1]
                            · have p711_0 := h711c.1
                              have p711_1 := h711c.2.1
                              have p711_2 := h711c.2.2.1
                              have p711_3 := h711c.2.2.2
                              linarith only [h647, hlam, p711_0]
                            · have p711_0 := h711c.1
                              have p711_1 := h711c.2.1
                              have p711_2 := h711c.2.2.1
                              have p711_3 := h711c.2.2.2
                              linarith only [h2, h4, h645, h701, h705, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p711_1]
                            · have p711_0 := h711c.1
                              have p711_1 := h711c.2.1
                              have p711_2 := h711c.2.2.1
                              have p711_3 := h711c.2.2.2
                              linarith only [hlam, p711_0]
                      · linarith only [h4, h647, h706, hlam]
                    · linarith only [h4, h705, hc02, hlam, hphi, ht23, ht34, u4elo3]
                · linarith only [h4, h645, h701, h702, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · linarith only [h4, h644, h701, hc12, hc23, hlam, hphi]
        · linarith only [h4, h645, h647, hlam]
      · linarith only [h4, h644, h646, hc24, hlam, hphi, u4elo3]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h759 | h759
      · rcases m.htr 0 3 5 (by decide) (by decide) with h760 | h760
        · rcases m.htr 0 4 5 (by decide) (by decide) with h761 | h761
          · linarith only [h644, h645, h761, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h763 | h763
            · linarith only [h0, h4, h763, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h765 | h765
              · rcases m.htr 1 2 5 (by decide) (by decide) with h766 | h766
                · linarith only [h0, h645, h766, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h768 | h768
                  · linarith only [h761, h768, hc04, hlam, hphi, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h770 | h770
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h771 | h771
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h772 | h772
                        · linarith only [h644, h645, h761, h772, hlam]
                        · linarith only [h0, h645, h765, h770, h772, hc34, hlam, hphi, u4elo4]
                      · linarith only [h0, h1, h4, h760, h765, h770, h771, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h4, h770, hc02, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h4, h644, h765, hc12, hc23, hlam, hphi]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h778 | h778
          · linarith only [h4, h644, h760, h778, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h780 | h780
            · linarith only [h0, h4, h644, h780, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h782 | h782
              · rcases m.htr 1 2 5 (by decide) (by decide) with h783 | h783
                · linarith only [h0, h645, h783, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h785 | h785
                  · linarith only [h778, h785, hc04, hlam, hphi, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h787 | h787
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h788 | h788
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h789 | h789
                        · linarith only [h0, h4, h760, h778, h782, h789, hlam]
                        · linarith only [h0, h645, h782, h787, h789, hc34, hlam, hphi, u4elo4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h792 | h792
                        · linarith only [h2, h778, h792, hc14, hlam, hphi, u4elo2]
                        · linarith only [h4, h644, h787, h788, h792, hc34, hlam, hphi, u4elo4]
                    · linarith only [h0, h4, h782, h787, hc24, hlam, hphi, u4elo3]
              · linarith only [h4, h644, h782, hc12, hc23, hlam, hphi]
      · linarith only [h4, h644, h759, hc24, hlam, hphi, u4elo3]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h798 | h798
    · rcases m.htr 0 3 4 (by decide) (by decide) with h799 | h799
      · rcases m.htr 0 3 5 (by decide) (by decide) with h800 | h800
        · rcases m.htr 0 4 5 (by decide) (by decide) with h801 | h801
          · rcases m.htr 1 2 3 (by decide) (by decide) with h802 | h802
            · linarith only [h0, h644, h802, hc23, hlam, hphi, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h804 | h804
              · linarith only [h0, h644, h804, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h806 | h806
                · rcases m.htr 1 4 5 (by decide) (by decide) with h807 | h807
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h808 | h808
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h809 | h809
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h810 | h810
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h811 | h811
                          · rcases h0bigk with h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c
                            · have p812_0 := h812c.1
                              have p812_1 := h812c.2.1
                              have p812_2 := h812c.2.2.1
                              have p812_3 := h812c.2.2.2
                              linarith only [hlam, p812_0]
                            · have p812_0 := h812c.1
                              have p812_1 := h812c.2.1
                              have p812_2 := h812c.2.2.1
                              have p812_3 := h812c.2.2.2
                              linarith only [h0, h806, h809, h811, hc01, hc45, hlam, hphi, ht0b, ht5b, p812_1]
                            · have p812_0 := h812c.1
                              have p812_1 := h812c.2.1
                              have p812_2 := h812c.2.2.1
                              have p812_3 := h812c.2.2.2
                              linarith only [h799, h811, hc01, hc45, hlam, hphi, ht0b, ht5b, p812_1]
                            · have p812_0 := h812c.1
                              have p812_1 := h812c.2.1
                              have p812_2 := h812c.2.2.1
                              have p812_3 := h812c.2.2.2
                              linarith only [h0, h644, h806, h809, h811, hc01, hc45, hlam, hphi, ht0b, ht5b, p812_1]
                            · have p812_0 := h812c.1
                              have p812_1 := h812c.2.1
                              have p812_2 := h812c.2.2.1
                              have p812_3 := h812c.2.2.2
                              rcases p812_3 (m.d 0 1) (by simp) with h817 | h817
                              · rcases p812_3 (m.d 0 2) (by simp) with h818 | h818
                                · linarith only [h0, h818, hlam]
                                · linarith only [h798, h818, hlam]
                              · linarith only [h3, h817, hlam]
                            · have p812_0 := h812c.1
                              have p812_1 := h812c.2.1
                              have p812_2 := h812c.2.2.1
                              have p812_3 := h812c.2.2.2
                              linarith only [h0, hlam, p812_0]
                            · have p812_0 := h812c.1
                              have p812_1 := h812c.2.1
                              have p812_2 := h812c.2.2.1
                              have p812_3 := h812c.2.2.2
                              linarith only [hlam, p812_0]
                            · have p812_0 := h812c.1
                              have p812_1 := h812c.2.1
                              have p812_2 := h812c.2.2.1
                              have p812_3 := h812c.2.2.2
                              linarith only [h4, hlam, p812_0]
                            · have p812_0 := h812c.1
                              have p812_1 := h812c.2.1
                              have p812_2 := h812c.2.2.1
                              have p812_3 := h812c.2.2.2
                              linarith only [h644, hlam, p812_1]
                            · have p812_0 := h812c.1
                              have p812_1 := h812c.2.1
                              have p812_2 := h812c.2.2.1
                              have p812_3 := h812c.2.2.2
                              linarith only [h644, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p812_1, u4elo2]
                            · have p812_0 := h812c.1
                              have p812_1 := h812c.2.1
                              have p812_2 := h812c.2.2.1
                              have p812_3 := h812c.2.2.2
                              linarith only [h1, hlam, p812_1]
                            · have p812_0 := h812c.1
                              have p812_1 := h812c.2.1
                              have p812_2 := h812c.2.2.1
                              have p812_3 := h812c.2.2.2
                              linarith only [h0, h806, hc03, hc25, hlam, hphi, ht0b, ht5b, p812_1]
                            · have p812_0 := h812c.1
                              have p812_1 := h812c.2.1
                              have p812_2 := h812c.2.2.1
                              have p812_3 := h812c.2.2.2
                              linarith only [hlam, p812_0]
                            · have p812_0 := h812c.1
                              have p812_1 := h812c.2.1
                              have p812_2 := h812c.2.2.1
                              have p812_3 := h812c.2.2.2
                              linarith only [h0, h644, h806, h809, h811, hc03, hc45, hlam, hphi, ht0b, ht5b, p812_1]
                            · have p812_0 := h812c.1
                              have p812_1 := h812c.2.1
                              have p812_2 := h812c.2.2.1
                              have p812_3 := h812c.2.2.2
                              rcases p812_3 (m.d 0 1) (by simp) with h831 | h831
                              · rcases p812_3 (m.d 0 2) (by simp) with h832 | h832
                                · linarith only [h4, h832, hlam]
                                · linarith only [h798, h832, hlam]
                              · linarith only [h3, h831, hlam]
                            · have p812_0 := h812c.1
                              have p812_1 := h812c.2.1
                              have p812_2 := h812c.2.2.1
                              have p812_3 := h812c.2.2.2
                              linarith only [h2, hlam, p812_0]
                            · have p812_0 := h812c.1
                              have p812_1 := h812c.2.1
                              have p812_2 := h812c.2.2.1
                              have p812_3 := h812c.2.2.2
                              linarith only [h0, h806, h809, h811, hc04, hc45, hlam, hphi, ht0b, ht5b, p812_1]
                            · have p812_0 := h812c.1
                              have p812_1 := h812c.2.1
                              have p812_2 := h812c.2.2.1
                              have p812_3 := h812c.2.2.2
                              linarith only [h799, hlam, p812_0]
                            · have p812_0 := h812c.1
                              have p812_1 := h812c.2.1
                              have p812_2 := h812c.2.2.1
                              have p812_3 := h812c.2.2.2
                              linarith only [hlam, p812_0]
                            · have p812_0 := h812c.1
                              have p812_1 := h812c.2.1
                              have p812_2 := h812c.2.2.1
                              have p812_3 := h812c.2.2.2
                              linarith only [h3, h644, h806, h809, h811, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p812_1, u4elo2]
                            · have p812_0 := h812c.1
                              have p812_1 := h812c.2.1
                              have p812_2 := h812c.2.2.1
                              have p812_3 := h812c.2.2.2
                              linarith only [h3, hlam, p812_0]
                            · have p812_0 := h812c.1
                              have p812_1 := h812c.2.1
                              have p812_2 := h812c.2.2.1
                              have p812_3 := h812c.2.2.2
                              linarith only [h798, hlam, p812_1]
                            · have p812_0 := h812c.1
                              have p812_1 := h812c.2.1
                              have p812_2 := h812c.2.2.1
                              have p812_3 := h812c.2.2.2
                              linarith only [h800, hlam, p812_0]
                            · have p812_0 := h812c.1
                              have p812_1 := h812c.2.1
                              have p812_2 := h812c.2.2.1
                              have p812_3 := h812c.2.2.2
                              linarith only [h801, hlam, p812_1]
                            · have p812_0 := h812c.1
                              have p812_1 := h812c.2.1
                              have p812_2 := h812c.2.2.1
                              have p812_3 := h812c.2.2.2
                              linarith only [hlam, p812_0]
                          · linarith only [h644, h801, h811, hc34, hlam, hphi, u4elo2]
                        · linarith only [h0, h644, h806, h809, h810, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                      · linarith only [h4, h800, h809, hlam]
                    · linarith only [h0, h4, h806, h808, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                  · linarith only [h801, h807, hc14, hlam, hphi, u4elo0]
                · linarith only [h644, h798, h806, hc12, hlam, hphi, ht23, ht34, u4elo2]
          · linarith only [h644, h798, h801, hlam]
        · linarith only [h644, h798, h799, h800, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h854 | h854
        · rcases m.htr 0 4 5 (by decide) (by decide) with h855 | h855
          · rcases m.htr 1 2 3 (by decide) (by decide) with h856 | h856
            · linarith only [h0, h4, h798, h856, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h858 | h858
              · linarith only [h0, h4, h799, h858, hc24, hlam, hphi, u4elo3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h860 | h860
                · rcases m.htr 1 4 5 (by decide) (by decide) with h861 | h861
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h862 | h862
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h863 | h863
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h864 | h864
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h865 | h865
                          · rcases h0bigk with h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c | h866c
                            · have p866_0 := h866c.1
                              have p866_1 := h866c.2.1
                              have p866_2 := h866c.2.2.1
                              have p866_3 := h866c.2.2.2
                              linarith only [hlam, p866_0]
                            · have p866_0 := h866c.1
                              have p866_1 := h866c.2.1
                              have p866_2 := h866c.2.2.1
                              have p866_3 := h866c.2.2.2
                              linarith only [h0, h860, h863, h865, hc01, hc45, hlam, hphi, ht0b, ht5b, p866_1]
                            · have p866_0 := h866c.1
                              have p866_1 := h866c.2.1
                              have p866_2 := h866c.2.2.1
                              have p866_3 := h866c.2.2.2
                              linarith only [h0, h4, h860, h863, h865, hc01, hc45, hlam, hphi, ht0b, ht5b, p866_1]
                            · have p866_0 := h866c.1
                              have p866_1 := h866c.2.1
                              have p866_2 := h866c.2.2.1
                              have p866_3 := h866c.2.2.2
                              linarith only [h0, h4, h799, h860, h863, h865, hc01, hc45, hlam, hphi, ht0b, ht5b, p866_1]
                            · have p866_0 := h866c.1
                              have p866_1 := h866c.2.1
                              have p866_2 := h866c.2.2.1
                              have p866_3 := h866c.2.2.2
                              rcases p866_3 (m.d 0 1) (by simp) with h871 | h871
                              · rcases p866_3 (m.d 0 2) (by simp) with h872 | h872
                                · linarith only [h0, h872, hlam]
                                · linarith only [h798, h872, hlam]
                              · linarith only [h3, h871, hlam]
                            · have p866_0 := h866c.1
                              have p866_1 := h866c.2.1
                              have p866_2 := h866c.2.2.1
                              have p866_3 := h866c.2.2.2
                              linarith only [h0, hlam, p866_0]
                            · have p866_0 := h866c.1
                              have p866_1 := h866c.2.1
                              have p866_2 := h866c.2.2.1
                              have p866_3 := h866c.2.2.2
                              linarith only [hlam, p866_0]
                            · have p866_0 := h866c.1
                              have p866_1 := h866c.2.1
                              have p866_2 := h866c.2.2.1
                              have p866_3 := h866c.2.2.2
                              linarith only [h4, hlam, p866_0]
                            · have p866_0 := h866c.1
                              have p866_1 := h866c.2.1
                              have p866_2 := h866c.2.2.1
                              have p866_3 := h866c.2.2.2
                              linarith only [h644, hlam, p866_1]
                            · have p866_0 := h866c.1
                              have p866_1 := h866c.2.1
                              have p866_2 := h866c.2.2.1
                              have p866_3 := h866c.2.2.2
                              linarith only [h4, h799, h862, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p866_1, u4elo2]
                            · have p866_0 := h866c.1
                              have p866_1 := h866c.2.1
                              have p866_2 := h866c.2.2.1
                              have p866_3 := h866c.2.2.2
                              linarith only [h1, hlam, p866_1]
                            · have p866_0 := h866c.1
                              have p866_1 := h866c.2.1
                              have p866_2 := h866c.2.2.1
                              have p866_3 := h866c.2.2.2
                              linarith only [h799, h862, hc02, hlam, hphi, ht23, ht34, p866_1, u4elo2]
                            · have p866_0 := h866c.1
                              have p866_1 := h866c.2.1
                              have p866_2 := h866c.2.2.1
                              have p866_3 := h866c.2.2.2
                              linarith only [hlam, p866_0]
                            · have p866_0 := h866c.1
                              have p866_1 := h866c.2.1
                              have p866_2 := h866c.2.2.1
                              have p866_3 := h866c.2.2.2
                              linarith only [h799, hlam, p866_1]
                            · have p866_0 := h866c.1
                              have p866_1 := h866c.2.1
                              have p866_2 := h866c.2.2.1
                              have p866_3 := h866c.2.2.2
                              linarith only [h798, h799, h862, h863, h865, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p866_1, u4elo2]
                            · have p866_0 := h866c.1
                              have p866_1 := h866c.2.1
                              have p866_2 := h866c.2.2.1
                              have p866_3 := h866c.2.2.2
                              linarith only [h2, hlam, p866_0]
                            · have p866_0 := h866c.1
                              have p866_1 := h866c.2.1
                              have p866_2 := h866c.2.2.1
                              have p866_3 := h866c.2.2.2
                              linarith only [h0, h860, h863, h865, hc04, hc45, hlam, hphi, ht0b, ht5b, p866_1]
                            · have p866_0 := h866c.1
                              have p866_1 := h866c.2.1
                              have p866_2 := h866c.2.2.1
                              have p866_3 := h866c.2.2.2
                              linarith only [h799, h862, hc03, hlam, hphi, ht34, p866_1, u4elo2]
                            · have p866_0 := h866c.1
                              have p866_1 := h866c.2.1
                              have p866_2 := h866c.2.2.1
                              have p866_3 := h866c.2.2.2
                              linarith only [hlam, p866_0]
                            · have p866_0 := h866c.1
                              have p866_1 := h866c.2.1
                              have p866_2 := h866c.2.2.1
                              have p866_3 := h866c.2.2.2
                              linarith only [h798, h799, h862, h863, h865, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p866_1, u4elo2]
                            · have p866_0 := h866c.1
                              have p866_1 := h866c.2.1
                              have p866_2 := h866c.2.2.1
                              have p866_3 := h866c.2.2.2
                              linarith only [h3, hlam, p866_0]
                            · have p866_0 := h866c.1
                              have p866_1 := h866c.2.1
                              have p866_2 := h866c.2.2.1
                              have p866_3 := h866c.2.2.2
                              linarith only [h798, hlam, p866_1]
                            · have p866_0 := h866c.1
                              have p866_1 := h866c.2.1
                              have p866_2 := h866c.2.2.1
                              have p866_3 := h866c.2.2.2
                              linarith only [h854, hlam, p866_0]
                            · have p866_0 := h866c.1
                              have p866_1 := h866c.2.1
                              have p866_2 := h866c.2.2.1
                              have p866_3 := h866c.2.2.2
                              linarith only [h855, hlam, p866_1]
                            · have p866_0 := h866c.1
                              have p866_1 := h866c.2.1
                              have p866_2 := h866c.2.2.1
                              have p866_3 := h866c.2.2.2
                              linarith only [hlam, p866_0]
                          · linarith only [h0, h4, h799, h860, h863, h865, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                        · linarith only [h0, h644, h860, h863, h864, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                      · linarith only [h0, h4, h799, h860, h862, h863, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h0, h4, h860, h862, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                  · linarith only [h855, h858, h860, h861, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
                · linarith only [h644, h798, h860, hc12, hlam, hphi, ht23, ht34, u4elo2]
          · linarith only [h4, h798, h799, h855, hlam]
        · linarith only [h4, h798, h854, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h904 | h904
      · rcases m.htr 0 3 5 (by decide) (by decide) with h905 | h905
        · rcases m.htr 0 4 5 (by decide) (by decide) with h906 | h906
          · rcases m.htr 1 2 3 (by decide) (by decide) with h907 | h907
            · linarith only [h0, h4, h907, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h909 | h909
              · linarith only [h0, h644, h909, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h911 | h911
                · linarith only [h0, h798, h911, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h913 | h913
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h914 | h914
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h915 | h915
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h916 | h916
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h917 | h917
                          · rcases h0bigk with h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [hlam, p918_0]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              rcases p918_3 (m.d 0 1) (by simp) with h920 | h920
                              · rcases p918_3 (m.d 0 2) (by simp) with h921 | h921
                                · linarith only [h0, h921, hlam]
                                · rcases p918_3 (m.d 0 3) (by simp) with h923 | h923
                                  · linarith only [h1, h923, hlam]
                                  · linarith only [h4, h923, hlam]
                              · linarith only [h0, h920, hlam]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [h904, h917, hc01, hc45, hlam, hphi, ht0b, ht5b, p918_1]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [h2, h913, hc01, hc45, hlam, hphi, ht0b, ht5b, p918_1]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              rcases p918_3 (m.d 0 1) (by simp) with h929 | h929
                              · rcases p918_3 (m.d 0 2) (by simp) with h930 | h930
                                · linarith only [h0, h930, hlam]
                                · rcases p918_3 (m.d 0 3) (by simp) with h932 | h932
                                  · linarith only [h1, h932, hlam]
                                  · linarith only [h905, h932, hlam]
                              · linarith only [h3, h929, hlam]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [h0, hlam, p918_0]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [hlam, p918_0]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [h4, hlam, p918_0]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [h644, hlam, p918_1]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [h798, hlam, p918_0]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [h1, hlam, p918_1]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [h4, hc02, hc23, hlam, hphi, p918_1]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [hlam, p918_0]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [h2, h4, h913, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p918_1]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [h0, h4, h798, hc12, hc23, hlam, hphi, p918_1]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [h2, hlam, p918_0]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht23, ht34, p918_1, u4elo0]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [h904, hlam, p918_0]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [hlam, p918_0]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [h0, h644, h798, hc12, hlam, hphi, ht23, ht34, p918_1, u4elo2]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [h3, hlam, p918_0]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [h0, h798, hc12, hc25, hlam, hphi, p918_1]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [h905, hlam, p918_0]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [h906, hlam, p918_1]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [hlam, p918_0]
                          · linarith only [h913, h917, hc34, hlam, hphi, u4elo1]
                        · linarith only [h2, h644, h913, h916, hlam]
                      · linarith only [h0, h4, h644, h905, h906, h915, hc12, hlam, hphi, ht23, ht34, u4elo2]
                    · linarith only [h0, h4, h914, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h644, h906, h913, hc14, hlam, hphi, u4elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h961 | h961
            · linarith only [h0, h4, h961, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h963 | h963
              · linarith only [h0, h644, h963, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h965 | h965
                · linarith only [h0, h798, h965, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h967 | h967
                  · linarith only [h644, h906, h967, hc02, hlam, hphi, ht23, ht34, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h969 | h969
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h970 | h970
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h971 | h971
                        · linarith only [h0, h644, h906, h971, hc12, hlam, hphi, ht23, ht34, u4elo2]
                        · linarith only [h0, h644, h971, hc12, hlam, hphi, ht23, ht34, u4elo4]
                      · linarith only [h4, h905, h970, hlam]
                    · linarith only [h0, h4, h969, hc12, hlam, hphi, ht23, ht34, u4elo3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h976 | h976
          · linarith only [h904, h905, h976, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h978 | h978
            · linarith only [h0, h4, h978, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h980 | h980
              · linarith only [h0, h644, h980, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h982 | h982
                · linarith only [h0, h798, h982, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h984 | h984
                  · linarith only [h2, h976, h984, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h986 | h986
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h987 | h987
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h988 | h988
                        · linarith only [h976, h988, hc04, hlam, hphi, u4elo2]
                        · linarith only [h0, h644, h988, hc12, hlam, hphi, ht23, ht34, u4elo4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h991 | h991
                        · linarith only [h0, h644, h976, h991, hc12, hlam, hphi, ht23, ht34, u4elo2]
                        · linarith only [h0, h644, h991, hc12, hlam, hphi, ht23, ht34, u4elo4]
                    · linarith only [h0, h4, h986, hc12, hlam, hphi, ht23, ht34, u4elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h995 | h995
        · rcases m.htr 0 4 5 (by decide) (by decide) with h996 | h996
          · rcases m.htr 1 2 3 (by decide) (by decide) with h997 | h997
            · linarith only [h0, h644, h997, hc23, hlam, hphi, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h999 | h999
              · linarith only [h0, h644, h999, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1001 | h1001
                · linarith only [h0, h1001, h798, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1003 | h1003
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1004 | h1004
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1005 | h1005
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1006 | h1006
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1007 | h1007
                          · rcases h0bigk with h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [hlam, p1008_0]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              rcases p1008_3 (m.d 0 1) (by simp) with h1010 | h1010
                              · rcases p1008_3 (m.d 0 2) (by simp) with h1011 | h1011
                                · linarith only [h0, h1011, hlam]
                                · rcases p1008_3 (m.d 0 3) (by simp) with h1013 | h1013
                                  · linarith only [h1, h1013, hlam]
                                  · linarith only [h1013, h4, hlam]
                              · linarith only [h0, h1010, hlam]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h1007, h995, hc01, hc45, hlam, hphi, ht0b, ht5b, p1008_1]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h1007, h904, h995, hc01, hc45, hlam, hphi, ht0b, ht5b, p1008_1]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              rcases p1008_3 (m.d 0 1) (by simp) with h1019 | h1019
                              · rcases p1008_3 (m.d 0 2) (by simp) with h1020 | h1020
                                · linarith only [h0, h1020, hlam]
                                · rcases p1008_3 (m.d 0 3) (by simp) with h1022 | h1022
                                  · linarith only [h1, h1022, hlam]
                                  · linarith only [h1022, h995, hlam]
                              · linarith only [h1019, h3, hlam]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h0, hlam, p1008_0]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [hlam, p1008_0]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h4, hlam, p1008_0]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h644, hlam, p1008_1]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h798, hlam, p1008_0]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h1, hlam, p1008_1]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h0, h1004, h904, hc12, hlam, hphi, ht23, ht34, p1008_1, u4elo2]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [hlam, p1008_0]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h904, hlam, p1008_1]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h0, h1004, h798, h904, hc12, hlam, hphi, ht23, ht34, p1008_1, u4elo2]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h2, hlam, p1008_0]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht23, ht34, p1008_1, u4elo0]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h1004, h1007, h904, h995, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1008_1, u4elo2]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [hlam, p1008_0]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h0, h1004, h798, h904, hc12, hlam, hphi, ht23, ht34, p1008_1, u4elo2]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h3, hlam, p1008_0]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h0, h798, hc12, hc25, hlam, hphi, p1008_1]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h995, hlam, p1008_0]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [h996, hlam, p1008_1]
                            · have p1008_0 := h1008c.1
                              have p1008_1 := h1008c.2.1
                              have p1008_2 := h1008c.2.2.1
                              have p1008_3 := h1008c.2.2.2
                              linarith only [hlam, p1008_0]
                          · linarith only [h1007, h904, hc03, hlam, hphi, ht34, u4elo4]
                        · linarith only [h1003, h1006, h3, h904, h995, hc24, hlam, hphi, u4elo3]
                      · linarith only [h1004, h1005, h904, h995, hc23, hlam, hphi, ht34, u4elo2]
                    · linarith only [h0, h1004, h4, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h1003, h904, h995, h996, hc14, hlam, hphi, u4elo3]
          · linarith only [h904, h995, h996, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1052 | h1052
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1053 | h1053
            · linarith only [h0, h1053, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1055 | h1055
              · linarith only [h0, h1055, h644, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1057 | h1057
                · linarith only [h0, h1057, h798, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1059 | h1059
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1060 | h1060
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1061 | h1061
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1062 | h1062
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1063 | h1063
                          · rcases h0bigk with h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              rcases p1064_3 (m.d 0 1) (by simp) with h1066 | h1066
                              · rcases p1064_3 (m.d 0 2) (by simp) with h1067 | h1067
                                · linarith only [h0, h1067, hlam]
                                · rcases p1064_3 (m.d 0 3) (by simp) with h1069 | h1069
                                  · linarith only [h1, h1069, hlam]
                                  · linarith only [h1069, h4, hlam]
                              · linarith only [h0, h1066, hlam]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              rcases p1064_3 (m.d 0 1) (by simp) with h1073 | h1073
                              · rcases p1064_3 (m.d 0 2) (by simp) with h1074 | h1074
                                · linarith only [h0, h1074, hlam]
                                · rcases p1064_3 (m.d 0 3) (by simp) with h1076 | h1076
                                  · linarith only [h1, h1076, hlam]
                                  · rcases p1064_3 (m.d 0 4) (by simp) with h1078 | h1078
                                    · linarith only [h1078, h2, hlam]
                                    · linarith only [h1078, h904, hlam]
                              · linarith only [h1, h1073, hlam]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1059, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1064_1]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              rcases p1064_3 (m.d 0 1) (by simp) with h1083 | h1083
                              · rcases p1064_3 (m.d 0 2) (by simp) with h1084 | h1084
                                · linarith only [h0, h1084, hlam]
                                · rcases p1064_3 (m.d 0 3) (by simp) with h1086 | h1086
                                  · linarith only [h1, h1086, hlam]
                                  · rcases p1064_3 (m.d 0 4) (by simp) with h1088 | h1088
                                    · linarith only [h1088, h2, hlam]
                                    · linarith only [h1052, h1088, hlam]
                              · linarith only [h1083, h3, hlam]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h0, hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h4, hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h644, hlam, p1064_1]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h798, hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1, hlam, p1064_1]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h0, h1060, h1063, h995, hc12, hc23, hlam, hphi, p1064_1]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h904, hlam, p1064_1]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h995, hlam, p1064_1]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h2, hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht23, ht34, p1064_1, u4elo0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h644, hc03, hlam, hphi, ht34, p1064_1, u4elo2]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h0, h4, h644, h995, hc12, hlam, hphi, ht23, ht34, p1064_1, u4elo2]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h3, hlam, p1064_0]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h0, h1062, h798, hc12, hlam, hphi, ht23, ht34, p1064_1, u4elo2]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h0, h1061, h1062, h4, h995, hc12, hlam, hphi, ht23, ht34, p1064_1, u4elo2]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [h1052, hlam, p1064_1]
                            · have p1064_0 := h1064c.1
                              have p1064_1 := h1064c.2.1
                              have p1064_2 := h1064c.2.2.1
                              have p1064_3 := h1064c.2.2.2
                              linarith only [hlam, p1064_0]
                          · linarith only [h0, h1063, h4, h904, hc12, hlam, hphi, ht23, ht34, u4elo4]
                        · linarith only [h1059, h1062, h2, hc24, hlam, hphi, u4elo0]
                      · linarith only [h1060, h1061, h4, h904, hc02, hc35, hlam, hphi, ht23]
                    · linarith only [h0, h1060, h4, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h1052, h1059, h644, hc14, hlam, hphi, u4elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1117 | h1117
            · linarith only [h0, h1117, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1119 | h1119
              · linarith only [h0, h1119, h644, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1121 | h1121
                · linarith only [h0, h1121, h798, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1123 | h1123
                  · linarith only [h1052, h1123, h904, hc03, hlam, hphi, ht34, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1125 | h1125
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1126 | h1126
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1127 | h1127
                        · linarith only [h1, h1052, h1117, h1127, h904, hc12, hlam, hphi, ht23, ht34, u4elo2]
                        · linarith only [h0, h1127, h644, hc12, hlam, hphi, ht23, ht34, u4elo4]
                      · linarith only [h1, h1117, h1125, h1126, h904, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h0, h1125, h4, hc12, hlam, hphi, ht23, ht34, u4elo3]

set_option maxHeartbeats 5924000 in
set_option maxHeartbeats 5924000 in
theorem r1l7_20_12_14_H_I_L_I_L_0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_20_12_14_H_I_L_I_L_0_x0_x0_x0_x0_x0 m hb0 hb2 hb4 h0 h1 h2 h3 h4
  · exact r1l7_20_12_14_H_I_L_I_L_0_x0_x0_x0_x0_x1 m hb0 hb2 hb4 h0 h1 h2 h3 h4

set_option maxHeartbeats 5924000 in
set_option maxHeartbeats 5924000 in
theorem r1l7_20_12_14_H_I_L_I_L_0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1132 | h1132
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1133 | h1133
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1134 | h1134
      · linarith only [h0, h1134, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1136 | h1136
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1137 | h1137
          · linarith only [h1, h1137, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1139 | h1139
            · linarith only [h1139, h2, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1141 | h1141
              · linarith only [h0, h1139, h1141, h3, hc23, hlam, hphi, ht34, u4elo4]
              · linarith only [h0, h1132, h1139, h1141, h3, hc12, hlam, hphi, ht23, ht34, u4elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1144 | h1144
          · linarith only [h1, h1144, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1146 | h1146
            · linarith only [h0, h1133, h1146, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1148 | h1148
              · linarith only [h0, h1146, h1148, h3, hc23, hlam, hphi, ht34, u4elo4]
              · linarith only [h0, h1132, h1146, h1148, h3, hc12, hlam, hphi, ht23, ht34, u4elo4]
    · linarith only [h1132, h1133, hc23, hlam, hphi, ht34, u4elo2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1152 | h1152
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1153 | h1153
      · linarith only [h0, h1153, h3, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1155 | h1155
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1156 | h1156
          · linarith only [h1, h1156, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1158 | h1158
            · linarith only [h0, h1152, h1158, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1160 | h1160
              · linarith only [h0, h1132, h1160, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1162 | h1162
                · linarith only [h0, h1158, h1162, h3, hc24, hlam, hphi, u4elo4]
                · linarith only [h1132, h1152, h1162, hc12, hc23, hlam, hphi]
        · linarith only [h1132, h1152, h1155, hc24, hlam, hphi, u4elo3]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1166 | h1166
      · linarith only [h0, h1152, h1166, h3, hc12, hlam, hphi, ht23, ht34, u4elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1168 | h1168
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1169 | h1169
          · linarith only [h1, h1169, h3, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1171 | h1171
            · linarith only [h1171, h2, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1173 | h1173
              · linarith only [h0, h1132, h1173, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1175 | h1175
                · linarith only [h0, h1171, h1175, h3, hc24, hlam, hphi, u4elo4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1177 | h1177
                  · linarith only [h0, h1166, h1177, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1179 | h1179
                    · linarith only [h1171, h1179, hc04, hlam, hphi, u4elo1]
                    · linarith only [h1, h1173, h1179, h3, hc12, hlam, hphi, ht23, ht34, u4elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1182 | h1182
          · linarith only [h1, h1168, h1182, h3, hc13, hlam, hphi, ht34, u4elo3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1184 | h1184
            · linarith only [h1184, h2, h3, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1186 | h1186
              · linarith only [h0, h1132, h1186, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1188 | h1188
                · linarith only [h1, h1168, h1184, h1186, h1188, hc24, hlam, hphi, u4elo4]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1190 | h1190
                  · linarith only [h0, h1166, h1190, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1192 | h1192
                    · linarith only [h1, h1168, h1184, h1186, h1192, h2, h3, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h0, h1192, h3, hc12, hlam, hphi, ht23, ht34, u4elo4]

set_option maxHeartbeats 5924000 in
set_option maxHeartbeats 5924000 in
theorem r1l7_20_12_14_H_I_L_I_L_0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_20_12_14_H_I_L_I_L_0_x0_x0_x0_x0 m hb0 hb2 hb4 h0 h1 h2 h3
  · exact r1l7_20_12_14_H_I_L_I_L_0_x0_x0_x0_x1 m hb0 hb2 hb4 h0 h1 h2 h3

set_option maxHeartbeats 5924000 in
set_option maxHeartbeats 5924000 in
theorem r1l7_20_12_14_H_I_L_I_L_0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  linarith only [h1, h2, hc13, hlam, hphi, ht34, u4elo1]

set_option maxHeartbeats 5924000 in
set_option maxHeartbeats 5924000 in
theorem r1l7_20_12_14_H_I_L_I_L_0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_20_12_14_H_I_L_I_L_0_x0_x0_x0 m hb0 hb2 hb4 h0 h1 h2
  · exact r1l7_20_12_14_H_I_L_I_L_0_x0_x0_x1 m hb0 hb2 hb4 h0 h1 h2

set_option maxHeartbeats 5924000 in
set_option maxHeartbeats 5924000 in
theorem r1l7_20_12_14_H_I_L_I_L_0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1196 | h1196
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1197 | h1197
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1198 | h1198
      · linarith only [h0, h1, h1198, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1200 | h1200
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1201 | h1201
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1202 | h1202
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1203 | h1203
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1204 | h1204
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1205 | h1205
                  · linarith only [h0, h1, h1198, h1205, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1207 | h1207
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1208 | h1208
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1209 | h1209
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1210 | h1210
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1211 | h1211
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1212 | h1212
                              · linarith only [h0, h1, h1205, h1207, h1212, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · linarith only [h1196, h1209, h1212, hc24, hlam, hphi, u4elo0]
                            · linarith only [h0, h1, h1205, h1211, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h0, h1, h1205, h1210, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h1204, h1209, hc14, hlam, hphi, u4elo0]
                      · linarith only [h0, h1, h1201, h1207, h1208, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h1, h1200, h1205, h1207, hc12, hc23, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1220 | h1220
                  · linarith only [h0, h1, h1198, h1220, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1222 | h1222
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1223 | h1223
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1224 | h1224
                        · linarith only [h1204, h1224, hc04, hlam, hphi, u4elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1226 | h1226
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1227 | h1227
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1228 | h1228
                              · linarith only [h1196, h1204, h1222, h1228, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1230 | h1230
                                · linarith only [h0, h1, h1204, h1220, h1223, h1226, h1228, h1230, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · rcases h0bigk with h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c | h1232c
                                  · have p1232_0 := h1232c.1
                                    have p1232_1 := h1232c.2.1
                                    have p1232_2 := h1232c.2.2.1
                                    have p1232_3 := h1232c.2.2.2
                                    linarith only [hlam, p1232_0]
                                  · have p1232_0 := h1232c.1
                                    have p1232_1 := h1232c.2.1
                                    have p1232_2 := h1232c.2.2.1
                                    have p1232_3 := h1232c.2.2.2
                                    linarith only [h1, h1220, hc02, hc23, hlam, hphi, p1232_1]
                                  · have p1232_0 := h1232c.1
                                    have p1232_1 := h1232c.2.1
                                    have p1232_2 := h1232c.2.2.1
                                    have p1232_3 := h1232c.2.2.2
                                    linarith only [h1, hlam, p1232_0]
                                  · have p1232_0 := h1232c.1
                                    have p1232_1 := h1232c.2.1
                                    have p1232_2 := h1232c.2.2.1
                                    have p1232_3 := h1232c.2.2.2
                                    linarith only [h1, h1196, h1220, h1222, h1226, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1232_1]
                                  · have p1232_0 := h1232c.1
                                    have p1232_1 := h1232c.2.1
                                    have p1232_2 := h1232c.2.2.1
                                    have p1232_3 := h1232c.2.2.2
                                    linarith only [h1, h1196, h1204, h1220, h1222, h1226, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1232_1]
                                  · have p1232_0 := h1232c.1
                                    have p1232_1 := h1232c.2.1
                                    have p1232_2 := h1232c.2.2.1
                                    have p1232_3 := h1232c.2.2.2
                                    linarith only [h0, hlam, p1232_0]
                                  · have p1232_0 := h1232c.1
                                    have p1232_1 := h1232c.2.1
                                    have p1232_2 := h1232c.2.2.1
                                    have p1232_3 := h1232c.2.2.2
                                    linarith only [hlam, p1232_0]
                                  · have p1232_0 := h1232c.1
                                    have p1232_1 := h1232c.2.1
                                    have p1232_2 := h1232c.2.2.1
                                    have p1232_3 := h1232c.2.2.2
                                    linarith only [h1198, hlam, p1232_0]
                                  · have p1232_0 := h1232c.1
                                    have p1232_1 := h1232c.2.1
                                    have p1232_2 := h1232c.2.2.1
                                    have p1232_3 := h1232c.2.2.2
                                    linarith only [h0, h1, h1196, h1220, h1222, h1226, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1232_1]
                                  · have p1232_0 := h1232c.1
                                    have p1232_1 := h1232c.2.1
                                    have p1232_2 := h1232c.2.2.1
                                    have p1232_3 := h1232c.2.2.2
                                    linarith only [h0, h1, h1196, h1204, h1220, h1222, h1226, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1232_1]
                                  · have p1232_0 := h1232c.1
                                    have p1232_1 := h1232c.2.1
                                    have p1232_2 := h1232c.2.2.1
                                    have p1232_3 := h1232c.2.2.2
                                    linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1232_1]
                                  · have p1232_0 := h1232c.1
                                    have p1232_1 := h1232c.2.1
                                    have p1232_2 := h1232c.2.2.1
                                    have p1232_3 := h1232c.2.2.2
                                    linarith only [h1, h1220, hc02, hc23, hlam, hphi, p1232_1]
                                  · have p1232_0 := h1232c.1
                                    have p1232_1 := h1232c.2.1
                                    have p1232_2 := h1232c.2.2.1
                                    have p1232_3 := h1232c.2.2.2
                                    linarith only [hlam, p1232_0]
                                  · have p1232_0 := h1232c.1
                                    have p1232_1 := h1232c.2.1
                                    have p1232_2 := h1232c.2.2.1
                                    have p1232_3 := h1232c.2.2.2
                                    rcases p1232_3 (m.d 0 1) (by simp) with h1246 | h1246
                                    · linarith only [h1, h1246, hlam]
                                    · linarith only [h1196, h1246, hlam]
                                  · have p1232_0 := h1232c.1
                                    have p1232_1 := h1232c.2.1
                                    have p1232_2 := h1232c.2.2.1
                                    have p1232_3 := h1232c.2.2.2
                                    rcases p1232_3 (m.d 0 1) (by simp) with h1249 | h1249
                                    · linarith only [h1, h1249, hlam]
                                    · linarith only [h1197, h1249, hlam]
                                  · have p1232_0 := h1232c.1
                                    have p1232_1 := h1232c.2.1
                                    have p1232_2 := h1232c.2.2.1
                                    have p1232_3 := h1232c.2.2.2
                                    linarith only [h1196, hlam, p1232_0]
                                  · have p1232_0 := h1232c.1
                                    have p1232_1 := h1232c.2.1
                                    have p1232_2 := h1232c.2.2.1
                                    have p1232_3 := h1232c.2.2.2
                                    linarith only [h1200, hlam, p1232_0]
                                  · have p1232_0 := h1232c.1
                                    have p1232_1 := h1232c.2.1
                                    have p1232_2 := h1232c.2.2.1
                                    have p1232_3 := h1232c.2.2.2
                                    linarith only [h1202, hlam, p1232_0]
                                  · have p1232_0 := h1232c.1
                                    have p1232_1 := h1232c.2.1
                                    have p1232_2 := h1232c.2.2.1
                                    have p1232_3 := h1232c.2.2.2
                                    linarith only [hlam, p1232_0]
                                  · have p1232_0 := h1232c.1
                                    have p1232_1 := h1232c.2.1
                                    have p1232_2 := h1232c.2.2.1
                                    have p1232_3 := h1232c.2.2.2
                                    linarith only [h1204, hlam, p1232_0]
                                  · have p1232_0 := h1232c.1
                                    have p1232_1 := h1232c.2.1
                                    have p1232_2 := h1232c.2.2.1
                                    have p1232_3 := h1232c.2.2.2
                                    linarith only [h1197, hlam, p1232_0]
                                  · have p1232_0 := h1232c.1
                                    have p1232_1 := h1232c.2.1
                                    have p1232_2 := h1232c.2.2.1
                                    have p1232_3 := h1232c.2.2.2
                                    linarith only [h1201, hlam, p1232_1]
                                  · have p1232_0 := h1232c.1
                                    have p1232_1 := h1232c.2.1
                                    have p1232_2 := h1232c.2.2.1
                                    have p1232_3 := h1232c.2.2.2
                                    linarith only [h1203, hlam, p1232_0]
                                  · have p1232_0 := h1232c.1
                                    have p1232_1 := h1232c.2.1
                                    have p1232_2 := h1232c.2.2.1
                                    have p1232_3 := h1232c.2.2.2
                                    linarith only [h1, h1196, h1197, h1220, h1222, h1226, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1232_1]
                                  · have p1232_0 := h1232c.1
                                    have p1232_1 := h1232c.2.1
                                    have p1232_2 := h1232c.2.2.1
                                    have p1232_3 := h1232c.2.2.2
                                    linarith only [hlam, p1232_0]
                            · linarith only [h0, h1, h1220, h1227, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h0, h1, h1220, h1222, h1226, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1, h1201, h1222, h1223, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h1, h1200, h1220, h1222, hc12, hc23, hlam, hphi]
              · linarith only [h1, h1197, h1203, hlam]
            · linarith only [h0, h1, h1202, hc12, hlam, hphi, ht23, ht34, u4elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1268 | h1268
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1269 | h1269
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1270 | h1270
                · linarith only [h1200, h1201, h1270, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1272 | h1272
                  · linarith only [h0, h1198, h1272, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1274 | h1274
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1275 | h1275
                      · linarith only [h0, h1201, h1275, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1277 | h1277
                        · linarith only [h1196, h1270, h1277, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1279 | h1279
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1280 | h1280
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1281 | h1281
                              · linarith only [h1270, h1281, hc04, hlam, hphi, u4elo2]
                              · linarith only [h1200, h1201, h1279, h1281, hc34, hlam, hphi, u4elo4]
                            · linarith only [h1, h1197, h1269, h1272, h1274, h1275, h1279, h1280, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h1, h1197, h1272, h1274, h1275, h1279, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h1, h1200, h1272, h1274, hc12, hc23, hlam, hphi]
              · linarith only [h1, h1197, h1269, hlam]
            · linarith only [h1, h1196, h1268, hc14, hlam, hphi, u4elo3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1289 | h1289
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1290 | h1290
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1291 | h1291
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1292 | h1292
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1293 | h1293
                  · linarith only [h0, h1200, h1293, hc23, hlam, hphi, ht34, u4elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1295 | h1295
                    · linarith only [h0, h1200, h1295, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1297 | h1297
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1298 | h1298
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1299 | h1299
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1300 | h1300
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1301 | h1301
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1302 | h1302
                                · rcases h0bigk with h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c
                                  · have p1303_0 := h1303c.1
                                    have p1303_1 := h1303c.2.1
                                    have p1303_2 := h1303c.2.2.1
                                    have p1303_3 := h1303c.2.2.2
                                    linarith only [hlam, p1303_0]
                                  · have p1303_0 := h1303c.1
                                    have p1303_1 := h1303c.2.1
                                    have p1303_2 := h1303c.2.2.1
                                    have p1303_3 := h1303c.2.2.2
                                    linarith only [h0, h1297, h1300, h1302, hc01, hc45, hlam, hphi, ht0b, ht5b, p1303_1]
                                  · have p1303_0 := h1303c.1
                                    have p1303_1 := h1303c.2.1
                                    have p1303_2 := h1303c.2.2.1
                                    have p1303_3 := h1303c.2.2.2
                                    linarith only [h1, hlam, p1303_0]
                                  · have p1303_0 := h1303c.1
                                    have p1303_1 := h1303c.2.1
                                    have p1303_2 := h1303c.2.2.1
                                    have p1303_3 := h1303c.2.2.2
                                    linarith only [h1, h1293, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1303_1]
                                  · have p1303_0 := h1303c.1
                                    have p1303_1 := h1303c.2.1
                                    have p1303_2 := h1303c.2.2.1
                                    have p1303_3 := h1303c.2.2.2
                                    linarith only [h1, h1293, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1303_1]
                                  · have p1303_0 := h1303c.1
                                    have p1303_1 := h1303c.2.1
                                    have p1303_2 := h1303c.2.2.1
                                    have p1303_3 := h1303c.2.2.2
                                    linarith only [h0, hlam, p1303_0]
                                  · have p1303_0 := h1303c.1
                                    have p1303_1 := h1303c.2.1
                                    have p1303_2 := h1303c.2.2.1
                                    have p1303_3 := h1303c.2.2.2
                                    linarith only [hlam, p1303_0]
                                  · have p1303_0 := h1303c.1
                                    have p1303_1 := h1303c.2.1
                                    have p1303_2 := h1303c.2.2.1
                                    have p1303_3 := h1303c.2.2.2
                                    linarith only [h1198, hlam, p1303_0]
                                  · have p1303_0 := h1303c.1
                                    have p1303_1 := h1303c.2.1
                                    have p1303_2 := h1303c.2.2.1
                                    have p1303_3 := h1303c.2.2.2
                                    linarith only [h1200, hlam, p1303_1]
                                  · have p1303_0 := h1303c.1
                                    have p1303_1 := h1303c.2.1
                                    have p1303_2 := h1303c.2.2.1
                                    have p1303_3 := h1303c.2.2.2
                                    linarith only [h1197, h1200, h1297, h1300, h1302, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1303_1, u4elo2]
                                  · have p1303_0 := h1303c.1
                                    have p1303_1 := h1303c.2.1
                                    have p1303_2 := h1303c.2.2.1
                                    have p1303_3 := h1303c.2.2.2
                                    linarith only [h1, h1293, hc01, hc23, hlam, hphi, ht12, p1303_1]
                                  · have p1303_0 := h1303c.1
                                    have p1303_1 := h1303c.2.1
                                    have p1303_2 := h1303c.2.2.1
                                    have p1303_3 := h1303c.2.2.2
                                    linarith only [h1, h1293, hc02, hc23, hlam, hphi, p1303_1]
                                  · have p1303_0 := h1303c.1
                                    have p1303_1 := h1303c.2.1
                                    have p1303_2 := h1303c.2.2.1
                                    have p1303_3 := h1303c.2.2.2
                                    linarith only [hlam, p1303_0]
                                  · have p1303_0 := h1303c.1
                                    have p1303_1 := h1303c.2.1
                                    have p1303_2 := h1303c.2.2.1
                                    have p1303_3 := h1303c.2.2.2
                                    linarith only [h0, h1, h1200, h1293, h1297, h1300, h1302, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1303_1]
                                  · have p1303_0 := h1303c.1
                                    have p1303_1 := h1303c.2.1
                                    have p1303_2 := h1303c.2.2.1
                                    have p1303_3 := h1303c.2.2.2
                                    rcases p1303_3 (m.d 0 1) (by simp) with h1318 | h1318
                                    · linarith only [h1, h1318, hlam]
                                    · linarith only [h1197, h1318, hlam]
                                  · have p1303_0 := h1303c.1
                                    have p1303_1 := h1303c.2.1
                                    have p1303_2 := h1303c.2.2.1
                                    have p1303_3 := h1303c.2.2.2
                                    linarith only [h1196, hlam, p1303_0]
                                  · have p1303_0 := h1303c.1
                                    have p1303_1 := h1303c.2.1
                                    have p1303_2 := h1303c.2.2.1
                                    have p1303_3 := h1303c.2.2.2
                                    linarith only [h0, h1297, h1300, h1302, hc04, hc45, hlam, hphi, ht0b, ht5b, p1303_1]
                                  · have p1303_0 := h1303c.1
                                    have p1303_1 := h1303c.2.1
                                    have p1303_2 := h1303c.2.2.1
                                    have p1303_3 := h1303c.2.2.2
                                    linarith only [h1290, hlam, p1303_0]
                                  · have p1303_0 := h1303c.1
                                    have p1303_1 := h1303c.2.1
                                    have p1303_2 := h1303c.2.2.1
                                    have p1303_3 := h1303c.2.2.2
                                    linarith only [hlam, p1303_0]
                                  · have p1303_0 := h1303c.1
                                    have p1303_1 := h1303c.2.1
                                    have p1303_2 := h1303c.2.2.1
                                    have p1303_3 := h1303c.2.2.2
                                    linarith only [h1197, h1200, h1297, h1300, h1302, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1303_1, u4elo2]
                                  · have p1303_0 := h1303c.1
                                    have p1303_1 := h1303c.2.1
                                    have p1303_2 := h1303c.2.2.1
                                    have p1303_3 := h1303c.2.2.2
                                    linarith only [h1197, hlam, p1303_0]
                                  · have p1303_0 := h1303c.1
                                    have p1303_1 := h1303c.2.1
                                    have p1303_2 := h1303c.2.2.1
                                    have p1303_3 := h1303c.2.2.2
                                    linarith only [h1289, hlam, p1303_1]
                                  · have p1303_0 := h1303c.1
                                    have p1303_1 := h1303c.2.1
                                    have p1303_2 := h1303c.2.2.1
                                    have p1303_3 := h1303c.2.2.2
                                    linarith only [h1291, hlam, p1303_0]
                                  · have p1303_0 := h1303c.1
                                    have p1303_1 := h1303c.2.1
                                    have p1303_2 := h1303c.2.2.1
                                    have p1303_3 := h1303c.2.2.2
                                    linarith only [h1292, hlam, p1303_1]
                                  · have p1303_0 := h1303c.1
                                    have p1303_1 := h1303c.2.1
                                    have p1303_2 := h1303c.2.2.1
                                    have p1303_3 := h1303c.2.2.2
                                    linarith only [hlam, p1303_0]
                                · linarith only [h1292, h1302, hc34, hlam, hphi, u4elo0]
                              · linarith only [h1200, h1301, hc02, hlam, hphi, ht23, ht34, u4elo4]
                            · linarith only [h1, h1196, h1293, h1298, h1300, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h1, h1196, h1293, h1295, h1297, h1299, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h1, h1196, h1292, h1295, h1297, h1298, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h0, h1, h1289, h1293, h1297, hc12, hc23, hlam, hphi]
                · linarith only [h1200, h1289, h1292, hlam]
              · linarith only [h0, h1, h1289, h1291, hlam]
            · linarith only [h0, h1, h1290, hc12, hlam, hphi, ht23, ht34, u4elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1340 | h1340
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1341 | h1341
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1342 | h1342
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1343 | h1343
                  · linarith only [h0, h1200, h1343, hc23, hlam, hphi, ht34, u4elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1345 | h1345
                    · linarith only [h0, h1200, h1345, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1347 | h1347
                      · linarith only [h0, h1289, h1347, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1349 | h1349
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1350 | h1350
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1351 | h1351
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1352 | h1352
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1353 | h1353
                                · rcases h0bigk with h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c | h1354c
                                  · have p1354_0 := h1354c.1
                                    have p1354_1 := h1354c.2.1
                                    have p1354_2 := h1354c.2.2.1
                                    have p1354_3 := h1354c.2.2.2
                                    linarith only [hlam, p1354_0]
                                  · have p1354_0 := h1354c.1
                                    have p1354_1 := h1354c.2.1
                                    have p1354_2 := h1354c.2.2.1
                                    have p1354_3 := h1354c.2.2.2
                                    linarith only [h0, h1, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1354_1]
                                  · have p1354_0 := h1354c.1
                                    have p1354_1 := h1354c.2.1
                                    have p1354_2 := h1354c.2.2.1
                                    have p1354_3 := h1354c.2.2.2
                                    linarith only [h1, hlam, p1354_0]
                                  · have p1354_0 := h1354c.1
                                    have p1354_1 := h1354c.2.1
                                    have p1354_2 := h1354c.2.2.1
                                    have p1354_3 := h1354c.2.2.2
                                    linarith only [h1, h1343, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1354_1]
                                  · have p1354_0 := h1354c.1
                                    have p1354_1 := h1354c.2.1
                                    have p1354_2 := h1354c.2.2.1
                                    have p1354_3 := h1354c.2.2.2
                                    linarith only [h1, h1343, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1354_1]
                                  · have p1354_0 := h1354c.1
                                    have p1354_1 := h1354c.2.1
                                    have p1354_2 := h1354c.2.2.1
                                    have p1354_3 := h1354c.2.2.2
                                    linarith only [h0, hlam, p1354_0]
                                  · have p1354_0 := h1354c.1
                                    have p1354_1 := h1354c.2.1
                                    have p1354_2 := h1354c.2.2.1
                                    have p1354_3 := h1354c.2.2.2
                                    linarith only [hlam, p1354_0]
                                  · have p1354_0 := h1354c.1
                                    have p1354_1 := h1354c.2.1
                                    have p1354_2 := h1354c.2.2.1
                                    have p1354_3 := h1354c.2.2.2
                                    linarith only [h1198, hlam, p1354_0]
                                  · have p1354_0 := h1354c.1
                                    have p1354_1 := h1354c.2.1
                                    have p1354_2 := h1354c.2.2.1
                                    have p1354_3 := h1354c.2.2.2
                                    linarith only [h1200, hlam, p1354_1]
                                  · have p1354_0 := h1354c.1
                                    have p1354_1 := h1354c.2.1
                                    have p1354_2 := h1354c.2.2.1
                                    have p1354_3 := h1354c.2.2.2
                                    linarith only [h1289, hlam, p1354_0]
                                  · have p1354_0 := h1354c.1
                                    have p1354_1 := h1354c.2.1
                                    have p1354_2 := h1354c.2.2.1
                                    have p1354_3 := h1354c.2.2.2
                                    linarith only [h1196, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b, p1354_1]
                                  · have p1354_0 := h1354c.1
                                    have p1354_1 := h1354c.2.1
                                    have p1354_2 := h1354c.2.2.1
                                    have p1354_3 := h1354c.2.2.2
                                    linarith only [h0, h1, h1343, hc12, hc23, hlam, hphi, p1354_1]
                                  · have p1354_0 := h1354c.1
                                    have p1354_1 := h1354c.2.1
                                    have p1354_2 := h1354c.2.2.1
                                    have p1354_3 := h1354c.2.2.2
                                    linarith only [hlam, p1354_0]
                                  · have p1354_0 := h1354c.1
                                    have p1354_1 := h1354c.2.1
                                    have p1354_2 := h1354c.2.2.1
                                    have p1354_3 := h1354c.2.2.2
                                    linarith only [h1, h1196, h1343, h1349, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1354_1]
                                  · have p1354_0 := h1354c.1
                                    have p1354_1 := h1354c.2.1
                                    have p1354_2 := h1354c.2.2.1
                                    have p1354_3 := h1354c.2.2.2
                                    linarith only [h1, h1197, h1343, h1347, hc12, hc23, hlam, hphi, p1354_1]
                                  · have p1354_0 := h1354c.1
                                    have p1354_1 := h1354c.2.1
                                    have p1354_2 := h1354c.2.2.1
                                    have p1354_3 := h1354c.2.2.2
                                    linarith only [h1196, hlam, p1354_0]
                                  · have p1354_0 := h1354c.1
                                    have p1354_1 := h1354c.2.1
                                    have p1354_2 := h1354c.2.2.1
                                    have p1354_3 := h1354c.2.2.2
                                    linarith only [h0, hc12, hlam, hphi, ht23, ht34, p1354_1, u4elo0]
                                  · have p1354_0 := h1354c.1
                                    have p1354_1 := h1354c.2.1
                                    have p1354_2 := h1354c.2.2.1
                                    have p1354_3 := h1354c.2.2.2
                                    linarith only [h1340, hlam, p1354_0]
                                  · have p1354_0 := h1354c.1
                                    have p1354_1 := h1354c.2.1
                                    have p1354_2 := h1354c.2.2.1
                                    have p1354_3 := h1354c.2.2.2
                                    linarith only [hlam, p1354_0]
                                  · have p1354_0 := h1354c.1
                                    have p1354_1 := h1354c.2.1
                                    have p1354_2 := h1354c.2.2.1
                                    have p1354_3 := h1354c.2.2.2
                                    linarith only [h1197, h1200, h1347, hc12, hlam, hphi, ht23, ht34, p1354_1, u4elo2]
                                  · have p1354_0 := h1354c.1
                                    have p1354_1 := h1354c.2.1
                                    have p1354_2 := h1354c.2.2.1
                                    have p1354_3 := h1354c.2.2.2
                                    linarith only [h1197, hlam, p1354_0]
                                  · have p1354_0 := h1354c.1
                                    have p1354_1 := h1354c.2.1
                                    have p1354_2 := h1354c.2.2.1
                                    have p1354_3 := h1354c.2.2.2
                                    linarith only [h0, h1, h1197, h1343, hc12, hc23, hlam, hphi, p1354_1]
                                  · have p1354_0 := h1354c.1
                                    have p1354_1 := h1354c.2.1
                                    have p1354_2 := h1354c.2.2.1
                                    have p1354_3 := h1354c.2.2.2
                                    linarith only [h1341, hlam, p1354_0]
                                  · have p1354_0 := h1354c.1
                                    have p1354_1 := h1354c.2.1
                                    have p1354_2 := h1354c.2.2.1
                                    have p1354_3 := h1354c.2.2.2
                                    linarith only [h1342, hlam, p1354_1]
                                  · have p1354_0 := h1354c.1
                                    have p1354_1 := h1354c.2.1
                                    have p1354_2 := h1354c.2.2.1
                                    have p1354_3 := h1354c.2.2.2
                                    linarith only [hlam, p1354_0]
                                · linarith only [h1349, h1353, hc34, hlam, hphi, u4elo1]
                              · linarith only [h1, h1196, h1200, h1343, h1349, h1352, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h1, h1343, h1351, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h1196, h1343, h1349, h1350, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h1200, h1342, h1349, hc14, hlam, hphi, u4elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1385 | h1385
                  · linarith only [h0, h1198, h1385, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1387 | h1387
                    · linarith only [h0, h1200, h1387, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1389 | h1389
                      · linarith only [h0, h1289, h1389, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1391 | h1391
                        · linarith only [h0, h1, h1196, h1200, h1342, h1391, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1393 | h1393
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1394 | h1394
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1395 | h1395
                              · linarith only [h0, h1200, h1342, h1395, hc12, hlam, hphi, ht23, ht34, u4elo2]
                              · linarith only [h0, h1200, h1395, hc12, hlam, hphi, ht23, ht34, u4elo4]
                            · linarith only [h1, h1341, h1342, h1385, h1394, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                          · linarith only [h1, h1197, h1385, h1387, h1391, h1393, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h1197, h1341, hlam]
            · linarith only [h0, h1, h1340, hc12, hlam, hphi, ht23, ht34, u4elo3]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1402 | h1402
      · linarith only [h0, h1, h1402, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1404 | h1404
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1405 | h1405
          · linarith only [h0, h1197, h1405, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1407 | h1407
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1408 | h1408
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1409 | h1409
                · linarith only [h0, h1197, h1404, h1409, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1411 | h1411
                  · linarith only [h0, h1, h1402, h1411, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1413 | h1413
                    · linarith only [h0, h1197, h1409, h1413, hc24, hlam, hphi, u4elo4]
                    · linarith only [h1404, h1405, h1413, hc12, hc25, hlam, hphi]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1416 | h1416
                · linarith only [h1, h1196, h1408, h1416, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1418 | h1418
                  · linarith only [h0, h1, h1408, h1416, h1418, hc23, hlam, hphi, ht34, u4elo4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1420 | h1420
                    · linarith only [h0, h1, h1408, h1416, h1420, hc24, hlam, hphi, u4elo4]
                    · linarith only [h0, h1, h1404, h1408, h1416, h1420, hc12, hlam, hphi, ht23, ht34, u4elo4]
            · linarith only [h1, h1196, h1407, hc14, hlam, hphi, u4elo3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1424 | h1424
          · linarith only [h0, h1197, h1404, h1424, hc12, hlam, hphi, ht23, ht34, u4elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1426 | h1426
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1427 | h1427
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1428 | h1428
                · linarith only [h1196, h1197, h1428, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1430 | h1430
                  · linarith only [h0, h1404, h1428, h1430, hc23, hlam, hphi, ht34, u4elo4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1432 | h1432
                    · linarith only [h0, h1404, h1428, h1432, hc24, hlam, hphi, u4elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1434 | h1434
                      · linarith only [h1196, h1197, h1424, h1432, h1434, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1436 | h1436
                        · linarith only [h1196, h1197, h1428, h1436, hlam]
                        · linarith only [h1196, h1197, h1432, h1436, hc12, hlam, hphi, ht23, ht34, u4elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1439 | h1439
                · linarith only [h1196, h1197, h1439, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1441 | h1441
                  · linarith only [h0, h1, h1402, h1426, h1441, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1443 | h1443
                    · linarith only [h0, h1404, h1439, h1443, hc24, hlam, hphi, u4elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1445 | h1445
                      · linarith only [h1, h1196, h1424, h1427, h1443, h1445, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1447 | h1447
                        · linarith only [h1, h1196, h1427, h1439, h1447, hlam]
                        · linarith only [h1196, h1197, h1443, h1447, hc12, hlam, hphi, ht23, ht34, u4elo4]
            · linarith only [h0, h1, h1426, hc12, hlam, hphi, ht23, ht34, u4elo3]
  · linarith only [h0, h1196, hc12, hlam, hphi, ht23, ht34, u4elo1]

set_option maxHeartbeats 5924000 in
set_option maxHeartbeats 5924000 in
theorem r1l7_20_12_14_H_I_L_I_L_0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_12_14_H_I_L_I_L_0_x0_x0 m hb0 hb2 hb4 h0 h1
  · exact r1l7_20_12_14_H_I_L_I_L_0_x0_x1 m hb0 hb2 hb4 h0 h1

end R2N4
