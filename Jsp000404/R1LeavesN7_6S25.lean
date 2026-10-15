import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9982000 in
set_option maxHeartbeats 9982000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s12_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg10058 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11024 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11558 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h14803 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h10058 := hg10058
  have h11024 := hg11024
  rcases m.htr 0 2 5 (by decide) (by decide) with h14804 | h14804
  · rcases m.htr 0 3 4 (by decide) (by decide) with h14805 | h14805
    · rcases m.htr 0 3 5 (by decide) (by decide) with h14806 | h14806
      · rcases m.htr 0 4 5 (by decide) (by decide) with h14807 | h14807
        · rcases m.htr 1 2 3 (by decide) (by decide) with h14808 | h14808
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14809 | h14809
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14810 | h14810
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14811 | h14811
                · rcases m.htr 1 4 5 (by decide) (by decide) with h14812 | h14812
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14813 | h14813
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h14814 | h14814
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h14815 | h14815
                        · linarith only [h11558, h14803, h14808, h14815, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h11558, h14803, h14807, h14808, h14815, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h11558, h14806, h14814, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h11558, h14805, h14813, hlam]
                  · linarith only [h10058, h14803, h14807, h14812, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h11558, h14803, h14805, h14808, h14811, h6793, hc01, hc12, hlam, hphi]
              · linarith only [h11558, h14808, h14810, hc02, hc25, hlam, hphi]
            · linarith only [h11558, h14803, h14808, h14809, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14824 | h14824
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14825 | h14825
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14826 | h14826
                · rcases m.htr 1 4 5 (by decide) (by decide) with h14827 | h14827
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14828 | h14828
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h14829 | h14829
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h14830 | h14830
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h14831 | h14831
                          · rcases h0bigk with h14832c | h14832c | h14832c | h14832c | h14832c | h14832c | h14832c | h14832c | h14832c | h14832c | h14832c | h14832c | h14832c | h14832c | h14832c | h14832c | h14832c | h14832c | h14832c | h14832c | h14832c | h14832c | h14832c | h14832c | h14832c
                            · have p14832_0 := h14832c.1
                              have p14832_1 := h14832c.2.1
                              have p14832_2 := h14832c.2.2.1
                              have p14832_3 := h14832c.2.2.2
                              linarith only [hlam, p14832_0]
                            · have p14832_0 := h14832c.1
                              have p14832_1 := h14832c.2.1
                              have p14832_2 := h14832c.2.2.1
                              have p14832_3 := h14832c.2.2.2
                              linarith only [h0, hlam, p14832_1]
                            · have p14832_0 := h14832c.1
                              have p14832_1 := h14832c.2.1
                              have p14832_2 := h14832c.2.2.1
                              have p14832_3 := h14832c.2.2.2
                              linarith only [h6793, hlam, p14832_0]
                            · have p14832_0 := h14832c.1
                              have p14832_1 := h14832c.2.1
                              have p14832_2 := h14832c.2.2.1
                              have p14832_3 := h14832c.2.2.2
                              linarith only [h10058, hlam, p14832_1]
                            · have p14832_0 := h14832c.1
                              have p14832_1 := h14832c.2.1
                              have p14832_2 := h14832c.2.2.1
                              have p14832_3 := h14832c.2.2.2
                              linarith only [h11024, hlam, p14832_1]
                            · have p14832_0 := h14832c.1
                              have p14832_1 := h14832c.2.1
                              have p14832_2 := h14832c.2.2.1
                              have p14832_3 := h14832c.2.2.2
                              linarith only [h0, h14808, hc01, hc23, hlam, hphi, ht12, p14832_1]
                            · have p14832_0 := h14832c.1
                              have p14832_1 := h14832c.2.1
                              have p14832_2 := h14832c.2.2.1
                              have p14832_3 := h14832c.2.2.2
                              linarith only [hlam, p14832_0]
                            · have p14832_0 := h14832c.1
                              have p14832_1 := h14832c.2.1
                              have p14832_2 := h14832c.2.2.1
                              have p14832_3 := h14832c.2.2.2
                              linarith only [h11558, hlam, p14832_0]
                            · have p14832_0 := h14832c.1
                              have p14832_1 := h14832c.2.1
                              have p14832_2 := h14832c.2.2.1
                              have p14832_3 := h14832c.2.2.2
                              linarith only [h0, h14803, h14808, h14828, h14831, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14832_1]
                            · have p14832_0 := h14832c.1
                              have p14832_1 := h14832c.2.1
                              have p14832_2 := h14832c.2.2.1
                              have p14832_3 := h14832c.2.2.2
                              linarith only [h0, h11024, h14808, hc01, hc23, hlam, hphi, ht12, p14832_1]
                            · have p14832_0 := h14832c.1
                              have p14832_1 := h14832c.2.1
                              have p14832_2 := h14832c.2.2.1
                              have p14832_3 := h14832c.2.2.2
                              rcases p14832_3 (m.d 0 1) (by simp) with h14843 | h14843
                              · linarith only [h14843, h6793, hlam]
                              · rcases p14832_3 (m.d 0 2) (by simp) with h14845 | h14845
                                · linarith only [h11558, h14845, hlam]
                                · linarith only [h0, h14845, hlam]
                            · have p14832_0 := h14832c.1
                              have p14832_1 := h14832c.2.1
                              have p14832_2 := h14832c.2.2.1
                              have p14832_3 := h14832c.2.2.2
                              linarith only [h14803, h14828, h14831, hc45, hlam, hphi, ht0b, ht5b, p14832_1, u0elo2]
                            · have p14832_0 := h14832c.1
                              have p14832_1 := h14832c.2.1
                              have p14832_2 := h14832c.2.2.1
                              have p14832_3 := h14832c.2.2.2
                              linarith only [hlam, p14832_0]
                            · have p14832_0 := h14832c.1
                              have p14832_1 := h14832c.2.1
                              have p14832_2 := h14832c.2.2.1
                              have p14832_3 := h14832c.2.2.2
                              linarith only [h14803, h14828, h14831, hc45, hlam, hphi, ht0b, ht5b, p14832_1, u0elo2]
                            · have p14832_0 := h14832c.1
                              have p14832_1 := h14832c.2.1
                              have p14832_2 := h14832c.2.2.1
                              have p14832_3 := h14832c.2.2.2
                              rcases p14832_3 (m.d 0 1) (by simp) with h14851 | h14851
                              · linarith only [h14851, h6793, hlam]
                              · rcases p14832_3 (m.d 0 2) (by simp) with h14853 | h14853
                                · linarith only [h11558, h14853, hlam]
                                · linarith only [h14804, h14853, hlam]
                            · have p14832_0 := h14832c.1
                              have p14832_1 := h14832c.2.1
                              have p14832_2 := h14832c.2.2.1
                              have p14832_3 := h14832c.2.2.2
                              linarith only [h0, h14803, h14808, hc01, hc23, hlam, hphi, ht12, p14832_1]
                            · have p14832_0 := h14832c.1
                              have p14832_1 := h14832c.2.1
                              have p14832_2 := h14832c.2.2.1
                              have p14832_3 := h14832c.2.2.2
                              linarith only [h14803, hlam, p14832_0]
                            · have p14832_0 := h14832c.1
                              have p14832_1 := h14832c.2.1
                              have p14832_2 := h14832c.2.2.1
                              have p14832_3 := h14832c.2.2.2
                              linarith only [h14805, hlam, p14832_0]
                            · have p14832_0 := h14832c.1
                              have p14832_1 := h14832c.2.1
                              have p14832_2 := h14832c.2.2.1
                              have p14832_3 := h14832c.2.2.2
                              linarith only [hlam, p14832_0]
                            · have p14832_0 := h14832c.1
                              have p14832_1 := h14832c.2.1
                              have p14832_2 := h14832c.2.2.1
                              have p14832_3 := h14832c.2.2.2
                              linarith only [h0, h11024, h14803, h14808, hc01, hc23, hlam, hphi, ht12, p14832_1]
                            · have p14832_0 := h14832c.1
                              have p14832_1 := h14832c.2.1
                              have p14832_2 := h14832c.2.2.1
                              have p14832_3 := h14832c.2.2.2
                              linarith only [h0, h14804, h14808, hc01, hc23, hlam, hphi, ht12, p14832_1]
                            · have p14832_0 := h14832c.1
                              have p14832_1 := h14832c.2.1
                              have p14832_2 := h14832c.2.2.1
                              have p14832_3 := h14832c.2.2.2
                              linarith only [h14804, hlam, p14832_1]
                            · have p14832_0 := h14832c.1
                              have p14832_1 := h14832c.2.1
                              have p14832_2 := h14832c.2.2.1
                              have p14832_3 := h14832c.2.2.2
                              linarith only [h14806, hlam, p14832_0]
                            · have p14832_0 := h14832c.1
                              have p14832_1 := h14832c.2.1
                              have p14832_2 := h14832c.2.2.1
                              have p14832_3 := h14832c.2.2.2
                              linarith only [h14807, hlam, p14832_1]
                            · have p14832_0 := h14832c.1
                              have p14832_1 := h14832c.2.1
                              have p14832_2 := h14832c.2.2.1
                              have p14832_3 := h14832c.2.2.2
                              linarith only [hlam, p14832_0]
                          · linarith only [h0, h14803, h14808, h14830, h14831, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h14867 | h14867
                          · linarith only [h14805, h14830, h14867, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                          · rcases h0bigk with h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c | h14869c
                            · have p14869_0 := h14869c.1
                              have p14869_1 := h14869c.2.1
                              have p14869_2 := h14869c.2.2.1
                              have p14869_3 := h14869c.2.2.2
                              linarith only [hlam, p14869_0]
                            · have p14869_0 := h14869c.1
                              have p14869_1 := h14869c.2.1
                              have p14869_2 := h14869c.2.2.1
                              have p14869_3 := h14869c.2.2.2
                              linarith only [h0, hlam, p14869_1]
                            · have p14869_0 := h14869c.1
                              have p14869_1 := h14869c.2.1
                              have p14869_2 := h14869c.2.2.1
                              have p14869_3 := h14869c.2.2.2
                              linarith only [h6793, hlam, p14869_0]
                            · have p14869_0 := h14869c.1
                              have p14869_1 := h14869c.2.1
                              have p14869_2 := h14869c.2.2.1
                              have p14869_3 := h14869c.2.2.2
                              linarith only [h10058, hlam, p14869_1]
                            · have p14869_0 := h14869c.1
                              have p14869_1 := h14869c.2.1
                              have p14869_2 := h14869c.2.2.1
                              have p14869_3 := h14869c.2.2.2
                              linarith only [h11024, hlam, p14869_1]
                            · have p14869_0 := h14869c.1
                              have p14869_1 := h14869c.2.1
                              have p14869_2 := h14869c.2.2.1
                              have p14869_3 := h14869c.2.2.2
                              linarith only [h0, h14808, hc01, hc23, hlam, hphi, ht12, p14869_1]
                            · have p14869_0 := h14869c.1
                              have p14869_1 := h14869c.2.1
                              have p14869_2 := h14869c.2.2.1
                              have p14869_3 := h14869c.2.2.2
                              linarith only [hlam, p14869_0]
                            · have p14869_0 := h14869c.1
                              have p14869_1 := h14869c.2.1
                              have p14869_2 := h14869c.2.2.1
                              have p14869_3 := h14869c.2.2.2
                              linarith only [h11558, hlam, p14869_0]
                            · have p14869_0 := h14869c.1
                              have p14869_1 := h14869c.2.1
                              have p14869_2 := h14869c.2.2.1
                              have p14869_3 := h14869c.2.2.2
                              linarith only [h0, h14807, h14808, h14828, h14830, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14869_1]
                            · have p14869_0 := h14869c.1
                              have p14869_1 := h14869c.2.1
                              have p14869_2 := h14869c.2.2.1
                              have p14869_3 := h14869c.2.2.2
                              linarith only [h0, h11024, h14808, hc01, hc23, hlam, hphi, ht12, p14869_1]
                            · have p14869_0 := h14869c.1
                              have p14869_1 := h14869c.2.1
                              have p14869_2 := h14869c.2.2.1
                              have p14869_3 := h14869c.2.2.2
                              rcases p14869_3 (m.d 0 1) (by simp) with h14880 | h14880
                              · linarith only [h14880, h6793, hlam]
                              · rcases p14869_3 (m.d 0 2) (by simp) with h14882 | h14882
                                · linarith only [h11558, h14882, hlam]
                                · linarith only [h0, h14882, hlam]
                            · have p14869_0 := h14869c.1
                              have p14869_1 := h14869c.2.1
                              have p14869_2 := h14869c.2.2.1
                              have p14869_3 := h14869c.2.2.2
                              linarith only [h14803, h14828, hc34, hlam, hphi, ht0b, ht45, ht5b, p14869_1, u0elo2]
                            · have p14869_0 := h14869c.1
                              have p14869_1 := h14869c.2.1
                              have p14869_2 := h14869c.2.2.1
                              have p14869_3 := h14869c.2.2.2
                              linarith only [hlam, p14869_0]
                            · have p14869_0 := h14869c.1
                              have p14869_1 := h14869c.2.1
                              have p14869_2 := h14869c.2.2.1
                              have p14869_3 := h14869c.2.2.2
                              linarith only [h14807, h14828, h14830, hc34, hlam, hphi, ht0b, ht45, ht5b, p14869_1, u0elo2]
                            · have p14869_0 := h14869c.1
                              have p14869_1 := h14869c.2.1
                              have p14869_2 := h14869c.2.2.1
                              have p14869_3 := h14869c.2.2.2
                              linarith only [h14807, h14828, h14830, hc34, hlam, hphi, ht0b, ht45, ht5b, p14869_1, u0elo2]
                            · have p14869_0 := h14869c.1
                              have p14869_1 := h14869c.2.1
                              have p14869_2 := h14869c.2.2.1
                              have p14869_3 := h14869c.2.2.2
                              linarith only [h0, h14803, h14808, hc01, hc23, hlam, hphi, ht12, p14869_1]
                            · have p14869_0 := h14869c.1
                              have p14869_1 := h14869c.2.1
                              have p14869_2 := h14869c.2.2.1
                              have p14869_3 := h14869c.2.2.2
                              linarith only [h14803, hlam, p14869_0]
                            · have p14869_0 := h14869c.1
                              have p14869_1 := h14869c.2.1
                              have p14869_2 := h14869c.2.2.1
                              have p14869_3 := h14869c.2.2.2
                              linarith only [h14805, hlam, p14869_0]
                            · have p14869_0 := h14869c.1
                              have p14869_1 := h14869c.2.1
                              have p14869_2 := h14869c.2.2.1
                              have p14869_3 := h14869c.2.2.2
                              linarith only [hlam, p14869_0]
                            · have p14869_0 := h14869c.1
                              have p14869_1 := h14869c.2.1
                              have p14869_2 := h14869c.2.2.1
                              have p14869_3 := h14869c.2.2.2
                              linarith only [h0, h11024, h14803, h14808, hc01, hc23, hlam, hphi, ht12, p14869_1]
                            · have p14869_0 := h14869c.1
                              have p14869_1 := h14869c.2.1
                              have p14869_2 := h14869c.2.2.1
                              have p14869_3 := h14869c.2.2.2
                              linarith only [h0, h14804, h14808, hc01, hc23, hlam, hphi, ht12, p14869_1]
                            · have p14869_0 := h14869c.1
                              have p14869_1 := h14869c.2.1
                              have p14869_2 := h14869c.2.2.1
                              have p14869_3 := h14869c.2.2.2
                              linarith only [h14804, hlam, p14869_1]
                            · have p14869_0 := h14869c.1
                              have p14869_1 := h14869c.2.1
                              have p14869_2 := h14869c.2.2.1
                              have p14869_3 := h14869c.2.2.2
                              linarith only [h14806, hlam, p14869_0]
                            · have p14869_0 := h14869c.1
                              have p14869_1 := h14869c.2.1
                              have p14869_2 := h14869c.2.2.1
                              have p14869_3 := h14869c.2.2.2
                              linarith only [h14807, hlam, p14869_1]
                            · have p14869_0 := h14869c.1
                              have p14869_1 := h14869c.2.1
                              have p14869_2 := h14869c.2.2.1
                              have p14869_3 := h14869c.2.2.2
                              linarith only [hlam, p14869_0]
                      · linarith only [h0, h14808, h14829, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h14805, h14808, h14828, h6793, hlam]
                  · linarith only [h0, h10058, h14803, h14807, h14808, h14827, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h14805, h14826, h6793, hlam]
              · linarith only [h0, h14804, h14825, hlam]
            · linarith only [h0, h14803, h14824, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h14905 | h14905
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14906 | h14906
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14907 | h14907
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14908 | h14908
                · rcases m.htr 1 4 5 (by decide) (by decide) with h14909 | h14909
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14910 | h14910
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h14911 | h14911
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h14912 | h14912
                        · linarith only [h14803, h14807, h14912, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h14914 | h14914
                          · linarith only [h10058, h11558, h14804, h14807, h14905, h14910, h14912, h14914, hc01, hc12, hlam, hphi]
                          · rcases h0bigk with h14916c | h14916c | h14916c | h14916c | h14916c | h14916c | h14916c | h14916c | h14916c | h14916c | h14916c | h14916c | h14916c | h14916c | h14916c | h14916c | h14916c | h14916c | h14916c | h14916c | h14916c | h14916c | h14916c | h14916c | h14916c
                            · have p14916_0 := h14916c.1
                              have p14916_1 := h14916c.2.1
                              have p14916_2 := h14916c.2.2.1
                              have p14916_3 := h14916c.2.2.2
                              linarith only [hlam, p14916_0]
                            · have p14916_0 := h14916c.1
                              have p14916_1 := h14916c.2.1
                              have p14916_2 := h14916c.2.2.1
                              have p14916_3 := h14916c.2.2.2
                              linarith only [h0, hlam, p14916_1]
                            · have p14916_0 := h14916c.1
                              have p14916_1 := h14916c.2.1
                              have p14916_2 := h14916c.2.2.1
                              have p14916_3 := h14916c.2.2.2
                              linarith only [h6793, hlam, p14916_0]
                            · have p14916_0 := h14916c.1
                              have p14916_1 := h14916c.2.1
                              have p14916_2 := h14916c.2.2.1
                              have p14916_3 := h14916c.2.2.2
                              linarith only [h10058, hlam, p14916_1]
                            · have p14916_0 := h14916c.1
                              have p14916_1 := h14916c.2.1
                              have p14916_2 := h14916c.2.2.1
                              have p14916_3 := h14916c.2.2.2
                              linarith only [h11024, hlam, p14916_1]
                            · have p14916_0 := h14916c.1
                              have p14916_1 := h14916c.2.1
                              have p14916_2 := h14916c.2.2.1
                              have p14916_3 := h14916c.2.2.2
                              linarith only [h11558, h14905, hc01, hc12, hlam, hphi, p14916_1]
                            · have p14916_0 := h14916c.1
                              have p14916_1 := h14916c.2.1
                              have p14916_2 := h14916c.2.2.1
                              have p14916_3 := h14916c.2.2.2
                              linarith only [hlam, p14916_0]
                            · have p14916_0 := h14916c.1
                              have p14916_1 := h14916c.2.1
                              have p14916_2 := h14916c.2.2.1
                              have p14916_3 := h14916c.2.2.2
                              linarith only [h11558, hlam, p14916_0]
                            · have p14916_0 := h14916c.1
                              have p14916_1 := h14916c.2.1
                              have p14916_2 := h14916c.2.2.1
                              have p14916_3 := h14916c.2.2.2
                              linarith only [h10058, h11558, h14905, hc01, hc12, hlam, hphi, p14916_1]
                            · have p14916_0 := h14916c.1
                              have p14916_1 := h14916c.2.1
                              have p14916_2 := h14916c.2.2.1
                              have p14916_3 := h14916c.2.2.2
                              linarith only [h11558, h14905, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p14916_1]
                            · have p14916_0 := h14916c.1
                              have p14916_1 := h14916c.2.1
                              have p14916_2 := h14916c.2.2.1
                              have p14916_3 := h14916c.2.2.2
                              linarith only [h11558, h14905, hc01, hc12, hlam, hphi, p14916_1]
                            · have p14916_0 := h14916c.1
                              have p14916_1 := h14916c.2.1
                              have p14916_2 := h14916c.2.2.1
                              have p14916_3 := h14916c.2.2.2
                              linarith only [h11558, h14804, h14905, h14912, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p14916_1]
                            · have p14916_0 := h14916c.1
                              have p14916_1 := h14916c.2.1
                              have p14916_2 := h14916c.2.2.1
                              have p14916_3 := h14916c.2.2.2
                              linarith only [hlam, p14916_0]
                            · have p14916_0 := h14916c.1
                              have p14916_1 := h14916c.2.1
                              have p14916_2 := h14916c.2.2.1
                              have p14916_3 := h14916c.2.2.2
                              linarith only [h10058, h11558, h14905, hc01, hc12, hlam, hphi, p14916_1]
                            · have p14916_0 := h14916c.1
                              have p14916_1 := h14916c.2.1
                              have p14916_2 := h14916c.2.2.1
                              have p14916_3 := h14916c.2.2.2
                              linarith only [h11024, h11558, h14905, hc01, hc12, hlam, hphi, p14916_1]
                            · have p14916_0 := h14916c.1
                              have p14916_1 := h14916c.2.1
                              have p14916_2 := h14916c.2.2.1
                              have p14916_3 := h14916c.2.2.2
                              linarith only [h14807, h14908, h14909, hc01, hc13, hlam, hphi, p14916_1]
                            · have p14916_0 := h14916c.1
                              have p14916_1 := h14916c.2.1
                              have p14916_2 := h14916c.2.2.1
                              have p14916_3 := h14916c.2.2.2
                              linarith only [h14803, hlam, p14916_0]
                            · have p14916_0 := h14916c.1
                              have p14916_1 := h14916c.2.1
                              have p14916_2 := h14916c.2.2.1
                              have p14916_3 := h14916c.2.2.2
                              linarith only [h14805, hlam, p14916_0]
                            · have p14916_0 := h14916c.1
                              have p14916_1 := h14916c.2.1
                              have p14916_2 := h14916c.2.2.1
                              have p14916_3 := h14916c.2.2.2
                              linarith only [hlam, p14916_0]
                            · have p14916_0 := h14916c.1
                              have p14916_1 := h14916c.2.1
                              have p14916_2 := h14916c.2.2.1
                              have p14916_3 := h14916c.2.2.2
                              linarith only [h14807, hlam, p14916_0]
                            · have p14916_0 := h14916c.1
                              have p14916_1 := h14916c.2.1
                              have p14916_2 := h14916c.2.2.1
                              have p14916_3 := h14916c.2.2.2
                              linarith only [h11558, h14804, h14905, hc01, hc12, hlam, hphi, p14916_1]
                            · have p14916_0 := h14916c.1
                              have p14916_1 := h14916c.2.1
                              have p14916_2 := h14916c.2.2.1
                              have p14916_3 := h14916c.2.2.2
                              linarith only [h14804, hlam, p14916_1]
                            · have p14916_0 := h14916c.1
                              have p14916_1 := h14916c.2.1
                              have p14916_2 := h14916c.2.2.1
                              have p14916_3 := h14916c.2.2.2
                              linarith only [h14806, hlam, p14916_0]
                            · have p14916_0 := h14916c.1
                              have p14916_1 := h14916c.2.1
                              have p14916_2 := h14916c.2.2.1
                              have p14916_3 := h14916c.2.2.2
                              linarith only [h11558, h14804, h14905, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p14916_1]
                            · have p14916_0 := h14916c.1
                              have p14916_1 := h14916c.2.1
                              have p14916_2 := h14916c.2.2.1
                              have p14916_3 := h14916c.2.2.2
                              linarith only [hlam, p14916_0]
                      · linarith only [h11558, h14806, h14911, hlam]
                    · linarith only [h11558, h14805, h14910, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14944 | h14944
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h14945 | h14945
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h14946 | h14946
                        · linarith only [h14803, h14909, h14946, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h14948 | h14948
                          · linarith only [h10058, h11558, h14804, h14905, h14909, h14944, h14946, h14948, hc01, hc12, hlam, hphi]
                          · rcases h0bigk with h14950c | h14950c | h14950c | h14950c | h14950c | h14950c | h14950c | h14950c | h14950c | h14950c | h14950c | h14950c | h14950c | h14950c | h14950c | h14950c | h14950c | h14950c | h14950c | h14950c | h14950c | h14950c | h14950c | h14950c | h14950c
                            · have p14950_0 := h14950c.1
                              have p14950_1 := h14950c.2.1
                              have p14950_2 := h14950c.2.2.1
                              have p14950_3 := h14950c.2.2.2
                              linarith only [hlam, p14950_0]
                            · have p14950_0 := h14950c.1
                              have p14950_1 := h14950c.2.1
                              have p14950_2 := h14950c.2.2.1
                              have p14950_3 := h14950c.2.2.2
                              linarith only [h0, hlam, p14950_1]
                            · have p14950_0 := h14950c.1
                              have p14950_1 := h14950c.2.1
                              have p14950_2 := h14950c.2.2.1
                              have p14950_3 := h14950c.2.2.2
                              linarith only [h6793, hlam, p14950_0]
                            · have p14950_0 := h14950c.1
                              have p14950_1 := h14950c.2.1
                              have p14950_2 := h14950c.2.2.1
                              have p14950_3 := h14950c.2.2.2
                              linarith only [h10058, hlam, p14950_1]
                            · have p14950_0 := h14950c.1
                              have p14950_1 := h14950c.2.1
                              have p14950_2 := h14950c.2.2.1
                              have p14950_3 := h14950c.2.2.2
                              linarith only [h11024, hlam, p14950_1]
                            · have p14950_0 := h14950c.1
                              have p14950_1 := h14950c.2.1
                              have p14950_2 := h14950c.2.2.1
                              have p14950_3 := h14950c.2.2.2
                              linarith only [h11558, h14905, hc01, hc12, hlam, hphi, p14950_1]
                            · have p14950_0 := h14950c.1
                              have p14950_1 := h14950c.2.1
                              have p14950_2 := h14950c.2.2.1
                              have p14950_3 := h14950c.2.2.2
                              linarith only [hlam, p14950_0]
                            · have p14950_0 := h14950c.1
                              have p14950_1 := h14950c.2.1
                              have p14950_2 := h14950c.2.2.1
                              have p14950_3 := h14950c.2.2.2
                              linarith only [h11558, hlam, p14950_0]
                            · have p14950_0 := h14950c.1
                              have p14950_1 := h14950c.2.1
                              have p14950_2 := h14950c.2.2.1
                              have p14950_3 := h14950c.2.2.2
                              linarith only [h10058, h11558, h14905, hc01, hc12, hlam, hphi, p14950_1]
                            · have p14950_0 := h14950c.1
                              have p14950_1 := h14950c.2.1
                              have p14950_2 := h14950c.2.2.1
                              have p14950_3 := h14950c.2.2.2
                              linarith only [h11558, h14905, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p14950_1]
                            · have p14950_0 := h14950c.1
                              have p14950_1 := h14950c.2.1
                              have p14950_2 := h14950c.2.2.1
                              have p14950_3 := h14950c.2.2.2
                              linarith only [h11558, h14905, hc01, hc12, hlam, hphi, p14950_1]
                            · have p14950_0 := h14950c.1
                              have p14950_1 := h14950c.2.1
                              have p14950_2 := h14950c.2.2.1
                              have p14950_3 := h14950c.2.2.2
                              linarith only [h11558, h14804, h14905, h14946, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p14950_1]
                            · have p14950_0 := h14950c.1
                              have p14950_1 := h14950c.2.1
                              have p14950_2 := h14950c.2.2.1
                              have p14950_3 := h14950c.2.2.2
                              linarith only [hlam, p14950_0]
                            · have p14950_0 := h14950c.1
                              have p14950_1 := h14950c.2.1
                              have p14950_2 := h14950c.2.2.1
                              have p14950_3 := h14950c.2.2.2
                              linarith only [h10058, h11558, h14905, hc01, hc12, hlam, hphi, p14950_1]
                            · have p14950_0 := h14950c.1
                              have p14950_1 := h14950c.2.1
                              have p14950_2 := h14950c.2.2.1
                              have p14950_3 := h14950c.2.2.2
                              linarith only [h11024, h11558, h14905, hc01, hc12, hlam, hphi, p14950_1]
                            · have p14950_0 := h14950c.1
                              have p14950_1 := h14950c.2.1
                              have p14950_2 := h14950c.2.2.1
                              have p14950_3 := h14950c.2.2.2
                              linarith only [h10058, h14909, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p14950_1]
                            · have p14950_0 := h14950c.1
                              have p14950_1 := h14950c.2.1
                              have p14950_2 := h14950c.2.2.1
                              have p14950_3 := h14950c.2.2.2
                              linarith only [h14803, hlam, p14950_0]
                            · have p14950_0 := h14950c.1
                              have p14950_1 := h14950c.2.1
                              have p14950_2 := h14950c.2.2.1
                              have p14950_3 := h14950c.2.2.2
                              linarith only [h14805, hlam, p14950_0]
                            · have p14950_0 := h14950c.1
                              have p14950_1 := h14950c.2.1
                              have p14950_2 := h14950c.2.2.1
                              have p14950_3 := h14950c.2.2.2
                              linarith only [hlam, p14950_0]
                            · have p14950_0 := h14950c.1
                              have p14950_1 := h14950c.2.1
                              have p14950_2 := h14950c.2.2.1
                              have p14950_3 := h14950c.2.2.2
                              linarith only [h14807, hlam, p14950_0]
                            · have p14950_0 := h14950c.1
                              have p14950_1 := h14950c.2.1
                              have p14950_2 := h14950c.2.2.1
                              have p14950_3 := h14950c.2.2.2
                              linarith only [h11558, h14804, h14905, hc01, hc12, hlam, hphi, p14950_1]
                            · have p14950_0 := h14950c.1
                              have p14950_1 := h14950c.2.1
                              have p14950_2 := h14950c.2.2.1
                              have p14950_3 := h14950c.2.2.2
                              linarith only [h14804, hlam, p14950_1]
                            · have p14950_0 := h14950c.1
                              have p14950_1 := h14950c.2.1
                              have p14950_2 := h14950c.2.2.1
                              have p14950_3 := h14950c.2.2.2
                              linarith only [h14806, hlam, p14950_0]
                            · have p14950_0 := h14950c.1
                              have p14950_1 := h14950c.2.1
                              have p14950_2 := h14950c.2.2.1
                              have p14950_3 := h14950c.2.2.2
                              linarith only [h11558, h14804, h14905, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p14950_1]
                            · have p14950_0 := h14950c.1
                              have p14950_1 := h14950c.2.1
                              have p14950_2 := h14950c.2.2.1
                              have p14950_3 := h14950c.2.2.2
                              linarith only [hlam, p14950_0]
                      · linarith only [h11558, h14806, h14945, hlam]
                    · linarith only [h11558, h14805, h14944, hlam]
                · linarith only [h11558, h14803, h14805, h14908, h6793, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h11558, h14905, h14907, hc02, hc25, hlam, hphi]
            · linarith only [h11558, h14803, h14905, h14906, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14981 | h14981
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14982 | h14982
              · rcases m.htr 1 3 4 (by decide) (by decide) with h14983 | h14983
                · rcases m.htr 1 4 5 (by decide) (by decide) with h14984 | h14984
                  · linarith only [h10058, h14807, h14905, h14981, h14984, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14986 | h14986
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h14987 | h14987
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h14988 | h14988
                        · linarith only [h14803, h14984, h14988, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h14990 | h14990
                          · linarith only [h10058, h14804, h14984, h14986, h14988, h14990, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                          · rcases h0bigk with h14992c | h14992c | h14992c | h14992c | h14992c | h14992c | h14992c | h14992c | h14992c | h14992c | h14992c | h14992c | h14992c | h14992c | h14992c | h14992c | h14992c | h14992c | h14992c | h14992c | h14992c | h14992c | h14992c | h14992c | h14992c
                            · have p14992_0 := h14992c.1
                              have p14992_1 := h14992c.2.1
                              have p14992_2 := h14992c.2.2.1
                              have p14992_3 := h14992c.2.2.2
                              linarith only [hlam, p14992_0]
                            · have p14992_0 := h14992c.1
                              have p14992_1 := h14992c.2.1
                              have p14992_2 := h14992c.2.2.1
                              have p14992_3 := h14992c.2.2.2
                              linarith only [h0, hlam, p14992_1]
                            · have p14992_0 := h14992c.1
                              have p14992_1 := h14992c.2.1
                              have p14992_2 := h14992c.2.2.1
                              have p14992_3 := h14992c.2.2.2
                              linarith only [h6793, hlam, p14992_0]
                            · have p14992_0 := h14992c.1
                              have p14992_1 := h14992c.2.1
                              have p14992_2 := h14992c.2.2.1
                              have p14992_3 := h14992c.2.2.2
                              linarith only [h10058, hlam, p14992_1]
                            · have p14992_0 := h14992c.1
                              have p14992_1 := h14992c.2.1
                              have p14992_2 := h14992c.2.2.1
                              have p14992_3 := h14992c.2.2.2
                              linarith only [h11024, hlam, p14992_1]
                            · have p14992_0 := h14992c.1
                              have p14992_1 := h14992c.2.1
                              have p14992_2 := h14992c.2.2.1
                              have p14992_3 := h14992c.2.2.2
                              linarith only [h0, h14905, hc01, hc23, hlam, hphi, ht12, p14992_1]
                            · have p14992_0 := h14992c.1
                              have p14992_1 := h14992c.2.1
                              have p14992_2 := h14992c.2.2.1
                              have p14992_3 := h14992c.2.2.2
                              linarith only [hlam, p14992_0]
                            · have p14992_0 := h14992c.1
                              have p14992_1 := h14992c.2.1
                              have p14992_2 := h14992c.2.2.1
                              have p14992_3 := h14992c.2.2.2
                              linarith only [h11558, hlam, p14992_0]
                            · have p14992_0 := h14992c.1
                              have p14992_1 := h14992c.2.1
                              have p14992_2 := h14992c.2.2.1
                              have p14992_3 := h14992c.2.2.2
                              linarith only [h0, h10058, h14905, hc01, hc23, hlam, hphi, ht12, p14992_1]
                            · have p14992_0 := h14992c.1
                              have p14992_1 := h14992c.2.1
                              have p14992_2 := h14992c.2.2.1
                              have p14992_3 := h14992c.2.2.2
                              linarith only [h0, h11024, h14905, hc01, hc23, hlam, hphi, ht12, p14992_1]
                            · have p14992_0 := h14992c.1
                              have p14992_1 := h14992c.2.1
                              have p14992_2 := h14992c.2.2.1
                              have p14992_3 := h14992c.2.2.2
                              rcases p14992_3 (m.d 0 1) (by simp) with h15003 | h15003
                              · linarith only [h15003, h6793, hlam]
                              · rcases p14992_3 (m.d 0 2) (by simp) with h15005 | h15005
                                · linarith only [h11558, h15005, hlam]
                                · linarith only [h0, h15005, hlam]
                            · have p14992_0 := h14992c.1
                              have p14992_1 := h14992c.2.1
                              have p14992_2 := h14992c.2.2.1
                              have p14992_3 := h14992c.2.2.2
                              linarith only [h14804, h14988, hc24, hlam, hphi, ht0b, ht45, ht5b, p14992_1, u0elo2]
                            · have p14992_0 := h14992c.1
                              have p14992_1 := h14992c.2.1
                              have p14992_2 := h14992c.2.2.1
                              have p14992_3 := h14992c.2.2.2
                              linarith only [hlam, p14992_0]
                            · have p14992_0 := h14992c.1
                              have p14992_1 := h14992c.2.1
                              have p14992_2 := h14992c.2.2.1
                              have p14992_3 := h14992c.2.2.2
                              rcases p14992_3 (m.d 0 1) (by simp) with h15010 | h15010
                              · linarith only [h15010, h6793, hlam]
                              · rcases p14992_3 (m.d 0 2) (by simp) with h15012 | h15012
                                · linarith only [h11558, h15012, hlam]
                                · linarith only [h14803, h15012, hlam]
                            · have p14992_0 := h14992c.1
                              have p14992_1 := h14992c.2.1
                              have p14992_2 := h14992c.2.2.1
                              have p14992_3 := h14992c.2.2.2
                              rcases p14992_3 (m.d 0 1) (by simp) with h15015 | h15015
                              · linarith only [h15015, h6793, hlam]
                              · rcases p14992_3 (m.d 0 2) (by simp) with h15017 | h15017
                                · linarith only [h11558, h15017, hlam]
                                · linarith only [h14804, h15017, hlam]
                            · have p14992_0 := h14992c.1
                              have p14992_1 := h14992c.2.1
                              have p14992_2 := h14992c.2.2.1
                              have p14992_3 := h14992c.2.2.2
                              linarith only [h10058, h14984, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p14992_1]
                            · have p14992_0 := h14992c.1
                              have p14992_1 := h14992c.2.1
                              have p14992_2 := h14992c.2.2.1
                              have p14992_3 := h14992c.2.2.2
                              linarith only [h14803, hlam, p14992_0]
                            · have p14992_0 := h14992c.1
                              have p14992_1 := h14992c.2.1
                              have p14992_2 := h14992c.2.2.1
                              have p14992_3 := h14992c.2.2.2
                              linarith only [h14805, hlam, p14992_0]
                            · have p14992_0 := h14992c.1
                              have p14992_1 := h14992c.2.1
                              have p14992_2 := h14992c.2.2.1
                              have p14992_3 := h14992c.2.2.2
                              linarith only [hlam, p14992_0]
                            · have p14992_0 := h14992c.1
                              have p14992_1 := h14992c.2.1
                              have p14992_2 := h14992c.2.2.1
                              have p14992_3 := h14992c.2.2.2
                              linarith only [h14807, hlam, p14992_0]
                            · have p14992_0 := h14992c.1
                              have p14992_1 := h14992c.2.1
                              have p14992_2 := h14992c.2.2.1
                              have p14992_3 := h14992c.2.2.2
                              linarith only [h11558, h14804, hc01, hc23, hlam, hphi, ht12, p14992_1]
                            · have p14992_0 := h14992c.1
                              have p14992_1 := h14992c.2.1
                              have p14992_2 := h14992c.2.2.1
                              have p14992_3 := h14992c.2.2.2
                              linarith only [h14804, hlam, p14992_1]
                            · have p14992_0 := h14992c.1
                              have p14992_1 := h14992c.2.1
                              have p14992_2 := h14992c.2.2.1
                              have p14992_3 := h14992c.2.2.2
                              linarith only [h14806, hlam, p14992_0]
                            · have p14992_0 := h14992c.1
                              have p14992_1 := h14992c.2.1
                              have p14992_2 := h14992c.2.2.1
                              have p14992_3 := h14992c.2.2.2
                              linarith only [h10058, h11558, h14804, hc01, hc23, hlam, hphi, ht12, p14992_1]
                            · have p14992_0 := h14992c.1
                              have p14992_1 := h14992c.2.1
                              have p14992_2 := h14992c.2.2.1
                              have p14992_3 := h14992c.2.2.2
                              linarith only [hlam, p14992_0]
                      · linarith only [h0, h14905, h14987, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h14805, h14905, h14986, h6793, hlam]
                · linarith only [h11558, h14803, h14805, h14983, h6793, hlam]
              · linarith only [h10058, h14804, h14981, h14982, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h14803, h14981, hlam]
      · linarith only [h11558, h14804, h14806, hlam]
    · linarith only [h11558, h14803, h14805, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h15037 | h15037
    · rcases m.htr 0 3 5 (by decide) (by decide) with h15038 | h15038
      · rcases m.htr 0 4 5 (by decide) (by decide) with h15039 | h15039
        · linarith only [h14803, h14804, h15039, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h15041 | h15041
          · rcases m.htr 1 2 4 (by decide) (by decide) with h15042 | h15042
            · rcases m.htr 1 2 5 (by decide) (by decide) with h15043 | h15043
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15044 | h15044
                · rcases m.htr 1 4 5 (by decide) (by decide) with h15045 | h15045
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h15046 | h15046
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h15047 | h15047
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h15048 | h15048
                        · linarith only [h14803, h15039, h15048, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h15050 | h15050
                          · linarith only [h14803, h14804, h15046, h15048, h15050, hlam]
                          · rcases h0bigk with h15052c | h15052c | h15052c | h15052c | h15052c | h15052c | h15052c | h15052c | h15052c | h15052c | h15052c | h15052c | h15052c | h15052c | h15052c | h15052c | h15052c | h15052c | h15052c | h15052c | h15052c | h15052c | h15052c | h15052c | h15052c
                            · have p15052_0 := h15052c.1
                              have p15052_1 := h15052c.2.1
                              have p15052_2 := h15052c.2.2.1
                              have p15052_3 := h15052c.2.2.2
                              linarith only [hlam, p15052_0]
                            · have p15052_0 := h15052c.1
                              have p15052_1 := h15052c.2.1
                              have p15052_2 := h15052c.2.2.1
                              have p15052_3 := h15052c.2.2.2
                              linarith only [h0, hlam, p15052_1]
                            · have p15052_0 := h15052c.1
                              have p15052_1 := h15052c.2.1
                              have p15052_2 := h15052c.2.2.1
                              have p15052_3 := h15052c.2.2.2
                              linarith only [h6793, hlam, p15052_0]
                            · have p15052_0 := h15052c.1
                              have p15052_1 := h15052c.2.1
                              have p15052_2 := h15052c.2.2.1
                              have p15052_3 := h15052c.2.2.2
                              linarith only [h10058, hlam, p15052_1]
                            · have p15052_0 := h15052c.1
                              have p15052_1 := h15052c.2.1
                              have p15052_2 := h15052c.2.2.1
                              have p15052_3 := h15052c.2.2.2
                              linarith only [h11024, hlam, p15052_1]
                            · have p15052_0 := h15052c.1
                              have p15052_1 := h15052c.2.1
                              have p15052_2 := h15052c.2.2.1
                              have p15052_3 := h15052c.2.2.2
                              linarith only [h14804, h15041, h15044, h15045, h15048, hc01, hc12, hlam, hphi, p15052_1]
                            · have p15052_0 := h15052c.1
                              have p15052_1 := h15052c.2.1
                              have p15052_2 := h15052c.2.2.1
                              have p15052_3 := h15052c.2.2.2
                              linarith only [hlam, p15052_0]
                            · have p15052_0 := h15052c.1
                              have p15052_1 := h15052c.2.1
                              have p15052_2 := h15052c.2.2.1
                              have p15052_3 := h15052c.2.2.2
                              linarith only [h11558, hlam, p15052_0]
                            · have p15052_0 := h15052c.1
                              have p15052_1 := h15052c.2.1
                              have p15052_2 := h15052c.2.2.1
                              have p15052_3 := h15052c.2.2.2
                              linarith only [h10058, h14804, h15041, h15044, h15045, h15048, hc01, hc12, hlam, hphi, p15052_1]
                            · have p15052_0 := h15052c.1
                              have p15052_1 := h15052c.2.1
                              have p15052_2 := h15052c.2.2.1
                              have p15052_3 := h15052c.2.2.2
                              linarith only [h14804, hlam, p15052_0]
                            · have p15052_0 := h15052c.1
                              have p15052_1 := h15052c.2.1
                              have p15052_2 := h15052c.2.2.1
                              have p15052_3 := h15052c.2.2.2
                              linarith only [h11558, h15041, hc01, hc12, hlam, hphi, p15052_1]
                            · have p15052_0 := h15052c.1
                              have p15052_1 := h15052c.2.1
                              have p15052_2 := h15052c.2.2.1
                              have p15052_3 := h15052c.2.2.2
                              linarith only [h11558, h14803, h15041, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p15052_1]
                            · have p15052_0 := h15052c.1
                              have p15052_1 := h15052c.2.1
                              have p15052_2 := h15052c.2.2.1
                              have p15052_3 := h15052c.2.2.2
                              linarith only [hlam, p15052_0]
                            · have p15052_0 := h15052c.1
                              have p15052_1 := h15052c.2.1
                              have p15052_2 := h15052c.2.2.1
                              have p15052_3 := h15052c.2.2.2
                              linarith only [h10058, h11558, h15041, hc01, hc12, hlam, hphi, p15052_1]
                            · have p15052_0 := h15052c.1
                              have p15052_1 := h15052c.2.1
                              have p15052_2 := h15052c.2.2.1
                              have p15052_3 := h15052c.2.2.2
                              linarith only [h11024, h11558, h15041, hc01, hc12, hlam, hphi, p15052_1]
                            · have p15052_0 := h15052c.1
                              have p15052_1 := h15052c.2.1
                              have p15052_2 := h15052c.2.2.1
                              have p15052_3 := h15052c.2.2.2
                              linarith only [h11558, h14803, h15041, hc01, hc12, hlam, hphi, p15052_1]
                            · have p15052_0 := h15052c.1
                              have p15052_1 := h15052c.2.1
                              have p15052_2 := h15052c.2.2.1
                              have p15052_3 := h15052c.2.2.2
                              linarith only [h14803, hlam, p15052_0]
                            · have p15052_0 := h15052c.1
                              have p15052_1 := h15052c.2.1
                              have p15052_2 := h15052c.2.2.1
                              have p15052_3 := h15052c.2.2.2
                              linarith only [h15037, hlam, p15052_0]
                            · have p15052_0 := h15052c.1
                              have p15052_1 := h15052c.2.1
                              have p15052_2 := h15052c.2.2.1
                              have p15052_3 := h15052c.2.2.2
                              linarith only [hlam, p15052_0]
                            · have p15052_0 := h15052c.1
                              have p15052_1 := h15052c.2.1
                              have p15052_2 := h15052c.2.2.1
                              have p15052_3 := h15052c.2.2.2
                              linarith only [h15039, hlam, p15052_0]
                            · have p15052_0 := h15052c.1
                              have p15052_1 := h15052c.2.1
                              have p15052_2 := h15052c.2.2.1
                              have p15052_3 := h15052c.2.2.2
                              linarith only [h14804, h15041, h15044, h15045, h15048, hc01, hc12, hlam, hphi, p15052_1]
                            · have p15052_0 := h15052c.1
                              have p15052_1 := h15052c.2.1
                              have p15052_2 := h15052c.2.2.1
                              have p15052_3 := h15052c.2.2.2
                              linarith only [h0, h14804, h15041, h15044, h15045, h15048, hc01, hc12, hlam, hphi, p15052_1]
                            · have p15052_0 := h15052c.1
                              have p15052_1 := h15052c.2.1
                              have p15052_2 := h15052c.2.2.1
                              have p15052_3 := h15052c.2.2.2
                              linarith only [h15038, hlam, p15052_0]
                            · have p15052_0 := h15052c.1
                              have p15052_1 := h15052c.2.1
                              have p15052_2 := h15052c.2.2.1
                              have p15052_3 := h15052c.2.2.2
                              linarith only [h10058, h14804, h15041, h15044, h15045, h15048, hc01, hc12, hlam, hphi, p15052_1]
                            · have p15052_0 := h15052c.1
                              have p15052_1 := h15052c.2.1
                              have p15052_2 := h15052c.2.2.1
                              have p15052_3 := h15052c.2.2.2
                              linarith only [hlam, p15052_0]
                      · linarith only [h11558, h15038, h15047, hlam]
                    · linarith only [h11558, h15037, h15046, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h15080 | h15080
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h15081 | h15081
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h15082 | h15082
                        · linarith only [h14803, h15045, h15082, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h15084 | h15084
                          · linarith only [h11024, h11558, h15037, h15041, h15045, h15084, hc01, hc12, hlam, hphi]
                          · rcases h0bigk with h15086c | h15086c | h15086c | h15086c | h15086c | h15086c | h15086c | h15086c | h15086c | h15086c | h15086c | h15086c | h15086c | h15086c | h15086c | h15086c | h15086c | h15086c | h15086c | h15086c | h15086c | h15086c | h15086c | h15086c | h15086c
                            · have p15086_0 := h15086c.1
                              have p15086_1 := h15086c.2.1
                              have p15086_2 := h15086c.2.2.1
                              have p15086_3 := h15086c.2.2.2
                              linarith only [hlam, p15086_0]
                            · have p15086_0 := h15086c.1
                              have p15086_1 := h15086c.2.1
                              have p15086_2 := h15086c.2.2.1
                              have p15086_3 := h15086c.2.2.2
                              linarith only [h0, hlam, p15086_1]
                            · have p15086_0 := h15086c.1
                              have p15086_1 := h15086c.2.1
                              have p15086_2 := h15086c.2.2.1
                              have p15086_3 := h15086c.2.2.2
                              linarith only [h6793, hlam, p15086_0]
                            · have p15086_0 := h15086c.1
                              have p15086_1 := h15086c.2.1
                              have p15086_2 := h15086c.2.2.1
                              have p15086_3 := h15086c.2.2.2
                              linarith only [h10058, hlam, p15086_1]
                            · have p15086_0 := h15086c.1
                              have p15086_1 := h15086c.2.1
                              have p15086_2 := h15086c.2.2.1
                              have p15086_3 := h15086c.2.2.2
                              linarith only [h11024, hlam, p15086_1]
                            · have p15086_0 := h15086c.1
                              have p15086_1 := h15086c.2.1
                              have p15086_2 := h15086c.2.2.1
                              have p15086_3 := h15086c.2.2.2
                              linarith only [h14804, h15041, h15081, hc01, hc12, hlam, hphi, p15086_1]
                            · have p15086_0 := h15086c.1
                              have p15086_1 := h15086c.2.1
                              have p15086_2 := h15086c.2.2.1
                              have p15086_3 := h15086c.2.2.2
                              linarith only [hlam, p15086_0]
                            · have p15086_0 := h15086c.1
                              have p15086_1 := h15086c.2.1
                              have p15086_2 := h15086c.2.2.1
                              have p15086_3 := h15086c.2.2.2
                              linarith only [h11558, hlam, p15086_0]
                            · have p15086_0 := h15086c.1
                              have p15086_1 := h15086c.2.1
                              have p15086_2 := h15086c.2.2.1
                              have p15086_3 := h15086c.2.2.2
                              linarith only [h10058, h14804, h15041, h15081, hc01, hc12, hlam, hphi, p15086_1]
                            · have p15086_0 := h15086c.1
                              have p15086_1 := h15086c.2.1
                              have p15086_2 := h15086c.2.2.1
                              have p15086_3 := h15086c.2.2.2
                              linarith only [h14804, hlam, p15086_0]
                            · have p15086_0 := h15086c.1
                              have p15086_1 := h15086c.2.1
                              have p15086_2 := h15086c.2.2.1
                              have p15086_3 := h15086c.2.2.2
                              linarith only [h11558, h15041, hc01, hc12, hlam, hphi, p15086_1]
                            · have p15086_0 := h15086c.1
                              have p15086_1 := h15086c.2.1
                              have p15086_2 := h15086c.2.2.1
                              have p15086_3 := h15086c.2.2.2
                              linarith only [h11558, h14803, h15041, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p15086_1]
                            · have p15086_0 := h15086c.1
                              have p15086_1 := h15086c.2.1
                              have p15086_2 := h15086c.2.2.1
                              have p15086_3 := h15086c.2.2.2
                              linarith only [hlam, p15086_0]
                            · have p15086_0 := h15086c.1
                              have p15086_1 := h15086c.2.1
                              have p15086_2 := h15086c.2.2.1
                              have p15086_3 := h15086c.2.2.2
                              linarith only [h10058, h11558, h15041, hc01, hc12, hlam, hphi, p15086_1]
                            · have p15086_0 := h15086c.1
                              have p15086_1 := h15086c.2.1
                              have p15086_2 := h15086c.2.2.1
                              have p15086_3 := h15086c.2.2.2
                              linarith only [h11558, h14803, h14804, h15041, h15080, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15086_1]
                            · have p15086_0 := h15086c.1
                              have p15086_1 := h15086c.2.1
                              have p15086_2 := h15086c.2.2.1
                              have p15086_3 := h15086c.2.2.2
                              linarith only [h11558, h14803, h15041, hc01, hc12, hlam, hphi, p15086_1]
                            · have p15086_0 := h15086c.1
                              have p15086_1 := h15086c.2.1
                              have p15086_2 := h15086c.2.2.1
                              have p15086_3 := h15086c.2.2.2
                              linarith only [h14803, hlam, p15086_0]
                            · have p15086_0 := h15086c.1
                              have p15086_1 := h15086c.2.1
                              have p15086_2 := h15086c.2.2.1
                              have p15086_3 := h15086c.2.2.2
                              linarith only [h15037, hlam, p15086_0]
                            · have p15086_0 := h15086c.1
                              have p15086_1 := h15086c.2.1
                              have p15086_2 := h15086c.2.2.1
                              have p15086_3 := h15086c.2.2.2
                              linarith only [hlam, p15086_0]
                            · have p15086_0 := h15086c.1
                              have p15086_1 := h15086c.2.1
                              have p15086_2 := h15086c.2.2.1
                              have p15086_3 := h15086c.2.2.2
                              linarith only [h15039, hlam, p15086_0]
                            · have p15086_0 := h15086c.1
                              have p15086_1 := h15086c.2.1
                              have p15086_2 := h15086c.2.2.1
                              have p15086_3 := h15086c.2.2.2
                              linarith only [h14804, h15041, h15081, hc01, hc12, hlam, hphi, p15086_1]
                            · have p15086_0 := h15086c.1
                              have p15086_1 := h15086c.2.1
                              have p15086_2 := h15086c.2.2.1
                              have p15086_3 := h15086c.2.2.2
                              linarith only [h0, h14804, h15041, h15081, hc01, hc12, hlam, hphi, p15086_1]
                            · have p15086_0 := h15086c.1
                              have p15086_1 := h15086c.2.1
                              have p15086_2 := h15086c.2.2.1
                              have p15086_3 := h15086c.2.2.2
                              linarith only [h15038, hlam, p15086_0]
                            · have p15086_0 := h15086c.1
                              have p15086_1 := h15086c.2.1
                              have p15086_2 := h15086c.2.2.1
                              have p15086_3 := h15086c.2.2.2
                              linarith only [h10058, h14804, h15041, h15081, hc01, hc12, hlam, hphi, p15086_1]
                            · have p15086_0 := h15086c.1
                              have p15086_1 := h15086c.2.1
                              have p15086_2 := h15086c.2.2.1
                              have p15086_3 := h15086c.2.2.2
                              linarith only [hlam, p15086_0]
                      · linarith only [h11558, h15038, h15081, hlam]
                    · linarith only [h11558, h15037, h15080, hlam]
                · linarith only [h11558, h14803, h15037, h15044, h6793, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h11558, h15041, h15043, hc02, hc25, hlam, hphi]
            · linarith only [h11558, h14803, h15041, h15042, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h15117 | h15117
            · rcases m.htr 1 2 5 (by decide) (by decide) with h15118 | h15118
              · linarith only [h14803, h14804, h15041, h15118, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15120 | h15120
                · rcases m.htr 1 4 5 (by decide) (by decide) with h15121 | h15121
                  · linarith only [h10058, h15039, h15041, h15117, h15121, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h15123 | h15123
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h15124 | h15124
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h15125 | h15125
                        · linarith only [h14803, h15121, h15125, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h15127 | h15127
                          · linarith only [h0, h15118, h15125, h15127, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases h0bigk with h15129c | h15129c | h15129c | h15129c | h15129c | h15129c | h15129c | h15129c | h15129c | h15129c | h15129c | h15129c | h15129c | h15129c | h15129c | h15129c | h15129c | h15129c | h15129c | h15129c | h15129c | h15129c | h15129c | h15129c | h15129c
                            · have p15129_0 := h15129c.1
                              have p15129_1 := h15129c.2.1
                              have p15129_2 := h15129c.2.2.1
                              have p15129_3 := h15129c.2.2.2
                              linarith only [hlam, p15129_0]
                            · have p15129_0 := h15129c.1
                              have p15129_1 := h15129c.2.1
                              have p15129_2 := h15129c.2.2.1
                              have p15129_3 := h15129c.2.2.2
                              linarith only [h0, hlam, p15129_1]
                            · have p15129_0 := h15129c.1
                              have p15129_1 := h15129c.2.1
                              have p15129_2 := h15129c.2.2.1
                              have p15129_3 := h15129c.2.2.2
                              linarith only [h6793, hlam, p15129_0]
                            · have p15129_0 := h15129c.1
                              have p15129_1 := h15129c.2.1
                              have p15129_2 := h15129c.2.2.1
                              have p15129_3 := h15129c.2.2.2
                              linarith only [h10058, hlam, p15129_1]
                            · have p15129_0 := h15129c.1
                              have p15129_1 := h15129c.2.1
                              have p15129_2 := h15129c.2.2.1
                              have p15129_3 := h15129c.2.2.2
                              linarith only [h11024, hlam, p15129_1]
                            · have p15129_0 := h15129c.1
                              have p15129_1 := h15129c.2.1
                              have p15129_2 := h15129c.2.2.1
                              have p15129_3 := h15129c.2.2.2
                              linarith only [h0, h15118, hc01, hc25, hlam, hphi, ht12, p15129_1]
                            · have p15129_0 := h15129c.1
                              have p15129_1 := h15129c.2.1
                              have p15129_2 := h15129c.2.2.1
                              have p15129_3 := h15129c.2.2.2
                              linarith only [hlam, p15129_0]
                            · have p15129_0 := h15129c.1
                              have p15129_1 := h15129c.2.1
                              have p15129_2 := h15129c.2.2.1
                              have p15129_3 := h15129c.2.2.2
                              linarith only [h11558, hlam, p15129_0]
                            · have p15129_0 := h15129c.1
                              have p15129_1 := h15129c.2.1
                              have p15129_2 := h15129c.2.2.1
                              have p15129_3 := h15129c.2.2.2
                              linarith only [h0, h10058, h15118, h15125, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p15129_1]
                            · have p15129_0 := h15129c.1
                              have p15129_1 := h15129c.2.1
                              have p15129_2 := h15129c.2.2.1
                              have p15129_3 := h15129c.2.2.2
                              linarith only [h14804, hlam, p15129_0]
                            · have p15129_0 := h15129c.1
                              have p15129_1 := h15129c.2.1
                              have p15129_2 := h15129c.2.2.1
                              have p15129_3 := h15129c.2.2.2
                              rcases p15129_3 (m.d 0 1) (by simp) with h15140 | h15140
                              · linarith only [h15140, h6793, hlam]
                              · rcases p15129_3 (m.d 0 2) (by simp) with h15142 | h15142
                                · linarith only [h11558, h15142, hlam]
                                · linarith only [h0, h15142, hlam]
                            · have p15129_0 := h15129c.1
                              have p15129_1 := h15129c.2.1
                              have p15129_2 := h15129c.2.2.1
                              have p15129_3 := h15129c.2.2.2
                              linarith only [h14803, hc24, hlam, hphi, ht0b, ht45, ht5b, p15129_1, u0elo2]
                            · have p15129_0 := h15129c.1
                              have p15129_1 := h15129c.2.1
                              have p15129_2 := h15129c.2.2.1
                              have p15129_3 := h15129c.2.2.2
                              linarith only [hlam, p15129_0]
                            · have p15129_0 := h15129c.1
                              have p15129_1 := h15129c.2.1
                              have p15129_2 := h15129c.2.2.1
                              have p15129_3 := h15129c.2.2.2
                              rcases p15129_3 (m.d 0 1) (by simp) with h15147 | h15147
                              · linarith only [h15147, h6793, hlam]
                              · rcases p15129_3 (m.d 0 2) (by simp) with h15149 | h15149
                                · linarith only [h11558, h15149, hlam]
                                · linarith only [h14803, h15149, hlam]
                            · have p15129_0 := h15129c.1
                              have p15129_1 := h15129c.2.1
                              have p15129_2 := h15129c.2.2.1
                              have p15129_3 := h15129c.2.2.2
                              linarith only [h14803, h14804, h15123, hc34, hlam, hphi, ht0b, ht45, ht5b, p15129_1, u0elo2]
                            · have p15129_0 := h15129c.1
                              have p15129_1 := h15129c.2.1
                              have p15129_2 := h15129c.2.2.1
                              have p15129_3 := h15129c.2.2.2
                              linarith only [h0, h14803, h15118, h15125, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p15129_1]
                            · have p15129_0 := h15129c.1
                              have p15129_1 := h15129c.2.1
                              have p15129_2 := h15129c.2.2.1
                              have p15129_3 := h15129c.2.2.2
                              linarith only [h14803, hlam, p15129_0]
                            · have p15129_0 := h15129c.1
                              have p15129_1 := h15129c.2.1
                              have p15129_2 := h15129c.2.2.1
                              have p15129_3 := h15129c.2.2.2
                              linarith only [h15037, hlam, p15129_0]
                            · have p15129_0 := h15129c.1
                              have p15129_1 := h15129c.2.1
                              have p15129_2 := h15129c.2.2.1
                              have p15129_3 := h15129c.2.2.2
                              linarith only [hlam, p15129_0]
                            · have p15129_0 := h15129c.1
                              have p15129_1 := h15129c.2.1
                              have p15129_2 := h15129c.2.2.1
                              have p15129_3 := h15129c.2.2.2
                              linarith only [h15039, hlam, p15129_0]
                            · have p15129_0 := h15129c.1
                              have p15129_1 := h15129c.2.1
                              have p15129_2 := h15129c.2.2.1
                              have p15129_3 := h15129c.2.2.2
                              rcases p15129_3 (m.d 0 1) (by simp) with h15158 | h15158
                              · linarith only [h11024, h15158, hlam]
                              · rcases p15129_3 (m.d 0 2) (by simp) with h15160 | h15160
                                · linarith only [h14804, h15160, hlam]
                                · linarith only [h0, h15160, hlam]
                            · have p15129_0 := h15129c.1
                              have p15129_1 := h15129c.2.1
                              have p15129_2 := h15129c.2.2.1
                              have p15129_3 := h15129c.2.2.2
                              linarith only [h14803, h15123, hc34, hlam, hphi, ht0b, ht45, ht5b, p15129_1, u0elo4]
                            · have p15129_0 := h15129c.1
                              have p15129_1 := h15129c.2.1
                              have p15129_2 := h15129c.2.2.1
                              have p15129_3 := h15129c.2.2.2
                              linarith only [h15038, hlam, p15129_0]
                            · have p15129_0 := h15129c.1
                              have p15129_1 := h15129c.2.1
                              have p15129_2 := h15129c.2.2.1
                              have p15129_3 := h15129c.2.2.2
                              rcases p15129_3 (m.d 0 1) (by simp) with h15165 | h15165
                              · linarith only [h11024, h15165, hlam]
                              · rcases p15129_3 (m.d 0 2) (by simp) with h15167 | h15167
                                · linarith only [h14804, h15167, hlam]
                                · linarith only [h14803, h15167, hlam]
                            · have p15129_0 := h15129c.1
                              have p15129_1 := h15129c.2.1
                              have p15129_2 := h15129c.2.2.1
                              have p15129_3 := h15129c.2.2.2
                              linarith only [hlam, p15129_0]
                      · linarith only [h15038, h15041, h15124, h6793, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h15037, h15041, h15123, h6793, hlam]
                · linarith only [h10058, h15037, h15041, h15117, h15120, h6793, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h0, h14803, h15117, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h15175 | h15175
        · linarith only [h11558, h14803, h15038, h15175, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h15177 | h15177
          · rcases m.htr 1 2 4 (by decide) (by decide) with h15178 | h15178
            · rcases m.htr 1 2 5 (by decide) (by decide) with h15179 | h15179
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15180 | h15180
                · rcases m.htr 1 4 5 (by decide) (by decide) with h15181 | h15181
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h15182 | h15182
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h15183 | h15183
                      · linarith only [h11558, h14803, h15038, h15177, h15183, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h15185 | h15185
                        · linarith only [h11558, h14803, h15183, h15185, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h15187 | h15187
                          · linarith only [h11558, h15037, h15183, h15185, h15187, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h11558, h14803, h15177, h15180, h15181, h15182, h15183, h15187, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h11558, h15037, h15182, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h15191 | h15191
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h15192 | h15192
                      · linarith only [h11558, h14803, h15038, h15177, h15192, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h15194 | h15194
                        · linarith only [h11558, h14803, h15181, h15192, h15194, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h15196 | h15196
                          · linarith only [h10058, h11558, h14803, h15181, h15191, h15192, h15196, hc01, hc35, hlam, hphi, ht12, ht23]
                          · linarith only [h11558, h14803, h15192, h15196, hc24, hc45, hlam, hphi]
                    · linarith only [h11558, h14803, h15037, h15191, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · linarith only [h11558, h14803, h15037, h15177, h15180, hlam]
              · linarith only [h11558, h15177, h15179, hc02, hc25, hlam, hphi]
            · linarith only [h11558, h14803, h15177, h15178, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h15203 | h15203
            · rcases m.htr 1 2 5 (by decide) (by decide) with h15204 | h15204
              · linarith only [h14803, h14804, h15177, h15204, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15206 | h15206
                · rcases m.htr 1 4 5 (by decide) (by decide) with h15207 | h15207
                  · linarith only [h10058, h15175, h15177, h15203, h15207, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h15209 | h15209
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h15210 | h15210
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h15211 | h15211
                        · linarith only [h14803, h15207, h15211, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h15213 | h15213
                          · linarith only [h11558, h14803, h15038, h15204, h15209, h15210, h15211, h15213, hc12, hc23, hlam, hphi]
                          · rcases h0bigk with h15215c | h15215c | h15215c | h15215c | h15215c | h15215c | h15215c | h15215c | h15215c | h15215c | h15215c | h15215c | h15215c | h15215c | h15215c | h15215c | h15215c | h15215c | h15215c | h15215c | h15215c | h15215c | h15215c | h15215c | h15215c
                            · have p15215_0 := h15215c.1
                              have p15215_1 := h15215c.2.1
                              have p15215_2 := h15215c.2.2.1
                              have p15215_3 := h15215c.2.2.2
                              linarith only [hlam, p15215_0]
                            · have p15215_0 := h15215c.1
                              have p15215_1 := h15215c.2.1
                              have p15215_2 := h15215c.2.2.1
                              have p15215_3 := h15215c.2.2.2
                              linarith only [h0, hlam, p15215_1]
                            · have p15215_0 := h15215c.1
                              have p15215_1 := h15215c.2.1
                              have p15215_2 := h15215c.2.2.1
                              have p15215_3 := h15215c.2.2.2
                              linarith only [h6793, hlam, p15215_0]
                            · have p15215_0 := h15215c.1
                              have p15215_1 := h15215c.2.1
                              have p15215_2 := h15215c.2.2.1
                              have p15215_3 := h15215c.2.2.2
                              linarith only [h10058, hlam, p15215_1]
                            · have p15215_0 := h15215c.1
                              have p15215_1 := h15215c.2.1
                              have p15215_2 := h15215c.2.2.1
                              have p15215_3 := h15215c.2.2.2
                              linarith only [h11024, hlam, p15215_1]
                            · have p15215_0 := h15215c.1
                              have p15215_1 := h15215c.2.1
                              have p15215_2 := h15215c.2.2.1
                              have p15215_3 := h15215c.2.2.2
                              linarith only [h11558, h15038, h15210, hc01, hc23, hlam, hphi, ht12, p15215_1]
                            · have p15215_0 := h15215c.1
                              have p15215_1 := h15215c.2.1
                              have p15215_2 := h15215c.2.2.1
                              have p15215_3 := h15215c.2.2.2
                              linarith only [hlam, p15215_0]
                            · have p15215_0 := h15215c.1
                              have p15215_1 := h15215c.2.1
                              have p15215_2 := h15215c.2.2.1
                              have p15215_3 := h15215c.2.2.2
                              linarith only [h11558, hlam, p15215_0]
                            · have p15215_0 := h15215c.1
                              have p15215_1 := h15215c.2.1
                              have p15215_2 := h15215c.2.2.1
                              have p15215_3 := h15215c.2.2.2
                              linarith only [h10058, h11558, h15038, h15210, hc01, hc23, hlam, hphi, ht12, p15215_1]
                            · have p15215_0 := h15215c.1
                              have p15215_1 := h15215c.2.1
                              have p15215_2 := h15215c.2.2.1
                              have p15215_3 := h15215c.2.2.2
                              linarith only [h14804, hlam, p15215_0]
                            · have p15215_0 := h15215c.1
                              have p15215_1 := h15215c.2.1
                              have p15215_2 := h15215c.2.2.1
                              have p15215_3 := h15215c.2.2.2
                              linarith only [h15038, h15210, hc01, hc23, hlam, hphi, ht12, p15215_1]
                            · have p15215_0 := h15215c.1
                              have p15215_1 := h15215c.2.1
                              have p15215_2 := h15215c.2.2.1
                              have p15215_3 := h15215c.2.2.2
                              linarith only [h14803, h15038, h15209, h15210, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p15215_1]
                            · have p15215_0 := h15215c.1
                              have p15215_1 := h15215c.2.1
                              have p15215_2 := h15215c.2.2.1
                              have p15215_3 := h15215c.2.2.2
                              linarith only [hlam, p15215_0]
                            · have p15215_0 := h15215c.1
                              have p15215_1 := h15215c.2.1
                              have p15215_2 := h15215c.2.2.1
                              have p15215_3 := h15215c.2.2.2
                              linarith only [h10058, h15038, h15210, hc01, hc23, hlam, hphi, ht12, p15215_1]
                            · have p15215_0 := h15215c.1
                              have p15215_1 := h15215c.2.1
                              have p15215_2 := h15215c.2.2.1
                              have p15215_3 := h15215c.2.2.2
                              linarith only [h15038, hlam, p15215_1]
                            · have p15215_0 := h15215c.1
                              have p15215_1 := h15215c.2.1
                              have p15215_2 := h15215c.2.2.1
                              have p15215_3 := h15215c.2.2.2
                              linarith only [h10058, h15203, h15204, hc01, hc25, hlam, hphi, ht12, p15215_1]
                            · have p15215_0 := h15215c.1
                              have p15215_1 := h15215c.2.1
                              have p15215_2 := h15215c.2.2.1
                              have p15215_3 := h15215c.2.2.2
                              linarith only [h14803, hlam, p15215_0]
                            · have p15215_0 := h15215c.1
                              have p15215_1 := h15215c.2.1
                              have p15215_2 := h15215c.2.2.1
                              have p15215_3 := h15215c.2.2.2
                              linarith only [h15037, hlam, p15215_0]
                            · have p15215_0 := h15215c.1
                              have p15215_1 := h15215c.2.1
                              have p15215_2 := h15215c.2.2.1
                              have p15215_3 := h15215c.2.2.2
                              linarith only [hlam, p15215_0]
                            · have p15215_0 := h15215c.1
                              have p15215_1 := h15215c.2.1
                              have p15215_2 := h15215c.2.2.1
                              have p15215_3 := h15215c.2.2.2
                              linarith only [h15175, hlam, p15215_0]
                            · have p15215_0 := h15215c.1
                              have p15215_1 := h15215c.2.1
                              have p15215_2 := h15215c.2.2.1
                              have p15215_3 := h15215c.2.2.2
                              linarith only [h15038, h15210, hc01, hc23, hlam, hphi, ht12, p15215_1]
                            · have p15215_0 := h15215c.1
                              have p15215_1 := h15215c.2.1
                              have p15215_2 := h15215c.2.2.1
                              have p15215_3 := h15215c.2.2.2
                              linarith only [h14803, h15209, hc34, hlam, hphi, ht0b, ht45, ht5b, p15215_1, u0elo4]
                            · have p15215_0 := h15215c.1
                              have p15215_1 := h15215c.2.1
                              have p15215_2 := h15215c.2.2.1
                              have p15215_3 := h15215c.2.2.2
                              linarith only [h11558, h14803, h15038, h15209, h15210, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p15215_1]
                            · have p15215_0 := h15215c.1
                              have p15215_1 := h15215c.2.1
                              have p15215_2 := h15215c.2.2.1
                              have p15215_3 := h15215c.2.2.2
                              linarith only [h10058, h15038, h15210, hc01, hc23, hlam, hphi, ht12, p15215_1]
                            · have p15215_0 := h15215c.1
                              have p15215_1 := h15215c.2.1
                              have p15215_2 := h15215c.2.2.1
                              have p15215_3 := h15215c.2.2.2
                              linarith only [hlam, p15215_0]
                      · linarith only [h0, h15177, h15210, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h10058, h15177, h15203, h15209, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h10058, h15037, h15177, h15203, h15206, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
            · linarith only [h0, h14803, h15203, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
    · linarith only [h11558, h14803, h15037, hlam]

set_option maxHeartbeats 9982000 in
set_option maxHeartbeats 9982000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s12_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg10058 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11024 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11558 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h14803 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h15246 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6793 := hg6793
  have h10058 := hg10058
  have h11024 := hg11024
  rcases m.htr 0 3 4 (by decide) (by decide) with h15247 | h15247
  · rcases m.htr 0 3 5 (by decide) (by decide) with h15248 | h15248
    · rcases m.htr 0 4 5 (by decide) (by decide) with h15249 | h15249
      · rcases m.htr 1 2 3 (by decide) (by decide) with h15250 | h15250
        · rcases m.htr 1 2 4 (by decide) (by decide) with h15251 | h15251
          · rcases m.htr 1 2 5 (by decide) (by decide) with h15252 | h15252
            · rcases m.htr 1 3 4 (by decide) (by decide) with h15253 | h15253
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15254 | h15254
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15255 | h15255
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15256 | h15256
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15257 | h15257
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h15258 | h15258
                        · rcases h0bigk with h15259c | h15259c | h15259c | h15259c | h15259c | h15259c | h15259c | h15259c | h15259c | h15259c | h15259c | h15259c | h15259c | h15259c | h15259c | h15259c | h15259c | h15259c | h15259c | h15259c | h15259c | h15259c | h15259c | h15259c | h15259c
                          · have p15259_0 := h15259c.1
                            have p15259_1 := h15259c.2.1
                            have p15259_2 := h15259c.2.2.1
                            have p15259_3 := h15259c.2.2.2
                            linarith only [hlam, p15259_0]
                          · have p15259_0 := h15259c.1
                            have p15259_1 := h15259c.2.1
                            have p15259_2 := h15259c.2.2.1
                            have p15259_3 := h15259c.2.2.2
                            linarith only [h0, hlam, p15259_1]
                          · have p15259_0 := h15259c.1
                            have p15259_1 := h15259c.2.1
                            have p15259_2 := h15259c.2.2.1
                            have p15259_3 := h15259c.2.2.2
                            linarith only [h6793, hlam, p15259_0]
                          · have p15259_0 := h15259c.1
                            have p15259_1 := h15259c.2.1
                            have p15259_2 := h15259c.2.2.1
                            have p15259_3 := h15259c.2.2.2
                            linarith only [h10058, hlam, p15259_1]
                          · have p15259_0 := h15259c.1
                            have p15259_1 := h15259c.2.1
                            have p15259_2 := h15259c.2.2.1
                            have p15259_3 := h15259c.2.2.2
                            linarith only [h11024, hlam, p15259_1]
                          · have p15259_0 := h15259c.1
                            have p15259_1 := h15259c.2.1
                            have p15259_2 := h15259c.2.2.1
                            have p15259_3 := h15259c.2.2.2
                            linarith only [h14803, h15251, hc01, hc14, hlam, hphi, p15259_1]
                          · have p15259_0 := h15259c.1
                            have p15259_1 := h15259c.2.1
                            have p15259_2 := h15259c.2.2.1
                            have p15259_3 := h15259c.2.2.2
                            linarith only [hlam, p15259_0]
                          · have p15259_0 := h15259c.1
                            have p15259_1 := h15259c.2.1
                            have p15259_2 := h15259c.2.2.1
                            have p15259_3 := h15259c.2.2.2
                            linarith only [h11558, hlam, p15259_0]
                          · have p15259_0 := h15259c.1
                            have p15259_1 := h15259c.2.1
                            have p15259_2 := h15259c.2.2.1
                            have p15259_3 := h15259c.2.2.2
                            linarith only [h14803, hlam, p15259_1]
                          · have p15259_0 := h15259c.1
                            have p15259_1 := h15259c.2.1
                            have p15259_2 := h15259c.2.2.1
                            have p15259_3 := h15259c.2.2.2
                            linarith only [h11024, h14803, h15251, hc01, hc14, hlam, hphi, p15259_1]
                          · have p15259_0 := h15259c.1
                            have p15259_1 := h15259c.2.1
                            have p15259_2 := h15259c.2.2.1
                            have p15259_3 := h15259c.2.2.2
                            linarith only [h11558, h15250, hc01, hc12, hlam, hphi, p15259_1]
                          · have p15259_0 := h15259c.1
                            have p15259_1 := h15259c.2.1
                            have p15259_2 := h15259c.2.2.1
                            have p15259_3 := h15259c.2.2.2
                            linarith only [h11558, h15246, h15250, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p15259_1]
                          · have p15259_0 := h15259c.1
                            have p15259_1 := h15259c.2.1
                            have p15259_2 := h15259c.2.2.1
                            have p15259_3 := h15259c.2.2.2
                            linarith only [hlam, p15259_0]
                          · have p15259_0 := h15259c.1
                            have p15259_1 := h15259c.2.1
                            have p15259_2 := h15259c.2.2.1
                            have p15259_3 := h15259c.2.2.2
                            linarith only [h10058, h11558, h15250, hc01, hc12, hlam, hphi, p15259_1]
                          · have p15259_0 := h15259c.1
                            have p15259_1 := h15259c.2.1
                            have p15259_2 := h15259c.2.2.1
                            have p15259_3 := h15259c.2.2.2
                            linarith only [h11024, h11558, h15250, hc01, hc12, hlam, hphi, p15259_1]
                          · have p15259_0 := h15259c.1
                            have p15259_1 := h15259c.2.1
                            have p15259_2 := h15259c.2.2.1
                            have p15259_3 := h15259c.2.2.2
                            linarith only [h11558, h15247, h15250, hc01, hc12, hlam, hphi, p15259_1]
                          · have p15259_0 := h15259c.1
                            have p15259_1 := h15259c.2.1
                            have p15259_2 := h15259c.2.2.1
                            have p15259_3 := h15259c.2.2.2
                            linarith only [h15246, h15256, hc35, hlam, hphi, ht0b, ht5b, p15259_1, u0elo3]
                          · have p15259_0 := h15259c.1
                            have p15259_1 := h15259c.2.1
                            have p15259_2 := h15259c.2.2.1
                            have p15259_3 := h15259c.2.2.2
                            linarith only [h15247, hlam, p15259_0]
                          · have p15259_0 := h15259c.1
                            have p15259_1 := h15259c.2.1
                            have p15259_2 := h15259c.2.2.1
                            have p15259_3 := h15259c.2.2.2
                            linarith only [hlam, p15259_0]
                          · have p15259_0 := h15259c.1
                            have p15259_1 := h15259c.2.1
                            have p15259_2 := h15259c.2.2.1
                            have p15259_3 := h15259c.2.2.2
                            linarith only [h11024, h11558, h15247, h15250, hc01, hc12, hlam, hphi, p15259_1]
                          · have p15259_0 := h15259c.1
                            have p15259_1 := h15259c.2.1
                            have p15259_2 := h15259c.2.2.1
                            have p15259_3 := h15259c.2.2.2
                            linarith only [h11558, h15246, h15250, hc01, hc12, hlam, hphi, p15259_1]
                          · have p15259_0 := h15259c.1
                            have p15259_1 := h15259c.2.1
                            have p15259_2 := h15259c.2.2.1
                            have p15259_3 := h15259c.2.2.2
                            linarith only [h15246, hlam, p15259_1]
                          · have p15259_0 := h15259c.1
                            have p15259_1 := h15259c.2.1
                            have p15259_2 := h15259c.2.2.1
                            have p15259_3 := h15259c.2.2.2
                            linarith only [h15248, hlam, p15259_0]
                          · have p15259_0 := h15259c.1
                            have p15259_1 := h15259c.2.1
                            have p15259_2 := h15259c.2.2.1
                            have p15259_3 := h15259c.2.2.2
                            linarith only [h15249, hlam, p15259_1]
                          · have p15259_0 := h15259c.1
                            have p15259_1 := h15259c.2.1
                            have p15259_2 := h15259c.2.2.1
                            have p15259_3 := h15259c.2.2.2
                            linarith only [hlam, p15259_0]
                        · linarith only [h14803, h15246, h15250, h15255, h15257, h15258, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h14803, h15247, h15249, h15257, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h11558, h15248, h15256, hlam]
                  · linarith only [h11558, h15247, h15255, hlam]
                · linarith only [h10058, h11558, h15246, h15249, h15254, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h11558, h15247, h15250, h15253, h6793, hc01, hc12, hlam, hphi]
            · linarith only [h11558, h15250, h15252, hc02, hc25, hlam, hphi]
          · linarith only [h11024, h11558, h15246, h15250, h15251, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h15293 | h15293
          · linarith only [h11024, h14803, h15246, h15250, h15293, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h15295 | h15295
            · rcases m.htr 1 3 4 (by decide) (by decide) with h15296 | h15296
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15297 | h15297
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15298 | h15298
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15299 | h15299
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15300 | h15300
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h15301 | h15301
                        · rcases h0bigk with h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c | h15302c
                          · have p15302_0 := h15302c.1
                            have p15302_1 := h15302c.2.1
                            have p15302_2 := h15302c.2.2.1
                            have p15302_3 := h15302c.2.2.2
                            linarith only [hlam, p15302_0]
                          · have p15302_0 := h15302c.1
                            have p15302_1 := h15302c.2.1
                            have p15302_2 := h15302c.2.2.1
                            have p15302_3 := h15302c.2.2.2
                            linarith only [h0, hlam, p15302_1]
                          · have p15302_0 := h15302c.1
                            have p15302_1 := h15302c.2.1
                            have p15302_2 := h15302c.2.2.1
                            have p15302_3 := h15302c.2.2.2
                            linarith only [h6793, hlam, p15302_0]
                          · have p15302_0 := h15302c.1
                            have p15302_1 := h15302c.2.1
                            have p15302_2 := h15302c.2.2.1
                            have p15302_3 := h15302c.2.2.2
                            linarith only [h10058, hlam, p15302_1]
                          · have p15302_0 := h15302c.1
                            have p15302_1 := h15302c.2.1
                            have p15302_2 := h15302c.2.2.1
                            have p15302_3 := h15302c.2.2.2
                            linarith only [h11024, hlam, p15302_1]
                          · have p15302_0 := h15302c.1
                            have p15302_1 := h15302c.2.1
                            have p15302_2 := h15302c.2.2.1
                            have p15302_3 := h15302c.2.2.2
                            linarith only [h0, h15293, h15298, hc01, hc23, hlam, hphi, ht12, p15302_1]
                          · have p15302_0 := h15302c.1
                            have p15302_1 := h15302c.2.1
                            have p15302_2 := h15302c.2.2.1
                            have p15302_3 := h15302c.2.2.2
                            linarith only [hlam, p15302_0]
                          · have p15302_0 := h15302c.1
                            have p15302_1 := h15302c.2.1
                            have p15302_2 := h15302c.2.2.1
                            have p15302_3 := h15302c.2.2.2
                            linarith only [h11558, hlam, p15302_0]
                          · have p15302_0 := h15302c.1
                            have p15302_1 := h15302c.2.1
                            have p15302_2 := h15302c.2.2.1
                            have p15302_3 := h15302c.2.2.2
                            linarith only [h14803, hlam, p15302_1]
                          · have p15302_0 := h15302c.1
                            have p15302_1 := h15302c.2.1
                            have p15302_2 := h15302c.2.2.1
                            have p15302_3 := h15302c.2.2.2
                            linarith only [h0, h11024, h15293, h15298, hc01, hc23, hlam, hphi, ht12, p15302_1]
                          · have p15302_0 := h15302c.1
                            have p15302_1 := h15302c.2.1
                            have p15302_2 := h15302c.2.2.1
                            have p15302_3 := h15302c.2.2.2
                            rcases p15302_3 (m.d 0 1) (by simp) with h15313 | h15313
                            · linarith only [h15313, h6793, hlam]
                            · rcases p15302_3 (m.d 0 2) (by simp) with h15315 | h15315
                              · linarith only [h11558, h15315, hlam]
                              · linarith only [h0, h15315, hlam]
                          · have p15302_0 := h15302c.1
                            have p15302_1 := h15302c.2.1
                            have p15302_2 := h15302c.2.2.1
                            have p15302_3 := h15302c.2.2.2
                            linarith only [h15246, hc25, hlam, hphi, ht0b, ht5b, p15302_1, u0elo2]
                          · have p15302_0 := h15302c.1
                            have p15302_1 := h15302c.2.1
                            have p15302_2 := h15302c.2.2.1
                            have p15302_3 := h15302c.2.2.2
                            linarith only [hlam, p15302_0]
                          · have p15302_0 := h15302c.1
                            have p15302_1 := h15302c.2.1
                            have p15302_2 := h15302c.2.2.1
                            have p15302_3 := h15302c.2.2.2
                            linarith only [h14803, h15246, h15299, h15301, hc45, hlam, hphi, ht0b, ht5b, p15302_1, u0elo2]
                          · have p15302_0 := h15302c.1
                            have p15302_1 := h15302c.2.1
                            have p15302_2 := h15302c.2.2.1
                            have p15302_3 := h15302c.2.2.2
                            rcases p15302_3 (m.d 0 1) (by simp) with h15321 | h15321
                            · linarith only [h15321, h6793, hlam]
                            · rcases p15302_3 (m.d 0 2) (by simp) with h15323 | h15323
                              · linarith only [h11558, h15323, hlam]
                              · linarith only [h15246, h15323, hlam]
                          · have p15302_0 := h15302c.1
                            have p15302_1 := h15302c.2.1
                            have p15302_2 := h15302c.2.2.1
                            have p15302_3 := h15302c.2.2.2
                            rcases p15302_3 (m.d 0 1) (by simp) with h15326 | h15326
                            · linarith only [h10058, h15326, hlam]
                            · rcases p15302_3 (m.d 0 2) (by simp) with h15328 | h15328
                              · linarith only [h14803, h15328, hlam]
                              · linarith only [h0, h15328, hlam]
                          · have p15302_0 := h15302c.1
                            have p15302_1 := h15302c.2.1
                            have p15302_2 := h15302c.2.2.1
                            have p15302_3 := h15302c.2.2.2
                            linarith only [h15246, h15299, h15301, hc45, hlam, hphi, ht0b, ht5b, p15302_1, u0elo3]
                          · have p15302_0 := h15302c.1
                            have p15302_1 := h15302c.2.1
                            have p15302_2 := h15302c.2.2.1
                            have p15302_3 := h15302c.2.2.2
                            linarith only [h15247, hlam, p15302_0]
                          · have p15302_0 := h15302c.1
                            have p15302_1 := h15302c.2.1
                            have p15302_2 := h15302c.2.2.1
                            have p15302_3 := h15302c.2.2.2
                            linarith only [hlam, p15302_0]
                          · have p15302_0 := h15302c.1
                            have p15302_1 := h15302c.2.1
                            have p15302_2 := h15302c.2.2.1
                            have p15302_3 := h15302c.2.2.2
                            rcases p15302_3 (m.d 0 1) (by simp) with h15334 | h15334
                            · linarith only [h10058, h15334, hlam]
                            · rcases p15302_3 (m.d 0 2) (by simp) with h15336 | h15336
                              · linarith only [h14803, h15336, hlam]
                              · linarith only [h15246, h15336, hlam]
                          · have p15302_0 := h15302c.1
                            have p15302_1 := h15302c.2.1
                            have p15302_2 := h15302c.2.2.1
                            have p15302_3 := h15302c.2.2.2
                            linarith only [h0, h15246, h15293, h15298, hc01, hc23, hlam, hphi, ht12, p15302_1]
                          · have p15302_0 := h15302c.1
                            have p15302_1 := h15302c.2.1
                            have p15302_2 := h15302c.2.2.1
                            have p15302_3 := h15302c.2.2.2
                            linarith only [h15246, hlam, p15302_1]
                          · have p15302_0 := h15302c.1
                            have p15302_1 := h15302c.2.1
                            have p15302_2 := h15302c.2.2.1
                            have p15302_3 := h15302c.2.2.2
                            linarith only [h15248, hlam, p15302_0]
                          · have p15302_0 := h15302c.1
                            have p15302_1 := h15302c.2.1
                            have p15302_2 := h15302c.2.2.1
                            have p15302_3 := h15302c.2.2.2
                            linarith only [h15249, hlam, p15302_1]
                          · have p15302_0 := h15302c.1
                            have p15302_1 := h15302c.2.1
                            have p15302_2 := h15302c.2.2.1
                            have p15302_3 := h15302c.2.2.2
                            linarith only [hlam, p15302_0]
                        · rcases h0bigk with h15344c | h15344c | h15344c | h15344c | h15344c | h15344c | h15344c | h15344c | h15344c | h15344c | h15344c | h15344c | h15344c | h15344c | h15344c | h15344c | h15344c | h15344c | h15344c | h15344c | h15344c | h15344c | h15344c | h15344c | h15344c
                          · have p15344_0 := h15344c.1
                            have p15344_1 := h15344c.2.1
                            have p15344_2 := h15344c.2.2.1
                            have p15344_3 := h15344c.2.2.2
                            linarith only [hlam, p15344_0]
                          · have p15344_0 := h15344c.1
                            have p15344_1 := h15344c.2.1
                            have p15344_2 := h15344c.2.2.1
                            have p15344_3 := h15344c.2.2.2
                            linarith only [h0, hlam, p15344_1]
                          · have p15344_0 := h15344c.1
                            have p15344_1 := h15344c.2.1
                            have p15344_2 := h15344c.2.2.1
                            have p15344_3 := h15344c.2.2.2
                            linarith only [h6793, hlam, p15344_0]
                          · have p15344_0 := h15344c.1
                            have p15344_1 := h15344c.2.1
                            have p15344_2 := h15344c.2.2.1
                            have p15344_3 := h15344c.2.2.2
                            linarith only [h10058, hlam, p15344_1]
                          · have p15344_0 := h15344c.1
                            have p15344_1 := h15344c.2.1
                            have p15344_2 := h15344c.2.2.1
                            have p15344_3 := h15344c.2.2.2
                            linarith only [h11024, hlam, p15344_1]
                          · have p15344_0 := h15344c.1
                            have p15344_1 := h15344c.2.1
                            have p15344_2 := h15344c.2.2.1
                            have p15344_3 := h15344c.2.2.2
                            linarith only [h0, h15293, h15298, hc01, hc23, hlam, hphi, ht12, p15344_1]
                          · have p15344_0 := h15344c.1
                            have p15344_1 := h15344c.2.1
                            have p15344_2 := h15344c.2.2.1
                            have p15344_3 := h15344c.2.2.2
                            linarith only [hlam, p15344_0]
                          · have p15344_0 := h15344c.1
                            have p15344_1 := h15344c.2.1
                            have p15344_2 := h15344c.2.2.1
                            have p15344_3 := h15344c.2.2.2
                            linarith only [h11558, hlam, p15344_0]
                          · have p15344_0 := h15344c.1
                            have p15344_1 := h15344c.2.1
                            have p15344_2 := h15344c.2.2.1
                            have p15344_3 := h15344c.2.2.2
                            linarith only [h14803, hlam, p15344_1]
                          · have p15344_0 := h15344c.1
                            have p15344_1 := h15344c.2.1
                            have p15344_2 := h15344c.2.2.1
                            have p15344_3 := h15344c.2.2.2
                            linarith only [h0, h11024, h15293, h15298, hc01, hc23, hlam, hphi, ht12, p15344_1]
                          · have p15344_0 := h15344c.1
                            have p15344_1 := h15344c.2.1
                            have p15344_2 := h15344c.2.2.1
                            have p15344_3 := h15344c.2.2.2
                            rcases p15344_3 (m.d 0 1) (by simp) with h15355 | h15355
                            · linarith only [h15355, h6793, hlam]
                            · rcases p15344_3 (m.d 0 2) (by simp) with h15357 | h15357
                              · linarith only [h11558, h15357, hlam]
                              · linarith only [h0, h15357, hlam]
                          · have p15344_0 := h15344c.1
                            have p15344_1 := h15344c.2.1
                            have p15344_2 := h15344c.2.2.1
                            have p15344_3 := h15344c.2.2.2
                            linarith only [h15246, h15300, h15301, hc34, hlam, hphi, ht0b, ht45, ht5b, p15344_1, u0elo2]
                          · have p15344_0 := h15344c.1
                            have p15344_1 := h15344c.2.1
                            have p15344_2 := h15344c.2.2.1
                            have p15344_3 := h15344c.2.2.2
                            linarith only [hlam, p15344_0]
                          · have p15344_0 := h15344c.1
                            have p15344_1 := h15344c.2.1
                            have p15344_2 := h15344c.2.2.1
                            have p15344_3 := h15344c.2.2.2
                            linarith only [h14803, h15246, h15300, h15301, hc34, hlam, hphi, ht0b, ht45, ht5b, p15344_1, u0elo2]
                          · have p15344_0 := h15344c.1
                            have p15344_1 := h15344c.2.1
                            have p15344_2 := h15344c.2.2.1
                            have p15344_3 := h15344c.2.2.2
                            linarith only [h15246, h15300, h15301, hc34, hlam, hphi, ht0b, ht45, ht5b, p15344_1, u0elo2]
                          · have p15344_0 := h15344c.1
                            have p15344_1 := h15344c.2.1
                            have p15344_2 := h15344c.2.2.1
                            have p15344_3 := h15344c.2.2.2
                            rcases p15344_3 (m.d 0 1) (by simp) with h15364 | h15364
                            · linarith only [h10058, h15364, hlam]
                            · rcases p15344_3 (m.d 0 2) (by simp) with h15366 | h15366
                              · linarith only [h14803, h15366, hlam]
                              · linarith only [h0, h15366, hlam]
                          · have p15344_0 := h15344c.1
                            have p15344_1 := h15344c.2.1
                            have p15344_2 := h15344c.2.2.1
                            have p15344_3 := h15344c.2.2.2
                            linarith only [h15246, h15300, h15301, hc34, hlam, hphi, ht0b, ht45, ht5b, p15344_1, u0elo3]
                          · have p15344_0 := h15344c.1
                            have p15344_1 := h15344c.2.1
                            have p15344_2 := h15344c.2.2.1
                            have p15344_3 := h15344c.2.2.2
                            linarith only [h15247, hlam, p15344_0]
                          · have p15344_0 := h15344c.1
                            have p15344_1 := h15344c.2.1
                            have p15344_2 := h15344c.2.2.1
                            have p15344_3 := h15344c.2.2.2
                            linarith only [hlam, p15344_0]
                          · have p15344_0 := h15344c.1
                            have p15344_1 := h15344c.2.1
                            have p15344_2 := h15344c.2.2.1
                            have p15344_3 := h15344c.2.2.2
                            linarith only [h15246, h15247, h15300, h15301, hc34, hlam, hphi, ht0b, ht45, ht5b, p15344_1, u0elo2]
                          · have p15344_0 := h15344c.1
                            have p15344_1 := h15344c.2.1
                            have p15344_2 := h15344c.2.2.1
                            have p15344_3 := h15344c.2.2.2
                            linarith only [h0, h15246, h15293, h15298, hc01, hc23, hlam, hphi, ht12, p15344_1]
                          · have p15344_0 := h15344c.1
                            have p15344_1 := h15344c.2.1
                            have p15344_2 := h15344c.2.2.1
                            have p15344_3 := h15344c.2.2.2
                            linarith only [h15246, hlam, p15344_1]
                          · have p15344_0 := h15344c.1
                            have p15344_1 := h15344c.2.1
                            have p15344_2 := h15344c.2.2.1
                            have p15344_3 := h15344c.2.2.2
                            linarith only [h15248, hlam, p15344_0]
                          · have p15344_0 := h15344c.1
                            have p15344_1 := h15344c.2.1
                            have p15344_2 := h15344c.2.2.1
                            have p15344_3 := h15344c.2.2.2
                            linarith only [h15249, hlam, p15344_1]
                          · have p15344_0 := h15344c.1
                            have p15344_1 := h15344c.2.1
                            have p15344_2 := h15344c.2.2.1
                            have p15344_3 := h15344c.2.2.2
                            linarith only [hlam, p15344_0]
                      · linarith only [h0, h15293, h15300, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h15293, h15298, h15299, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h15247, h15250, h15298, h6793, hlam]
                · linarith only [h10058, h15247, h15249, h15297, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h15247, h15296, h6793, hlam]
            · linarith only [h0, h15246, h15295, hlam]
      · linarith only [h14803, h15246, h15249, hlam]
    · linarith only [h11558, h15246, h15248, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h15386 | h15386
    · rcases m.htr 0 4 5 (by decide) (by decide) with h15387 | h15387
      · rcases m.htr 1 2 3 (by decide) (by decide) with h15388 | h15388
        · rcases m.htr 1 2 4 (by decide) (by decide) with h15389 | h15389
          · rcases m.htr 1 2 5 (by decide) (by decide) with h15390 | h15390
            · rcases m.htr 1 3 4 (by decide) (by decide) with h15391 | h15391
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15392 | h15392
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15393 | h15393
                  · linarith only [h11558, h15246, h15247, h15388, h15393, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h11558, h15246, h15391, h15393, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h10058, h15387, h15392, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15397 | h15397
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15398 | h15398
                  · linarith only [h15388, h15391, h15398, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15400 | h15400
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15401 | h15401
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h15402 | h15402
                        · rcases h0bigk with h15403c | h15403c | h15403c | h15403c | h15403c | h15403c | h15403c | h15403c | h15403c | h15403c | h15403c | h15403c | h15403c | h15403c | h15403c | h15403c | h15403c | h15403c | h15403c | h15403c | h15403c | h15403c | h15403c | h15403c | h15403c
                          · have p15403_0 := h15403c.1
                            have p15403_1 := h15403c.2.1
                            have p15403_2 := h15403c.2.2.1
                            have p15403_3 := h15403c.2.2.2
                            linarith only [hlam, p15403_0]
                          · have p15403_0 := h15403c.1
                            have p15403_1 := h15403c.2.1
                            have p15403_2 := h15403c.2.2.1
                            have p15403_3 := h15403c.2.2.2
                            linarith only [h0, hlam, p15403_1]
                          · have p15403_0 := h15403c.1
                            have p15403_1 := h15403c.2.1
                            have p15403_2 := h15403c.2.2.1
                            have p15403_3 := h15403c.2.2.2
                            linarith only [h6793, hlam, p15403_0]
                          · have p15403_0 := h15403c.1
                            have p15403_1 := h15403c.2.1
                            have p15403_2 := h15403c.2.2.1
                            have p15403_3 := h15403c.2.2.2
                            linarith only [h10058, hlam, p15403_1]
                          · have p15403_0 := h15403c.1
                            have p15403_1 := h15403c.2.1
                            have p15403_2 := h15403c.2.2.1
                            have p15403_3 := h15403c.2.2.2
                            linarith only [h11024, hlam, p15403_1]
                          · have p15403_0 := h15403c.1
                            have p15403_1 := h15403c.2.1
                            have p15403_2 := h15403c.2.2.1
                            have p15403_3 := h15403c.2.2.2
                            linarith only [h11558, h15388, h15391, hc01, hc34, hlam, hphi, ht12, ht23, p15403_1]
                          · have p15403_0 := h15403c.1
                            have p15403_1 := h15403c.2.1
                            have p15403_2 := h15403c.2.2.1
                            have p15403_3 := h15403c.2.2.2
                            linarith only [hlam, p15403_0]
                          · have p15403_0 := h15403c.1
                            have p15403_1 := h15403c.2.1
                            have p15403_2 := h15403c.2.2.1
                            have p15403_3 := h15403c.2.2.2
                            linarith only [h11558, hlam, p15403_0]
                          · have p15403_0 := h15403c.1
                            have p15403_1 := h15403c.2.1
                            have p15403_2 := h15403c.2.2.1
                            have p15403_3 := h15403c.2.2.2
                            linarith only [h14803, hlam, p15403_1]
                          · have p15403_0 := h15403c.1
                            have p15403_1 := h15403c.2.1
                            have p15403_2 := h15403c.2.2.1
                            have p15403_3 := h15403c.2.2.2
                            linarith only [h11558, h15388, h15391, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p15403_1]
                          · have p15403_0 := h15403c.1
                            have p15403_1 := h15403c.2.1
                            have p15403_2 := h15403c.2.2.1
                            have p15403_3 := h15403c.2.2.2
                            linarith only [h15391, h6793, hc01, hc34, hlam, hphi, ht12, ht23, p15403_1]
                          · have p15403_0 := h15403c.1
                            have p15403_1 := h15403c.2.1
                            have p15403_2 := h15403c.2.2.1
                            have p15403_3 := h15403c.2.2.2
                            linarith only [h11558, h15388, h15391, hc02, hc34, hlam, hphi, ht23, p15403_1]
                          · have p15403_0 := h15403c.1
                            have p15403_1 := h15403c.2.1
                            have p15403_2 := h15403c.2.2.1
                            have p15403_3 := h15403c.2.2.2
                            linarith only [hlam, p15403_0]
                          · have p15403_0 := h15403c.1
                            have p15403_1 := h15403c.2.1
                            have p15403_2 := h15403c.2.2.1
                            have p15403_3 := h15403c.2.2.2
                            linarith only [h15247, hlam, p15403_1]
                          · have p15403_0 := h15403c.1
                            have p15403_1 := h15403c.2.1
                            have p15403_2 := h15403c.2.2.1
                            have p15403_3 := h15403c.2.2.2
                            linarith only [h11024, h11558, h15388, h15391, hc01, hc34, hlam, hphi, ht12, ht23, p15403_1]
                          · have p15403_0 := h15403c.1
                            have p15403_1 := h15403c.2.1
                            have p15403_2 := h15403c.2.2.1
                            have p15403_3 := h15403c.2.2.2
                            linarith only [h14803, h15389, hc01, hc12, hlam, hphi, p15403_1]
                          · have p15403_0 := h15403c.1
                            have p15403_1 := h15403c.2.1
                            have p15403_2 := h15403c.2.2.1
                            have p15403_3 := h15403c.2.2.2
                            linarith only [h15246, h15400, h15402, hc45, hlam, hphi, ht0b, ht5b, p15403_1, u0elo3]
                          · have p15403_0 := h15403c.1
                            have p15403_1 := h15403c.2.1
                            have p15403_2 := h15403c.2.2.1
                            have p15403_3 := h15403c.2.2.2
                            linarith only [h11558, h15246, h15400, h15402, hc45, hlam, hphi, ht0b, ht5b, p15403_1, u0elo3]
                          · have p15403_0 := h15403c.1
                            have p15403_1 := h15403c.2.1
                            have p15403_2 := h15403c.2.2.1
                            have p15403_3 := h15403c.2.2.2
                            linarith only [hlam, p15403_0]
                          · have p15403_0 := h15403c.1
                            have p15403_1 := h15403c.2.1
                            have p15403_2 := h15403c.2.2.1
                            have p15403_3 := h15403c.2.2.2
                            linarith only [h11024, h14803, h15389, hc01, hc12, hlam, hphi, p15403_1]
                          · have p15403_0 := h15403c.1
                            have p15403_1 := h15403c.2.1
                            have p15403_2 := h15403c.2.2.1
                            have p15403_3 := h15403c.2.2.2
                            linarith only [h11558, h15246, h15388, h15391, hc01, hc34, hlam, hphi, ht12, ht23, p15403_1]
                          · have p15403_0 := h15403c.1
                            have p15403_1 := h15403c.2.1
                            have p15403_2 := h15403c.2.2.1
                            have p15403_3 := h15403c.2.2.2
                            linarith only [h15246, hlam, p15403_1]
                          · have p15403_0 := h15403c.1
                            have p15403_1 := h15403c.2.1
                            have p15403_2 := h15403c.2.2.1
                            have p15403_3 := h15403c.2.2.2
                            linarith only [h15386, hlam, p15403_0]
                          · have p15403_0 := h15403c.1
                            have p15403_1 := h15403c.2.1
                            have p15403_2 := h15403c.2.2.1
                            have p15403_3 := h15403c.2.2.2
                            linarith only [h15387, hlam, p15403_1]
                          · have p15403_0 := h15403c.1
                            have p15403_1 := h15403c.2.1
                            have p15403_2 := h15403c.2.2.1
                            have p15403_3 := h15403c.2.2.2
                            linarith only [hlam, p15403_0]
                        · linarith only [h11558, h15246, h15388, h15391, h15400, h15402, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                      · linarith only [h10058, h11558, h14803, h15246, h15387, h15388, h15391, h15401, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h11558, h15386, h15400, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h10058, h11558, h15246, h15387, h15388, h15391, h15397, hc01, hc34, hlam, hphi, ht12, ht23]
            · linarith only [h11558, h15388, h15390, hc02, hc25, hlam, hphi]
          · linarith only [h11024, h11558, h15246, h15388, h15389, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h15435 | h15435
          · linarith only [h11024, h14803, h15246, h15388, h15435, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h15437 | h15437
            · rcases m.htr 1 3 4 (by decide) (by decide) with h15438 | h15438
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15439 | h15439
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15440 | h15440
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h15441 | h15441
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h15442 | h15442
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h15443 | h15443
                        · rcases h0bigk with h15444c | h15444c | h15444c | h15444c | h15444c | h15444c | h15444c | h15444c | h15444c | h15444c | h15444c | h15444c | h15444c | h15444c | h15444c | h15444c | h15444c | h15444c | h15444c | h15444c | h15444c | h15444c | h15444c | h15444c | h15444c
                          · have p15444_0 := h15444c.1
                            have p15444_1 := h15444c.2.1
                            have p15444_2 := h15444c.2.2.1
                            have p15444_3 := h15444c.2.2.2
                            linarith only [hlam, p15444_0]
                          · have p15444_0 := h15444c.1
                            have p15444_1 := h15444c.2.1
                            have p15444_2 := h15444c.2.2.1
                            have p15444_3 := h15444c.2.2.2
                            linarith only [h0, hlam, p15444_1]
                          · have p15444_0 := h15444c.1
                            have p15444_1 := h15444c.2.1
                            have p15444_2 := h15444c.2.2.1
                            have p15444_3 := h15444c.2.2.2
                            linarith only [h6793, hlam, p15444_0]
                          · have p15444_0 := h15444c.1
                            have p15444_1 := h15444c.2.1
                            have p15444_2 := h15444c.2.2.1
                            have p15444_3 := h15444c.2.2.2
                            linarith only [h10058, hlam, p15444_1]
                          · have p15444_0 := h15444c.1
                            have p15444_1 := h15444c.2.1
                            have p15444_2 := h15444c.2.2.1
                            have p15444_3 := h15444c.2.2.2
                            linarith only [h11024, hlam, p15444_1]
                          · have p15444_0 := h15444c.1
                            have p15444_1 := h15444c.2.1
                            have p15444_2 := h15444c.2.2.1
                            have p15444_3 := h15444c.2.2.2
                            linarith only [h11558, h15247, h15438, hc01, hc13, hlam, hphi, p15444_1]
                          · have p15444_0 := h15444c.1
                            have p15444_1 := h15444c.2.1
                            have p15444_2 := h15444c.2.2.1
                            have p15444_3 := h15444c.2.2.2
                            linarith only [hlam, p15444_0]
                          · have p15444_0 := h15444c.1
                            have p15444_1 := h15444c.2.1
                            have p15444_2 := h15444c.2.2.1
                            have p15444_3 := h15444c.2.2.2
                            linarith only [h11558, hlam, p15444_0]
                          · have p15444_0 := h15444c.1
                            have p15444_1 := h15444c.2.1
                            have p15444_2 := h15444c.2.2.1
                            have p15444_3 := h15444c.2.2.2
                            linarith only [h14803, hlam, p15444_1]
                          · have p15444_0 := h15444c.1
                            have p15444_1 := h15444c.2.1
                            have p15444_2 := h15444c.2.2.1
                            have p15444_3 := h15444c.2.2.2
                            linarith only [h11558, h15247, h15438, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p15444_1]
                          · have p15444_0 := h15444c.1
                            have p15444_1 := h15444c.2.1
                            have p15444_2 := h15444c.2.2.1
                            have p15444_3 := h15444c.2.2.2
                            linarith only [h15247, h15438, hc01, hc13, hlam, hphi, p15444_1]
                          · have p15444_0 := h15444c.1
                            have p15444_1 := h15444c.2.1
                            have p15444_2 := h15444c.2.2.1
                            have p15444_3 := h15444c.2.2.2
                            linarith only [h15247, h15438, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p15444_1]
                          · have p15444_0 := h15444c.1
                            have p15444_1 := h15444c.2.1
                            have p15444_2 := h15444c.2.2.1
                            have p15444_3 := h15444c.2.2.2
                            linarith only [hlam, p15444_0]
                          · have p15444_0 := h15444c.1
                            have p15444_1 := h15444c.2.1
                            have p15444_2 := h15444c.2.2.1
                            have p15444_3 := h15444c.2.2.2
                            linarith only [h15247, hlam, p15444_1]
                          · have p15444_0 := h15444c.1
                            have p15444_1 := h15444c.2.1
                            have p15444_2 := h15444c.2.2.1
                            have p15444_3 := h15444c.2.2.2
                            linarith only [h11024, h15247, h15438, hc01, hc13, hlam, hphi, p15444_1]
                          · have p15444_0 := h15444c.1
                            have p15444_1 := h15444c.2.1
                            have p15444_2 := h15444c.2.2.1
                            have p15444_3 := h15444c.2.2.2
                            linarith only [h15247, h15438, hc01, hc13, hlam, hphi, p15444_1]
                          · have p15444_0 := h15444c.1
                            have p15444_1 := h15444c.2.1
                            have p15444_2 := h15444c.2.2.1
                            have p15444_3 := h15444c.2.2.2
                            linarith only [h15246, h15441, h15443, hc45, hlam, hphi, ht0b, ht5b, p15444_1, u0elo3]
                          · have p15444_0 := h15444c.1
                            have p15444_1 := h15444c.2.1
                            have p15444_2 := h15444c.2.2.1
                            have p15444_3 := h15444c.2.2.2
                            linarith only [h15247, h15438, h6793, hc01, hc13, hlam, hphi, p15444_1]
                          · have p15444_0 := h15444c.1
                            have p15444_1 := h15444c.2.1
                            have p15444_2 := h15444c.2.2.1
                            have p15444_3 := h15444c.2.2.2
                            linarith only [hlam, p15444_0]
                          · have p15444_0 := h15444c.1
                            have p15444_1 := h15444c.2.1
                            have p15444_2 := h15444c.2.2.1
                            have p15444_3 := h15444c.2.2.2
                            linarith only [h11024, h15247, h15438, hc01, hc13, hlam, hphi, p15444_1]
                          · have p15444_0 := h15444c.1
                            have p15444_1 := h15444c.2.1
                            have p15444_2 := h15444c.2.2.1
                            have p15444_3 := h15444c.2.2.2
                            linarith only [h0, h15246, h15435, h15440, hc01, hc23, hlam, hphi, ht12, p15444_1]
                          · have p15444_0 := h15444c.1
                            have p15444_1 := h15444c.2.1
                            have p15444_2 := h15444c.2.2.1
                            have p15444_3 := h15444c.2.2.2
                            linarith only [h15246, hlam, p15444_1]
                          · have p15444_0 := h15444c.1
                            have p15444_1 := h15444c.2.1
                            have p15444_2 := h15444c.2.2.1
                            have p15444_3 := h15444c.2.2.2
                            linarith only [h15386, hlam, p15444_0]
                          · have p15444_0 := h15444c.1
                            have p15444_1 := h15444c.2.1
                            have p15444_2 := h15444c.2.2.1
                            have p15444_3 := h15444c.2.2.2
                            linarith only [h15387, hlam, p15444_1]
                          · have p15444_0 := h15444c.1
                            have p15444_1 := h15444c.2.1
                            have p15444_2 := h15444c.2.2.1
                            have p15444_3 := h15444c.2.2.2
                            linarith only [hlam, p15444_0]
                        · linarith only [h15247, h15387, h15443, hlam]
                      · linarith only [h14803, h15246, h15387, h15442, hlam]
                    · linarith only [h11558, h15247, h15388, h15438, h15441, hc02, hc35, hlam, hphi, ht23]
                  · linarith only [h15388, h15438, h15440, hlam]
                · linarith only [h11558, h15246, h15247, h15387, h15438, h15439, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h15475 | h15475
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15476 | h15476
                  · linarith only [h11024, h15388, h15437, h15438, h15476, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h11024, h15388, h15437, h15476, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h0, h10058, h15246, h15387, h15388, h15475, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h0, h15246, h15437, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
      · linarith only [h11558, h15246, h15247, h15387, hlam]
    · linarith only [h11558, h15246, h15386, hlam]

end R2N4
