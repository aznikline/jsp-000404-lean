import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5504000 in
set_option maxHeartbeats 5504000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s15_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg10058 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11024 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg11558 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg11559 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg11560 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h11561 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h12797 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h11558 := hg11558
  have h11559 := hg11559
  have h11560 := hg11560
  rcases m.htr 0 4 5 (by decide) (by decide) with h12798 | h12798
  · rcases m.htr 1 2 3 (by decide) (by decide) with h12799 | h12799
    · rcases m.htr 1 2 4 (by decide) (by decide) with h12800 | h12800
      · rcases m.htr 1 2 5 (by decide) (by decide) with h12801 | h12801
        · rcases m.htr 1 3 4 (by decide) (by decide) with h12802 | h12802
          · rcases m.htr 1 4 5 (by decide) (by decide) with h12803 | h12803
            · rcases m.htr 2 3 4 (by decide) (by decide) with h12804 | h12804
              · linarith only [h11558, h11561, h12804, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h12806 | h12806
                · rcases m.htr 2 4 5 (by decide) (by decide) with h12807 | h12807
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h12808 | h12808
                    · rcases h0bigk with h12809c | h12809c | h12809c | h12809c | h12809c | h12809c | h12809c | h12809c | h12809c | h12809c | h12809c | h12809c | h12809c | h12809c | h12809c | h12809c | h12809c | h12809c | h12809c | h12809c | h12809c | h12809c | h12809c | h12809c | h12809c
                      · have p12809_0 := h12809c.1
                        have p12809_1 := h12809c.2.1
                        have p12809_2 := h12809c.2.2.1
                        have p12809_3 := h12809c.2.2.2
                        linarith only [hlam, p12809_0]
                      · have p12809_0 := h12809c.1
                        have p12809_1 := h12809c.2.1
                        have p12809_2 := h12809c.2.2.1
                        have p12809_3 := h12809c.2.2.2
                        linarith only [h0, hlam, p12809_1]
                      · have p12809_0 := h12809c.1
                        have p12809_1 := h12809c.2.1
                        have p12809_2 := h12809c.2.2.1
                        have p12809_3 := h12809c.2.2.2
                        linarith only [h6793, hlam, p12809_0]
                      · have p12809_0 := h12809c.1
                        have p12809_1 := h12809c.2.1
                        have p12809_2 := h12809c.2.2.1
                        have p12809_3 := h12809c.2.2.2
                        linarith only [h10058, hlam, p12809_1]
                      · have p12809_0 := h12809c.1
                        have p12809_1 := h12809c.2.1
                        have p12809_2 := h12809c.2.2.1
                        have p12809_3 := h12809c.2.2.2
                        linarith only [h11024, hlam, p12809_1]
                      · have p12809_0 := h12809c.1
                        have p12809_1 := h12809c.2.1
                        have p12809_2 := h12809c.2.2.1
                        have p12809_3 := h12809c.2.2.2
                        rcases p12809_3 (m.d 0 1) (by simp) with h12815 | h12815
                        · linarith only [h0, h12815, hlam]
                        · rcases p12809_3 (m.d 0 2) (by simp) with h12817 | h12817
                          · rcases p12809_3 (m.d 0 3) (by simp) with h12818 | h12818
                            · linarith only [h11558, h12818, hlam]
                            · linarith only [h12818, h6793, hlam]
                          · linarith only [h0, h12817, hlam]
                      · have p12809_0 := h12809c.1
                        have p12809_1 := h12809c.2.1
                        have p12809_2 := h12809c.2.2.1
                        have p12809_3 := h12809c.2.2.2
                        linarith only [hlam, p12809_0]
                      · have p12809_0 := h12809c.1
                        have p12809_1 := h12809c.2.1
                        have p12809_2 := h12809c.2.2.1
                        have p12809_3 := h12809c.2.2.2
                        linarith only [h11558, h12806, h12808, hc45, hlam, hphi, ht0b, ht5b, p12809_1, u0elo1]
                      · have p12809_0 := h12809c.1
                        have p12809_1 := h12809c.2.1
                        have p12809_2 := h12809c.2.2.1
                        have p12809_3 := h12809c.2.2.2
                        linarith only [h11558, h11561, h12806, h12808, hc45, hlam, hphi, ht0b, ht5b, p12809_1, u0elo1]
                      · have p12809_0 := h12809c.1
                        have p12809_1 := h12809c.2.1
                        have p12809_2 := h12809c.2.2.1
                        have p12809_3 := h12809c.2.2.2
                        rcases p12809_3 (m.d 0 1) (by simp) with h12825 | h12825
                        · linarith only [h0, h12825, hlam]
                        · rcases p12809_3 (m.d 0 2) (by simp) with h12827 | h12827
                          · rcases p12809_3 (m.d 0 3) (by simp) with h12828 | h12828
                            · linarith only [h11558, h12828, hlam]
                            · linarith only [h12797, h12828, hlam]
                          · linarith only [h11560, h12827, hlam]
                      · have p12809_0 := h12809c.1
                        have p12809_1 := h12809c.2.1
                        have p12809_2 := h12809c.2.2.1
                        have p12809_3 := h12809c.2.2.2
                        linarith only [h11561, h12799, h12802, hc01, hc12, hlam, hphi, p12809_1]
                      · have p12809_0 := h12809c.1
                        have p12809_1 := h12809c.2.1
                        have p12809_2 := h12809c.2.2.1
                        have p12809_3 := h12809c.2.2.2
                        linarith only [h11558, hlam, p12809_1]
                      · have p12809_0 := h12809c.1
                        have p12809_1 := h12809c.2.1
                        have p12809_2 := h12809c.2.2.1
                        have p12809_3 := h12809c.2.2.2
                        linarith only [hlam, p12809_0]
                      · have p12809_0 := h12809c.1
                        have p12809_1 := h12809c.2.1
                        have p12809_2 := h12809c.2.2.1
                        have p12809_3 := h12809c.2.2.2
                        linarith only [h11561, hlam, p12809_1]
                      · have p12809_0 := h12809c.1
                        have p12809_1 := h12809c.2.1
                        have p12809_2 := h12809c.2.2.1
                        have p12809_3 := h12809c.2.2.2
                        linarith only [h11561, h12799, h12802, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p12809_1]
                      · have p12809_0 := h12809c.1
                        have p12809_1 := h12809c.2.1
                        have p12809_2 := h12809c.2.2.1
                        have p12809_3 := h12809c.2.2.2
                        linarith only [h11561, h12799, h12802, hc01, hc12, hlam, hphi, p12809_1]
                      · have p12809_0 := h12809c.1
                        have p12809_1 := h12809c.2.1
                        have p12809_2 := h12809c.2.2.1
                        have p12809_3 := h12809c.2.2.2
                        linarith only [h11559, hlam, p12809_0]
                      · have p12809_0 := h12809c.1
                        have p12809_1 := h12809c.2.1
                        have p12809_2 := h12809c.2.2.1
                        have p12809_3 := h12809c.2.2.2
                        linarith only [h11558, h11561, h12799, h12802, h12806, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p12809_1]
                      · have p12809_0 := h12809c.1
                        have p12809_1 := h12809c.2.1
                        have p12809_2 := h12809c.2.2.1
                        have p12809_3 := h12809c.2.2.2
                        linarith only [hlam, p12809_0]
                      · have p12809_0 := h12809c.1
                        have p12809_1 := h12809c.2.1
                        have p12809_2 := h12809c.2.2.1
                        have p12809_3 := h12809c.2.2.2
                        linarith only [h11024, h11561, h12799, h12802, hc01, hc12, hlam, hphi, p12809_1]
                      · have p12809_0 := h12809c.1
                        have p12809_1 := h12809c.2.1
                        have p12809_2 := h12809c.2.2.1
                        have p12809_3 := h12809c.2.2.2
                        linarith only [h11561, h12797, h12799, h12802, hc01, hc12, hlam, hphi, p12809_1]
                      · have p12809_0 := h12809c.1
                        have p12809_1 := h12809c.2.1
                        have p12809_2 := h12809c.2.2.1
                        have p12809_3 := h12809c.2.2.2
                        linarith only [h11560, hlam, p12809_1]
                      · have p12809_0 := h12809c.1
                        have p12809_1 := h12809c.2.1
                        have p12809_2 := h12809c.2.2.1
                        have p12809_3 := h12809c.2.2.2
                        linarith only [h12797, hlam, p12809_0]
                      · have p12809_0 := h12809c.1
                        have p12809_1 := h12809c.2.1
                        have p12809_2 := h12809c.2.2.1
                        have p12809_3 := h12809c.2.2.2
                        linarith only [h12798, hlam, p12809_1]
                      · have p12809_0 := h12809c.1
                        have p12809_1 := h12809c.2.1
                        have p12809_2 := h12809c.2.2.1
                        have p12809_3 := h12809c.2.2.2
                        linarith only [hlam, p12809_0]
                    · linarith only [h11559, h11561, h12798, h12808, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h11561, h12797, h12798, h12799, h12802, h12804, h12806, h12807, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h11561, h12797, h12799, h12802, h12806, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · linarith only [h10058, h11561, h12797, h12798, h12799, h12802, h12803, hc01, hc12, hlam, hphi]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h12851 | h12851
            · rcases m.htr 2 3 4 (by decide) (by decide) with h12852 | h12852
              · linarith only [h12802, h12852, h6793, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h12854 | h12854
                · rcases m.htr 2 4 5 (by decide) (by decide) with h12855 | h12855
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h12856 | h12856
                    · rcases h0bigk with h12857c | h12857c | h12857c | h12857c | h12857c | h12857c | h12857c | h12857c | h12857c | h12857c | h12857c | h12857c | h12857c | h12857c | h12857c | h12857c | h12857c | h12857c | h12857c | h12857c | h12857c | h12857c | h12857c | h12857c | h12857c
                      · have p12857_0 := h12857c.1
                        have p12857_1 := h12857c.2.1
                        have p12857_2 := h12857c.2.2.1
                        have p12857_3 := h12857c.2.2.2
                        linarith only [hlam, p12857_0]
                      · have p12857_0 := h12857c.1
                        have p12857_1 := h12857c.2.1
                        have p12857_2 := h12857c.2.2.1
                        have p12857_3 := h12857c.2.2.2
                        linarith only [h0, hlam, p12857_1]
                      · have p12857_0 := h12857c.1
                        have p12857_1 := h12857c.2.1
                        have p12857_2 := h12857c.2.2.1
                        have p12857_3 := h12857c.2.2.2
                        linarith only [h6793, hlam, p12857_0]
                      · have p12857_0 := h12857c.1
                        have p12857_1 := h12857c.2.1
                        have p12857_2 := h12857c.2.2.1
                        have p12857_3 := h12857c.2.2.2
                        linarith only [h10058, hlam, p12857_1]
                      · have p12857_0 := h12857c.1
                        have p12857_1 := h12857c.2.1
                        have p12857_2 := h12857c.2.2.1
                        have p12857_3 := h12857c.2.2.2
                        linarith only [h11024, hlam, p12857_1]
                      · have p12857_0 := h12857c.1
                        have p12857_1 := h12857c.2.1
                        have p12857_2 := h12857c.2.2.1
                        have p12857_3 := h12857c.2.2.2
                        rcases p12857_3 (m.d 0 1) (by simp) with h12863 | h12863
                        · linarith only [h0, h12863, hlam]
                        · rcases p12857_3 (m.d 0 2) (by simp) with h12865 | h12865
                          · rcases p12857_3 (m.d 0 3) (by simp) with h12866 | h12866
                            · linarith only [h11558, h12866, hlam]
                            · linarith only [h12866, h6793, hlam]
                          · linarith only [h0, h12865, hlam]
                      · have p12857_0 := h12857c.1
                        have p12857_1 := h12857c.2.1
                        have p12857_2 := h12857c.2.2.1
                        have p12857_3 := h12857c.2.2.2
                        linarith only [hlam, p12857_0]
                      · have p12857_0 := h12857c.1
                        have p12857_1 := h12857c.2.1
                        have p12857_2 := h12857c.2.2.1
                        have p12857_3 := h12857c.2.2.2
                        linarith only [h11558, h12854, h12856, hc45, hlam, hphi, ht0b, ht5b, p12857_1, u0elo1]
                      · have p12857_0 := h12857c.1
                        have p12857_1 := h12857c.2.1
                        have p12857_2 := h12857c.2.2.1
                        have p12857_3 := h12857c.2.2.2
                        linarith only [h11559, h12852, h12854, h12856, hc45, hlam, hphi, ht0b, ht5b, p12857_1, u0elo1]
                      · have p12857_0 := h12857c.1
                        have p12857_1 := h12857c.2.1
                        have p12857_2 := h12857c.2.2.1
                        have p12857_3 := h12857c.2.2.2
                        rcases p12857_3 (m.d 0 1) (by simp) with h12873 | h12873
                        · linarith only [h0, h12873, hlam]
                        · rcases p12857_3 (m.d 0 2) (by simp) with h12875 | h12875
                          · rcases p12857_3 (m.d 0 3) (by simp) with h12876 | h12876
                            · linarith only [h11558, h12876, hlam]
                            · linarith only [h12797, h12876, hlam]
                          · linarith only [h11560, h12875, hlam]
                      · have p12857_0 := h12857c.1
                        have p12857_1 := h12857c.2.1
                        have p12857_2 := h12857c.2.2.1
                        have p12857_3 := h12857c.2.2.2
                        linarith only [h12802, h6793, hc01, hc34, hlam, hphi, ht12, ht23, p12857_1]
                      · have p12857_0 := h12857c.1
                        have p12857_1 := h12857c.2.1
                        have p12857_2 := h12857c.2.2.1
                        have p12857_3 := h12857c.2.2.2
                        linarith only [h11558, hlam, p12857_1]
                      · have p12857_0 := h12857c.1
                        have p12857_1 := h12857c.2.1
                        have p12857_2 := h12857c.2.2.1
                        have p12857_3 := h12857c.2.2.2
                        linarith only [hlam, p12857_0]
                      · have p12857_0 := h12857c.1
                        have p12857_1 := h12857c.2.1
                        have p12857_2 := h12857c.2.2.1
                        have p12857_3 := h12857c.2.2.2
                        linarith only [h11561, hlam, p12857_1]
                      · have p12857_0 := h12857c.1
                        have p12857_1 := h12857c.2.1
                        have p12857_2 := h12857c.2.2.1
                        have p12857_3 := h12857c.2.2.2
                        linarith only [h11024, h12802, h6793, hc01, hc34, hlam, hphi, ht12, ht23, p12857_1]
                      · have p12857_0 := h12857c.1
                        have p12857_1 := h12857c.2.1
                        have p12857_2 := h12857c.2.2.1
                        have p12857_3 := h12857c.2.2.2
                        rcases p12857_3 (m.d 0 1) (by simp) with h12885 | h12885
                        · linarith only [h10058, h12885, hlam]
                        · rcases p12857_3 (m.d 0 2) (by simp) with h12887 | h12887
                          · rcases p12857_3 (m.d 0 3) (by simp) with h12888 | h12888
                            · linarith only [h11561, h12888, hlam]
                            · linarith only [h12888, h6793, hlam]
                          · linarith only [h0, h12887, hlam]
                      · have p12857_0 := h12857c.1
                        have p12857_1 := h12857c.2.1
                        have p12857_2 := h12857c.2.2.1
                        have p12857_3 := h12857c.2.2.2
                        linarith only [h11559, hlam, p12857_0]
                      · have p12857_0 := h12857c.1
                        have p12857_1 := h12857c.2.1
                        have p12857_2 := h12857c.2.2.1
                        have p12857_3 := h12857c.2.2.2
                        linarith only [h11558, h11559, h12854, h12856, hc45, hlam, hphi, ht0b, ht5b, p12857_1, u0elo1]
                      · have p12857_0 := h12857c.1
                        have p12857_1 := h12857c.2.1
                        have p12857_2 := h12857c.2.2.1
                        have p12857_3 := h12857c.2.2.2
                        linarith only [hlam, p12857_0]
                      · have p12857_0 := h12857c.1
                        have p12857_1 := h12857c.2.1
                        have p12857_2 := h12857c.2.2.1
                        have p12857_3 := h12857c.2.2.2
                        rcases p12857_3 (m.d 0 1) (by simp) with h12895 | h12895
                        · linarith only [h10058, h12895, hlam]
                        · rcases p12857_3 (m.d 0 2) (by simp) with h12897 | h12897
                          · rcases p12857_3 (m.d 0 3) (by simp) with h12898 | h12898
                            · linarith only [h11561, h12898, hlam]
                            · linarith only [h12797, h12898, hlam]
                          · linarith only [h11560, h12897, hlam]
                      · have p12857_0 := h12857c.1
                        have p12857_1 := h12857c.2.1
                        have p12857_2 := h12857c.2.2.1
                        have p12857_3 := h12857c.2.2.2
                        linarith only [h12797, h12802, h6793, hc01, hc34, hlam, hphi, ht12, ht23, p12857_1]
                      · have p12857_0 := h12857c.1
                        have p12857_1 := h12857c.2.1
                        have p12857_2 := h12857c.2.2.1
                        have p12857_3 := h12857c.2.2.2
                        linarith only [h11560, hlam, p12857_1]
                      · have p12857_0 := h12857c.1
                        have p12857_1 := h12857c.2.1
                        have p12857_2 := h12857c.2.2.1
                        have p12857_3 := h12857c.2.2.2
                        linarith only [h12797, hlam, p12857_0]
                      · have p12857_0 := h12857c.1
                        have p12857_1 := h12857c.2.1
                        have p12857_2 := h12857c.2.2.1
                        have p12857_3 := h12857c.2.2.2
                        linarith only [h12798, hlam, p12857_1]
                      · have p12857_0 := h12857c.1
                        have p12857_1 := h12857c.2.1
                        have p12857_2 := h12857c.2.2.1
                        have p12857_3 := h12857c.2.2.2
                        linarith only [hlam, p12857_0]
                    · linarith only [h12802, h12856, h6793, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h11559, h12798, h12852, h12854, h12855, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                · linarith only [h12797, h12802, h12854, h6793, hc23, hc34, hlam, hphi]
            · linarith only [h10058, h12798, h12851, hlam]
        · linarith only [h0, h11560, h12801, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
      · linarith only [h0, h11559, h12800, hlam]
    · linarith only [h0, h11558, h12799, hlam]
  · linarith only [h11561, h12797, h12798, hlam]

end R2N4
