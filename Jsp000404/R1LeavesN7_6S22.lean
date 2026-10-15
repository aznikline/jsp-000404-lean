import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5504000 in
set_option maxHeartbeats 5504000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s15_x1_x1_x0 (m : N7Model)
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
    (h12797 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h12915 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h12916 | h12916
  · rcases m.htr 1 2 4 (by decide) (by decide) with h12917 | h12917
    · rcases m.htr 1 2 5 (by decide) (by decide) with h12918 | h12918
      · rcases m.htr 1 3 4 (by decide) (by decide) with h12919 | h12919
        · rcases m.htr 1 4 5 (by decide) (by decide) with h12920 | h12920
          · rcases m.htr 2 3 4 (by decide) (by decide) with h12921 | h12921
            · linarith only [h11558, h11561, h12921, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h12923 | h12923
              · linarith only [h11558, h12797, h12923, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h12925 | h12925
                · rcases m.htr 3 4 5 (by decide) (by decide) with h12926 | h12926
                  · rcases h0bigk with h12927c | h12927c | h12927c | h12927c | h12927c | h12927c | h12927c | h12927c | h12927c | h12927c | h12927c | h12927c | h12927c | h12927c | h12927c | h12927c | h12927c | h12927c | h12927c | h12927c | h12927c | h12927c | h12927c | h12927c | h12927c
                    · have p12927_0 := h12927c.1
                      have p12927_1 := h12927c.2.1
                      have p12927_2 := h12927c.2.2.1
                      have p12927_3 := h12927c.2.2.2
                      linarith only [hlam, p12927_0]
                    · have p12927_0 := h12927c.1
                      have p12927_1 := h12927c.2.1
                      have p12927_2 := h12927c.2.2.1
                      have p12927_3 := h12927c.2.2.2
                      linarith only [h0, hlam, p12927_1]
                    · have p12927_0 := h12927c.1
                      have p12927_1 := h12927c.2.1
                      have p12927_2 := h12927c.2.2.1
                      have p12927_3 := h12927c.2.2.2
                      linarith only [h6793, hlam, p12927_0]
                    · have p12927_0 := h12927c.1
                      have p12927_1 := h12927c.2.1
                      have p12927_2 := h12927c.2.2.1
                      have p12927_3 := h12927c.2.2.2
                      linarith only [h10058, hlam, p12927_1]
                    · have p12927_0 := h12927c.1
                      have p12927_1 := h12927c.2.1
                      have p12927_2 := h12927c.2.2.1
                      have p12927_3 := h12927c.2.2.2
                      linarith only [h11024, hlam, p12927_1]
                    · have p12927_0 := h12927c.1
                      have p12927_1 := h12927c.2.1
                      have p12927_2 := h12927c.2.2.1
                      have p12927_3 := h12927c.2.2.2
                      rcases p12927_3 (m.d 0 1) (by simp) with h12933 | h12933
                      · linarith only [h0, h12933, hlam]
                      · rcases p12927_3 (m.d 0 2) (by simp) with h12935 | h12935
                        · rcases p12927_3 (m.d 0 3) (by simp) with h12936 | h12936
                          · linarith only [h11558, h12936, hlam]
                          · linarith only [h12936, h6793, hlam]
                        · linarith only [h0, h12935, hlam]
                    · have p12927_0 := h12927c.1
                      have p12927_1 := h12927c.2.1
                      have p12927_2 := h12927c.2.2.1
                      have p12927_3 := h12927c.2.2.2
                      linarith only [hlam, p12927_0]
                    · have p12927_0 := h12927c.1
                      have p12927_1 := h12927c.2.1
                      have p12927_2 := h12927c.2.2.1
                      have p12927_3 := h12927c.2.2.2
                      rcases p12927_3 (m.d 0 1) (by simp) with h12941 | h12941
                      · linarith only [h0, h12941, hlam]
                      · rcases p12927_3 (m.d 0 2) (by simp) with h12943 | h12943
                        · rcases p12927_3 (m.d 0 3) (by simp) with h12944 | h12944
                          · linarith only [h11558, h12944, hlam]
                          · rcases p12927_3 (m.d 0 4) (by simp) with h12946 | h12946
                            · linarith only [h11559, h12946, hlam]
                            · linarith only [h11561, h12946, hlam]
                        · linarith only [h11558, h12943, hlam]
                    · have p12927_0 := h12927c.1
                      have p12927_1 := h12927c.2.1
                      have p12927_2 := h12927c.2.2.1
                      have p12927_3 := h12927c.2.2.2
                      linarith only [h11559, h12925, hc45, hlam, hphi, ht0b, ht5b, p12927_1, u0elo1]
                    · have p12927_0 := h12927c.1
                      have p12927_1 := h12927c.2.1
                      have p12927_2 := h12927c.2.2.1
                      have p12927_3 := h12927c.2.2.2
                      rcases p12927_3 (m.d 0 1) (by simp) with h12951 | h12951
                      · linarith only [h0, h12951, hlam]
                      · rcases p12927_3 (m.d 0 2) (by simp) with h12953 | h12953
                        · rcases p12927_3 (m.d 0 3) (by simp) with h12954 | h12954
                          · linarith only [h11558, h12954, hlam]
                          · rcases p12927_3 (m.d 0 4) (by simp) with h12956 | h12956
                            · linarith only [h11559, h12956, hlam]
                            · linarith only [h12915, h12956, hlam]
                        · linarith only [h11560, h12953, hlam]
                    · have p12927_0 := h12927c.1
                      have p12927_1 := h12927c.2.1
                      have p12927_2 := h12927c.2.2.1
                      have p12927_3 := h12927c.2.2.2
                      linarith only [h12797, h12919, h12926, hc01, hc13, hlam, hphi, p12927_1]
                    · have p12927_0 := h12927c.1
                      have p12927_1 := h12927c.2.1
                      have p12927_2 := h12927c.2.2.1
                      have p12927_3 := h12927c.2.2.2
                      linarith only [h11558, hlam, p12927_1]
                    · have p12927_0 := h12927c.1
                      have p12927_1 := h12927c.2.1
                      have p12927_2 := h12927c.2.2.1
                      have p12927_3 := h12927c.2.2.2
                      linarith only [hlam, p12927_0]
                    · have p12927_0 := h12927c.1
                      have p12927_1 := h12927c.2.1
                      have p12927_2 := h12927c.2.2.1
                      have p12927_3 := h12927c.2.2.2
                      linarith only [h11561, hlam, p12927_1]
                    · have p12927_0 := h12927c.1
                      have p12927_1 := h12927c.2.1
                      have p12927_2 := h12927c.2.2.1
                      have p12927_3 := h12927c.2.2.2
                      linarith only [h12797, hlam, p12927_1]
                    · have p12927_0 := h12927c.1
                      have p12927_1 := h12927c.2.1
                      have p12927_2 := h12927c.2.2.1
                      have p12927_3 := h12927c.2.2.2
                      linarith only [h11561, h12919, hc01, hc13, hlam, hphi, p12927_1]
                    · have p12927_0 := h12927c.1
                      have p12927_1 := h12927c.2.1
                      have p12927_2 := h12927c.2.2.1
                      have p12927_3 := h12927c.2.2.2
                      linarith only [h11559, hlam, p12927_0]
                    · have p12927_0 := h12927c.1
                      have p12927_1 := h12927c.2.1
                      have p12927_2 := h12927c.2.2.1
                      have p12927_3 := h12927c.2.2.2
                      linarith only [h11561, h12919, h6793, hc01, hc13, hlam, hphi, p12927_1]
                    · have p12927_0 := h12927c.1
                      have p12927_1 := h12927c.2.1
                      have p12927_2 := h12927c.2.2.1
                      have p12927_3 := h12927c.2.2.2
                      linarith only [hlam, p12927_0]
                    · have p12927_0 := h12927c.1
                      have p12927_1 := h12927c.2.1
                      have p12927_2 := h12927c.2.2.1
                      have p12927_3 := h12927c.2.2.2
                      linarith only [h11561, h12797, h12919, h6793, hc01, hc13, hlam, hphi, p12927_1]
                    · have p12927_0 := h12927c.1
                      have p12927_1 := h12927c.2.1
                      have p12927_2 := h12927c.2.2.1
                      have p12927_3 := h12927c.2.2.2
                      linarith only [h12797, h12919, h12926, hc01, hc13, hlam, hphi, p12927_1]
                    · have p12927_0 := h12927c.1
                      have p12927_1 := h12927c.2.1
                      have p12927_2 := h12927c.2.2.1
                      have p12927_3 := h12927c.2.2.2
                      linarith only [h11560, hlam, p12927_1]
                    · have p12927_0 := h12927c.1
                      have p12927_1 := h12927c.2.1
                      have p12927_2 := h12927c.2.2.1
                      have p12927_3 := h12927c.2.2.2
                      linarith only [h12797, h12919, h12926, h6793, hc01, hc13, hlam, hphi, p12927_1]
                    · have p12927_0 := h12927c.1
                      have p12927_1 := h12927c.2.1
                      have p12927_2 := h12927c.2.2.1
                      have p12927_3 := h12927c.2.2.2
                      linarith only [h12915, hlam, p12927_1]
                    · have p12927_0 := h12927c.1
                      have p12927_1 := h12927c.2.1
                      have p12927_2 := h12927c.2.2.1
                      have p12927_3 := h12927c.2.2.2
                      linarith only [hlam, p12927_0]
                  · linarith only [h11561, h12915, h12926, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h12976 | h12976
                  · rcases h0bigk with h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c | h12977c
                    · have p12977_0 := h12977c.1
                      have p12977_1 := h12977c.2.1
                      have p12977_2 := h12977c.2.2.1
                      have p12977_3 := h12977c.2.2.2
                      linarith only [hlam, p12977_0]
                    · have p12977_0 := h12977c.1
                      have p12977_1 := h12977c.2.1
                      have p12977_2 := h12977c.2.2.1
                      have p12977_3 := h12977c.2.2.2
                      linarith only [h0, hlam, p12977_1]
                    · have p12977_0 := h12977c.1
                      have p12977_1 := h12977c.2.1
                      have p12977_2 := h12977c.2.2.1
                      have p12977_3 := h12977c.2.2.2
                      linarith only [h6793, hlam, p12977_0]
                    · have p12977_0 := h12977c.1
                      have p12977_1 := h12977c.2.1
                      have p12977_2 := h12977c.2.2.1
                      have p12977_3 := h12977c.2.2.2
                      linarith only [h10058, hlam, p12977_1]
                    · have p12977_0 := h12977c.1
                      have p12977_1 := h12977c.2.1
                      have p12977_2 := h12977c.2.2.1
                      have p12977_3 := h12977c.2.2.2
                      linarith only [h11024, hlam, p12977_1]
                    · have p12977_0 := h12977c.1
                      have p12977_1 := h12977c.2.1
                      have p12977_2 := h12977c.2.2.1
                      have p12977_3 := h12977c.2.2.2
                      rcases p12977_3 (m.d 0 1) (by simp) with h12983 | h12983
                      · linarith only [h0, h12983, hlam]
                      · rcases p12977_3 (m.d 0 2) (by simp) with h12985 | h12985
                        · rcases p12977_3 (m.d 0 3) (by simp) with h12986 | h12986
                          · linarith only [h11558, h12986, hlam]
                          · linarith only [h12986, h6793, hlam]
                        · linarith only [h0, h12985, hlam]
                    · have p12977_0 := h12977c.1
                      have p12977_1 := h12977c.2.1
                      have p12977_2 := h12977c.2.2.1
                      have p12977_3 := h12977c.2.2.2
                      linarith only [hlam, p12977_0]
                    · have p12977_0 := h12977c.1
                      have p12977_1 := h12977c.2.1
                      have p12977_2 := h12977c.2.2.1
                      have p12977_3 := h12977c.2.2.2
                      rcases p12977_3 (m.d 0 1) (by simp) with h12991 | h12991
                      · linarith only [h0, h12991, hlam]
                      · rcases p12977_3 (m.d 0 2) (by simp) with h12993 | h12993
                        · rcases p12977_3 (m.d 0 3) (by simp) with h12994 | h12994
                          · linarith only [h11558, h12994, hlam]
                          · rcases p12977_3 (m.d 0 4) (by simp) with h12996 | h12996
                            · linarith only [h11559, h12996, hlam]
                            · linarith only [h11561, h12996, hlam]
                        · linarith only [h11558, h12993, hlam]
                    · have p12977_0 := h12977c.1
                      have p12977_1 := h12977c.2.1
                      have p12977_2 := h12977c.2.2.1
                      have p12977_3 := h12977c.2.2.2
                      linarith only [h12915, h12921, h12925, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12977_1, u0elo1]
                    · have p12977_0 := h12977c.1
                      have p12977_1 := h12977c.2.1
                      have p12977_2 := h12977c.2.2.1
                      have p12977_3 := h12977c.2.2.2
                      linarith only [h12915, h12921, h12925, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12977_1, u0elo1]
                    · have p12977_0 := h12977c.1
                      have p12977_1 := h12977c.2.1
                      have p12977_2 := h12977c.2.2.1
                      have p12977_3 := h12977c.2.2.2
                      linarith only [h11561, h12797, h12915, h12916, h12919, h12921, h12925, hc01, hc12, hc23, hc35, hlam, hphi, p12977_1]
                    · have p12977_0 := h12977c.1
                      have p12977_1 := h12977c.2.1
                      have p12977_2 := h12977c.2.2.1
                      have p12977_3 := h12977c.2.2.2
                      linarith only [h11558, hlam, p12977_1]
                    · have p12977_0 := h12977c.1
                      have p12977_1 := h12977c.2.1
                      have p12977_2 := h12977c.2.2.1
                      have p12977_3 := h12977c.2.2.2
                      linarith only [hlam, p12977_0]
                    · have p12977_0 := h12977c.1
                      have p12977_1 := h12977c.2.1
                      have p12977_2 := h12977c.2.2.1
                      have p12977_3 := h12977c.2.2.2
                      linarith only [h11561, hlam, p12977_1]
                    · have p12977_0 := h12977c.1
                      have p12977_1 := h12977c.2.1
                      have p12977_2 := h12977c.2.2.1
                      have p12977_3 := h12977c.2.2.2
                      linarith only [h12797, hlam, p12977_1]
                    · have p12977_0 := h12977c.1
                      have p12977_1 := h12977c.2.1
                      have p12977_2 := h12977c.2.2.1
                      have p12977_3 := h12977c.2.2.2
                      linarith only [h11561, h12916, h12919, hc01, hc12, hlam, hphi, p12977_1]
                    · have p12977_0 := h12977c.1
                      have p12977_1 := h12977c.2.1
                      have p12977_2 := h12977c.2.2.1
                      have p12977_3 := h12977c.2.2.2
                      linarith only [h11559, hlam, p12977_0]
                    · have p12977_0 := h12977c.1
                      have p12977_1 := h12977c.2.1
                      have p12977_2 := h12977c.2.2.1
                      have p12977_3 := h12977c.2.2.2
                      linarith only [h11561, h12916, h12919, h6793, hc01, hc12, hlam, hphi, p12977_1]
                    · have p12977_0 := h12977c.1
                      have p12977_1 := h12977c.2.1
                      have p12977_2 := h12977c.2.2.1
                      have p12977_3 := h12977c.2.2.2
                      linarith only [hlam, p12977_0]
                    · have p12977_0 := h12977c.1
                      have p12977_1 := h12977c.2.1
                      have p12977_2 := h12977c.2.2.1
                      have p12977_3 := h12977c.2.2.2
                      linarith only [h11024, h11561, h12916, h12919, hc01, hc12, hlam, hphi, p12977_1]
                    · have p12977_0 := h12977c.1
                      have p12977_1 := h12977c.2.1
                      have p12977_2 := h12977c.2.2.1
                      have p12977_3 := h12977c.2.2.2
                      linarith only [h11561, h12915, h12916, h12919, hc01, hc12, hlam, hphi, p12977_1]
                    · have p12977_0 := h12977c.1
                      have p12977_1 := h12977c.2.1
                      have p12977_2 := h12977c.2.2.1
                      have p12977_3 := h12977c.2.2.2
                      linarith only [h11560, hlam, p12977_1]
                    · have p12977_0 := h12977c.1
                      have p12977_1 := h12977c.2.1
                      have p12977_2 := h12977c.2.2.1
                      have p12977_3 := h12977c.2.2.2
                      linarith only [h11561, h12915, h12916, h12919, h6793, hc01, hc12, hlam, hphi, p12977_1]
                    · have p12977_0 := h12977c.1
                      have p12977_1 := h12977c.2.1
                      have p12977_2 := h12977c.2.2.1
                      have p12977_3 := h12977c.2.2.2
                      linarith only [h12915, hlam, p12977_1]
                    · have p12977_0 := h12977c.1
                      have p12977_1 := h12977c.2.1
                      have p12977_2 := h12977c.2.2.1
                      have p12977_3 := h12977c.2.2.2
                      linarith only [hlam, p12977_0]
                  · linarith only [h11561, h12915, h12976, hlam]
          · linarith only [h11561, h12915, h12919, h12920, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h13019 | h13019
          · rcases m.htr 2 3 4 (by decide) (by decide) with h13020 | h13020
            · linarith only [h12919, h13020, h6793, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h13022 | h13022
              · linarith only [h11558, h12797, h13022, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h13024 | h13024
                · rcases m.htr 3 4 5 (by decide) (by decide) with h13025 | h13025
                  · rcases h0bigk with h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c | h13026c
                    · have p13026_0 := h13026c.1
                      have p13026_1 := h13026c.2.1
                      have p13026_2 := h13026c.2.2.1
                      have p13026_3 := h13026c.2.2.2
                      linarith only [hlam, p13026_0]
                    · have p13026_0 := h13026c.1
                      have p13026_1 := h13026c.2.1
                      have p13026_2 := h13026c.2.2.1
                      have p13026_3 := h13026c.2.2.2
                      linarith only [h0, hlam, p13026_1]
                    · have p13026_0 := h13026c.1
                      have p13026_1 := h13026c.2.1
                      have p13026_2 := h13026c.2.2.1
                      have p13026_3 := h13026c.2.2.2
                      linarith only [h6793, hlam, p13026_0]
                    · have p13026_0 := h13026c.1
                      have p13026_1 := h13026c.2.1
                      have p13026_2 := h13026c.2.2.1
                      have p13026_3 := h13026c.2.2.2
                      linarith only [h10058, hlam, p13026_1]
                    · have p13026_0 := h13026c.1
                      have p13026_1 := h13026c.2.1
                      have p13026_2 := h13026c.2.2.1
                      have p13026_3 := h13026c.2.2.2
                      linarith only [h11024, hlam, p13026_1]
                    · have p13026_0 := h13026c.1
                      have p13026_1 := h13026c.2.1
                      have p13026_2 := h13026c.2.2.1
                      have p13026_3 := h13026c.2.2.2
                      rcases p13026_3 (m.d 0 1) (by simp) with h13032 | h13032
                      · linarith only [h0, h13032, hlam]
                      · rcases p13026_3 (m.d 0 2) (by simp) with h13034 | h13034
                        · rcases p13026_3 (m.d 0 3) (by simp) with h13035 | h13035
                          · linarith only [h11558, h13035, hlam]
                          · linarith only [h13035, h6793, hlam]
                        · linarith only [h0, h13034, hlam]
                    · have p13026_0 := h13026c.1
                      have p13026_1 := h13026c.2.1
                      have p13026_2 := h13026c.2.2.1
                      have p13026_3 := h13026c.2.2.2
                      linarith only [hlam, p13026_0]
                    · have p13026_0 := h13026c.1
                      have p13026_1 := h13026c.2.1
                      have p13026_2 := h13026c.2.2.1
                      have p13026_3 := h13026c.2.2.2
                      rcases p13026_3 (m.d 0 1) (by simp) with h13040 | h13040
                      · linarith only [h0, h13040, hlam]
                      · rcases p13026_3 (m.d 0 2) (by simp) with h13042 | h13042
                        · rcases p13026_3 (m.d 0 3) (by simp) with h13043 | h13043
                          · linarith only [h11558, h13043, hlam]
                          · rcases p13026_3 (m.d 0 4) (by simp) with h13045 | h13045
                            · linarith only [h11559, h13045, hlam]
                            · linarith only [h11561, h13045, hlam]
                        · linarith only [h11558, h13042, hlam]
                    · have p13026_0 := h13026c.1
                      have p13026_1 := h13026c.2.1
                      have p13026_2 := h13026c.2.2.1
                      have p13026_3 := h13026c.2.2.2
                      linarith only [h11559, h13024, hc45, hlam, hphi, ht0b, ht5b, p13026_1, u0elo1]
                    · have p13026_0 := h13026c.1
                      have p13026_1 := h13026c.2.1
                      have p13026_2 := h13026c.2.2.1
                      have p13026_3 := h13026c.2.2.2
                      rcases p13026_3 (m.d 0 1) (by simp) with h13050 | h13050
                      · linarith only [h0, h13050, hlam]
                      · rcases p13026_3 (m.d 0 2) (by simp) with h13052 | h13052
                        · rcases p13026_3 (m.d 0 3) (by simp) with h13053 | h13053
                          · linarith only [h11558, h13053, hlam]
                          · rcases p13026_3 (m.d 0 4) (by simp) with h13055 | h13055
                            · linarith only [h11559, h13055, hlam]
                            · linarith only [h12915, h13055, hlam]
                        · linarith only [h11560, h13052, hlam]
                    · have p13026_0 := h13026c.1
                      have p13026_1 := h13026c.2.1
                      have p13026_2 := h13026c.2.2.1
                      have p13026_3 := h13026c.2.2.2
                      linarith only [h12797, hc01, hc35, hlam, hphi, ht12, ht23, p13026_1]
                    · have p13026_0 := h13026c.1
                      have p13026_1 := h13026c.2.1
                      have p13026_2 := h13026c.2.2.1
                      have p13026_3 := h13026c.2.2.2
                      linarith only [h11558, hlam, p13026_1]
                    · have p13026_0 := h13026c.1
                      have p13026_1 := h13026c.2.1
                      have p13026_2 := h13026c.2.2.1
                      have p13026_3 := h13026c.2.2.2
                      linarith only [hlam, p13026_0]
                    · have p13026_0 := h13026c.1
                      have p13026_1 := h13026c.2.1
                      have p13026_2 := h13026c.2.2.1
                      have p13026_3 := h13026c.2.2.2
                      linarith only [h11561, hlam, p13026_1]
                    · have p13026_0 := h13026c.1
                      have p13026_1 := h13026c.2.1
                      have p13026_2 := h13026c.2.2.1
                      have p13026_3 := h13026c.2.2.2
                      linarith only [h12797, hlam, p13026_1]
                    · have p13026_0 := h13026c.1
                      have p13026_1 := h13026c.2.1
                      have p13026_2 := h13026c.2.2.1
                      have p13026_3 := h13026c.2.2.2
                      rcases p13026_3 (m.d 0 1) (by simp) with h13064 | h13064
                      · linarith only [h10058, h13064, hlam]
                      · rcases p13026_3 (m.d 0 2) (by simp) with h13066 | h13066
                        · rcases p13026_3 (m.d 0 3) (by simp) with h13067 | h13067
                          · linarith only [h11561, h13067, hlam]
                          · linarith only [h13067, h6793, hlam]
                        · linarith only [h0, h13066, hlam]
                    · have p13026_0 := h13026c.1
                      have p13026_1 := h13026c.2.1
                      have p13026_2 := h13026c.2.2.1
                      have p13026_3 := h13026c.2.2.2
                      linarith only [h11559, hlam, p13026_0]
                    · have p13026_0 := h13026c.1
                      have p13026_1 := h13026c.2.1
                      have p13026_2 := h13026c.2.2.1
                      have p13026_3 := h13026c.2.2.2
                      rcases p13026_3 (m.d 0 1) (by simp) with h13072 | h13072
                      · linarith only [h10058, h13072, hlam]
                      · rcases p13026_3 (m.d 0 2) (by simp) with h13074 | h13074
                        · rcases p13026_3 (m.d 0 3) (by simp) with h13075 | h13075
                          · linarith only [h11561, h13075, hlam]
                          · rcases p13026_3 (m.d 0 4) (by simp) with h13077 | h13077
                            · rcases p13026_3 (m.d 0 5) (by simp) with h13078 | h13078
                              · linarith only [h12915, h13078, hlam]
                              · linarith only [h12797, h13078, hlam]
                            · linarith only [h11561, h13077, hlam]
                        · linarith only [h11558, h13074, hlam]
                    · have p13026_0 := h13026c.1
                      have p13026_1 := h13026c.2.1
                      have p13026_2 := h13026c.2.2.1
                      have p13026_3 := h13026c.2.2.2
                      linarith only [hlam, p13026_0]
                    · have p13026_0 := h13026c.1
                      have p13026_1 := h13026c.2.1
                      have p13026_2 := h13026c.2.2.1
                      have p13026_3 := h13026c.2.2.2
                      rcases p13026_3 (m.d 0 1) (by simp) with h13084 | h13084
                      · linarith only [h10058, h13084, hlam]
                      · rcases p13026_3 (m.d 0 2) (by simp) with h13086 | h13086
                        · rcases p13026_3 (m.d 0 3) (by simp) with h13087 | h13087
                          · linarith only [h11561, h13087, hlam]
                          · rcases p13026_3 (m.d 0 4) (by simp) with h13089 | h13089
                            · rcases p13026_3 (m.d 0 5) (by simp) with h13090 | h13090
                              · linarith only [h12915, h13090, hlam]
                              · rcases h0emin with h13092 | h13092 | h13092 | h13092 | h13092
                                · linarith only [h12919, h13092, h6793, hc34, hlam, ht01, ht12, ht23]
                                · rcases h2bigk with h13094c | h13094c | h13094c | h13094c | h13094c | h13094c | h13094c | h13094c | h13094c | h13094c | h13094c | h13094c | h13094c | h13094c | h13094c | h13094c | h13094c | h13094c | h13094c | h13094c | h13094c | h13094c | h13094c | h13094c | h13094c
                                  · have p13094_0 := h13094c.1
                                    have p13094_1 := h13094c.2.1
                                    have p13094_2 := h13094c.2.2.1
                                    have p13094_3 := h13094c.2.2.2
                                    linarith only [hlam, p13094_0]
                                  · have p13094_0 := h13094c.1
                                    have p13094_1 := h13094c.2.1
                                    have p13094_2 := h13094c.2.2.1
                                    have p13094_3 := h13094c.2.2.2
                                    linarith only [h0, hlam, p13094_1]
                                  · have p13094_0 := h13094c.1
                                    have p13094_1 := h13094c.2.1
                                    have p13094_2 := h13094c.2.2.1
                                    have p13094_3 := h13094c.2.2.2
                                    rcases p13094_3 (m.d 0 2) (by simp) with h13097 | h13097
                                    · rcases p13094_3 (m.d 1 2) (by simp) with h13098 | h13098
                                      · rcases p13094_3 (m.d 2 3) (by simp) with h13099 | h13099
                                        · linarith only [h13099, hlam, p13094_0]
                                        · rcases p13094_3 (m.d 2 4) (by simp) with h13101 | h13101
                                          · linarith only [h11559, h13101, hlam]
                                          · linarith only [h13020, h13101, hlam]
                                      · linarith only [h12916, h13098, hlam]
                                    · linarith only [h13097, hlam, p13094_0]
                                  · have p13094_0 := h13094c.1
                                    have p13094_1 := h13094c.2.1
                                    have p13094_2 := h13094c.2.2.1
                                    have p13094_3 := h13094c.2.2.2
                                    linarith only [h13024, hc45, hlam, hphi, ht0b, ht5b, p13094_1, u0elo1]
                                  · have p13094_0 := h13094c.1
                                    have p13094_1 := h13094c.2.1
                                    have p13094_2 := h13094c.2.2.1
                                    have p13094_3 := h13094c.2.2.2
                                    rcases p13094_3 (m.d 0 2) (by simp) with h13107 | h13107
                                    · rcases p13094_3 (m.d 1 2) (by simp) with h13108 | h13108
                                      · rcases p13094_3 (m.d 2 3) (by simp) with h13109 | h13109
                                        · linarith only [h11558, h13109, hlam]
                                        · rcases p13094_3 (m.d 2 4) (by simp) with h13111 | h13111
                                          · linarith only [h11559, h13111, hlam]
                                          · linarith only [h13024, h13111, hlam]
                                      · linarith only [h12918, h13108, hlam]
                                    · linarith only [h13107, hlam, p13094_0]
                                  · have p13094_0 := h13094c.1
                                    have p13094_1 := h13094c.2.1
                                    have p13094_2 := h13094c.2.2.1
                                    have p13094_3 := h13094c.2.2.2
                                    linarith only [h11559, h12797, h6793, hc01, hc12, hlam, hphi, p13026_1, p13094_1]
                                  · have p13094_0 := h13094c.1
                                    have p13094_1 := h13094c.2.1
                                    have p13094_2 := h13094c.2.2.1
                                    have p13094_3 := h13094c.2.2.2
                                    linarith only [hlam, p13094_0]
                                  · have p13094_0 := h13094c.1
                                    have p13094_1 := h13094c.2.1
                                    have p13094_2 := h13094c.2.2.1
                                    have p13094_3 := h13094c.2.2.2
                                    rcases p13094_3 (m.d 0 2) (by simp) with h13118 | h13118
                                    · linarith only [h0, h13118, hlam]
                                    · linarith only [h11558, h13118, hlam]
                                  · have p13094_0 := h13094c.1
                                    have p13094_1 := h13094c.2.1
                                    have p13094_2 := h13094c.2.2.1
                                    have p13094_3 := h13094c.2.2.2
                                    rcases p13094_3 (m.d 0 2) (by simp) with h13121 | h13121
                                    · linarith only [h0, h13121, hlam]
                                    · linarith only [h11559, h13121, hlam]
                                  · have p13094_0 := h13094c.1
                                    have p13094_1 := h13094c.2.1
                                    have p13094_2 := h13094c.2.2.1
                                    have p13094_3 := h13094c.2.2.2
                                    rcases p13094_3 (m.d 0 2) (by simp) with h13124 | h13124
                                    · linarith only [h0, h13124, hlam]
                                    · linarith only [h11560, h13124, hlam]
                                  · have p13094_0 := h13094c.1
                                    have p13094_1 := h13094c.2.1
                                    have p13094_2 := h13094c.2.2.1
                                    have p13094_3 := h13094c.2.2.2
                                    linarith only [h11558, hlam, p13094_0]
                                  · have p13094_0 := h13094c.1
                                    have p13094_1 := h13094c.2.1
                                    have p13094_2 := h13094c.2.2.1
                                    have p13094_3 := h13094c.2.2.2
                                    linarith only [h12916, hlam, p13094_0]
                                  · have p13094_0 := h13094c.1
                                    have p13094_1 := h13094c.2.1
                                    have p13094_2 := h13094c.2.2.1
                                    have p13094_3 := h13094c.2.2.2
                                    linarith only [hlam, p13094_0]
                                  · have p13094_0 := h13094c.1
                                    have p13094_1 := h13094c.2.1
                                    have p13094_2 := h13094c.2.2.1
                                    have p13094_3 := h13094c.2.2.2
                                    linarith only [h13020, hlam, p13094_0]
                                  · have p13094_0 := h13094c.1
                                    have p13094_1 := h13094c.2.1
                                    have p13094_2 := h13094c.2.2.1
                                    have p13094_3 := h13094c.2.2.2
                                    linarith only [h13022, hlam, p13094_0]
                                  · have p13094_0 := h13094c.1
                                    have p13094_1 := h13094c.2.1
                                    have p13094_2 := h13094c.2.2.1
                                    have p13094_3 := h13094c.2.2.2
                                    linarith only [h11559, hlam, p13094_0]
                                  · have p13094_0 := h13094c.1
                                    have p13094_1 := h13094c.2.1
                                    have p13094_2 := h13094c.2.2.1
                                    have p13094_3 := h13094c.2.2.2
                                    linarith only [h12917, hlam, p13094_0]
                                  · have p13094_0 := h13094c.1
                                    have p13094_1 := h13094c.2.1
                                    have p13094_2 := h13094c.2.2.1
                                    have p13094_3 := h13094c.2.2.2
                                    linarith only [h11559, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13094_1, u0elo1]
                                  · have p13094_0 := h13094c.1
                                    have p13094_1 := h13094c.2.1
                                    have p13094_2 := h13094c.2.2.1
                                    have p13094_3 := h13094c.2.2.2
                                    linarith only [hlam, p13094_0]
                                  · have p13094_0 := h13094c.1
                                    have p13094_1 := h13094c.2.1
                                    have p13094_2 := h13094c.2.2.1
                                    have p13094_3 := h13094c.2.2.2
                                    linarith only [h11559, hc25, hlam, hphi, ht0b, ht5b, p13094_1, u0elo1]
                                  · have p13094_0 := h13094c.1
                                    have p13094_1 := h13094c.2.1
                                    have p13094_2 := h13094c.2.2.1
                                    have p13094_3 := h13094c.2.2.2
                                    linarith only [h11560, hlam, p13094_0]
                                  · have p13094_0 := h13094c.1
                                    have p13094_1 := h13094c.2.1
                                    have p13094_2 := h13094c.2.2.1
                                    have p13094_3 := h13094c.2.2.2
                                    linarith only [h12918, hlam, p13094_0]
                                  · have p13094_0 := h13094c.1
                                    have p13094_1 := h13094c.2.1
                                    have p13094_2 := h13094c.2.2.1
                                    have p13094_3 := h13094c.2.2.2
                                    linarith only [h11560, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13094_1, u0elo1]
                                  · have p13094_0 := h13094c.1
                                    have p13094_1 := h13094c.2.1
                                    have p13094_2 := h13094c.2.2.1
                                    have p13094_3 := h13094c.2.2.2
                                    linarith only [h13024, hlam, p13094_0]
                                  · have p13094_0 := h13094c.1
                                    have p13094_1 := h13094c.2.1
                                    have p13094_2 := h13094c.2.2.1
                                    have p13094_3 := h13094c.2.2.2
                                    linarith only [hlam, p13094_0]
                                · linarith only [h11559, h12797, h13092, hlam, p13026_1, u0elo1]
                                · rcases h2bigk with h13143c | h13143c | h13143c | h13143c | h13143c | h13143c | h13143c | h13143c | h13143c | h13143c | h13143c | h13143c | h13143c | h13143c | h13143c | h13143c | h13143c | h13143c | h13143c | h13143c | h13143c | h13143c | h13143c | h13143c | h13143c
                                  · have p13143_0 := h13143c.1
                                    have p13143_1 := h13143c.2.1
                                    have p13143_2 := h13143c.2.2.1
                                    have p13143_3 := h13143c.2.2.2
                                    linarith only [hlam, p13143_0]
                                  · have p13143_0 := h13143c.1
                                    have p13143_1 := h13143c.2.1
                                    have p13143_2 := h13143c.2.2.1
                                    have p13143_3 := h13143c.2.2.2
                                    linarith only [h0, hlam, p13143_1]
                                  · have p13143_0 := h13143c.1
                                    have p13143_1 := h13143c.2.1
                                    have p13143_2 := h13143c.2.2.1
                                    have p13143_3 := h13143c.2.2.2
                                    rcases p13143_3 (m.d 0 2) (by simp) with h13146 | h13146
                                    · rcases p13143_3 (m.d 1 2) (by simp) with h13147 | h13147
                                      · rcases p13143_3 (m.d 2 3) (by simp) with h13148 | h13148
                                        · linarith only [h13148, hlam, p13143_0]
                                        · rcases p13143_3 (m.d 2 4) (by simp) with h13150 | h13150
                                          · linarith only [h11559, h13150, hlam]
                                          · linarith only [h13020, h13150, hlam]
                                      · linarith only [h12916, h13147, hlam]
                                    · linarith only [h13146, hlam, p13143_0]
                                  · have p13143_0 := h13143c.1
                                    have p13143_1 := h13143c.2.1
                                    have p13143_2 := h13143c.2.2.1
                                    have p13143_3 := h13143c.2.2.2
                                    linarith only [h13024, hc45, hlam, hphi, ht0b, ht5b, p13143_1, u0elo1]
                                  · have p13143_0 := h13143c.1
                                    have p13143_1 := h13143c.2.1
                                    have p13143_2 := h13143c.2.2.1
                                    have p13143_3 := h13143c.2.2.2
                                    rcases p13143_3 (m.d 0 2) (by simp) with h13156 | h13156
                                    · rcases p13143_3 (m.d 1 2) (by simp) with h13157 | h13157
                                      · rcases p13143_3 (m.d 2 3) (by simp) with h13158 | h13158
                                        · linarith only [h11558, h13158, hlam]
                                        · rcases p13143_3 (m.d 2 4) (by simp) with h13160 | h13160
                                          · linarith only [h11559, h13160, hlam]
                                          · linarith only [h13024, h13160, hlam]
                                      · linarith only [h12918, h13157, hlam]
                                    · linarith only [h13156, hlam, p13143_0]
                                  · have p13143_0 := h13143c.1
                                    have p13143_1 := h13143c.2.1
                                    have p13143_2 := h13143c.2.2.1
                                    have p13143_3 := h13143c.2.2.2
                                    linarith only [h11559, h12797, h6793, hc01, hc12, hlam, hphi, p13026_1, p13143_1]
                                  · have p13143_0 := h13143c.1
                                    have p13143_1 := h13143c.2.1
                                    have p13143_2 := h13143c.2.2.1
                                    have p13143_3 := h13143c.2.2.2
                                    linarith only [hlam, p13143_0]
                                  · have p13143_0 := h13143c.1
                                    have p13143_1 := h13143c.2.1
                                    have p13143_2 := h13143c.2.2.1
                                    have p13143_3 := h13143c.2.2.2
                                    rcases p13143_3 (m.d 0 2) (by simp) with h13167 | h13167
                                    · linarith only [h0, h13167, hlam]
                                    · linarith only [h11558, h13167, hlam]
                                  · have p13143_0 := h13143c.1
                                    have p13143_1 := h13143c.2.1
                                    have p13143_2 := h13143c.2.2.1
                                    have p13143_3 := h13143c.2.2.2
                                    rcases p13143_3 (m.d 0 2) (by simp) with h13170 | h13170
                                    · linarith only [h0, h13170, hlam]
                                    · linarith only [h11559, h13170, hlam]
                                  · have p13143_0 := h13143c.1
                                    have p13143_1 := h13143c.2.1
                                    have p13143_2 := h13143c.2.2.1
                                    have p13143_3 := h13143c.2.2.2
                                    rcases p13143_3 (m.d 0 2) (by simp) with h13173 | h13173
                                    · linarith only [h0, h13173, hlam]
                                    · linarith only [h11560, h13173, hlam]
                                  · have p13143_0 := h13143c.1
                                    have p13143_1 := h13143c.2.1
                                    have p13143_2 := h13143c.2.2.1
                                    have p13143_3 := h13143c.2.2.2
                                    linarith only [h11558, hlam, p13143_0]
                                  · have p13143_0 := h13143c.1
                                    have p13143_1 := h13143c.2.1
                                    have p13143_2 := h13143c.2.2.1
                                    have p13143_3 := h13143c.2.2.2
                                    linarith only [h12916, hlam, p13143_0]
                                  · have p13143_0 := h13143c.1
                                    have p13143_1 := h13143c.2.1
                                    have p13143_2 := h13143c.2.2.1
                                    have p13143_3 := h13143c.2.2.2
                                    linarith only [hlam, p13143_0]
                                  · have p13143_0 := h13143c.1
                                    have p13143_1 := h13143c.2.1
                                    have p13143_2 := h13143c.2.2.1
                                    have p13143_3 := h13143c.2.2.2
                                    linarith only [h13020, hlam, p13143_0]
                                  · have p13143_0 := h13143c.1
                                    have p13143_1 := h13143c.2.1
                                    have p13143_2 := h13143c.2.2.1
                                    have p13143_3 := h13143c.2.2.2
                                    linarith only [h13022, hlam, p13143_0]
                                  · have p13143_0 := h13143c.1
                                    have p13143_1 := h13143c.2.1
                                    have p13143_2 := h13143c.2.2.1
                                    have p13143_3 := h13143c.2.2.2
                                    linarith only [h11559, hlam, p13143_0]
                                  · have p13143_0 := h13143c.1
                                    have p13143_1 := h13143c.2.1
                                    have p13143_2 := h13143c.2.2.1
                                    have p13143_3 := h13143c.2.2.2
                                    linarith only [h12917, hlam, p13143_0]
                                  · have p13143_0 := h13143c.1
                                    have p13143_1 := h13143c.2.1
                                    have p13143_2 := h13143c.2.2.1
                                    have p13143_3 := h13143c.2.2.2
                                    linarith only [h11559, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13143_1, u0elo1]
                                  · have p13143_0 := h13143c.1
                                    have p13143_1 := h13143c.2.1
                                    have p13143_2 := h13143c.2.2.1
                                    have p13143_3 := h13143c.2.2.2
                                    linarith only [hlam, p13143_0]
                                  · have p13143_0 := h13143c.1
                                    have p13143_1 := h13143c.2.1
                                    have p13143_2 := h13143c.2.2.1
                                    have p13143_3 := h13143c.2.2.2
                                    linarith only [h11559, hc25, hlam, hphi, ht0b, ht5b, p13143_1, u0elo1]
                                  · have p13143_0 := h13143c.1
                                    have p13143_1 := h13143c.2.1
                                    have p13143_2 := h13143c.2.2.1
                                    have p13143_3 := h13143c.2.2.2
                                    linarith only [h11560, hlam, p13143_0]
                                  · have p13143_0 := h13143c.1
                                    have p13143_1 := h13143c.2.1
                                    have p13143_2 := h13143c.2.2.1
                                    have p13143_3 := h13143c.2.2.2
                                    linarith only [h12918, hlam, p13143_0]
                                  · have p13143_0 := h13143c.1
                                    have p13143_1 := h13143c.2.1
                                    have p13143_2 := h13143c.2.2.1
                                    have p13143_3 := h13143c.2.2.2
                                    linarith only [h11560, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13143_1, u0elo1]
                                  · have p13143_0 := h13143c.1
                                    have p13143_1 := h13143c.2.1
                                    have p13143_2 := h13143c.2.2.1
                                    have p13143_3 := h13143c.2.2.2
                                    linarith only [h13024, hlam, p13143_0]
                                  · have p13143_0 := h13143c.1
                                    have p13143_1 := h13143c.2.1
                                    have p13143_2 := h13143c.2.2.1
                                    have p13143_3 := h13143c.2.2.2
                                    linarith only [hlam, p13143_0]
                                · linarith only [h11559, h13092, hlam, p13026_1, u0elo1]
                            · linarith only [h12915, h13089, hlam]
                        · linarith only [h11560, h13086, hlam]
                    · have p13026_0 := h13026c.1
                      have p13026_1 := h13026c.2.1
                      have p13026_2 := h13026c.2.2.1
                      have p13026_3 := h13026c.2.2.2
                      rcases p13026_3 (m.d 0 1) (by simp) with h13194 | h13194
                      · linarith only [h11024, h13194, hlam]
                      · rcases p13026_3 (m.d 0 2) (by simp) with h13196 | h13196
                        · rcases p13026_3 (m.d 0 3) (by simp) with h13197 | h13197
                          · linarith only [h12797, h13197, hlam]
                          · linarith only [h13197, h6793, hlam]
                        · linarith only [h0, h13196, hlam]
                    · have p13026_0 := h13026c.1
                      have p13026_1 := h13026c.2.1
                      have p13026_2 := h13026c.2.2.1
                      have p13026_3 := h13026c.2.2.2
                      linarith only [h11560, hlam, p13026_1]
                    · have p13026_0 := h13026c.1
                      have p13026_1 := h13026c.2.1
                      have p13026_2 := h13026c.2.2.1
                      have p13026_3 := h13026c.2.2.2
                      rcases p13026_3 (m.d 0 1) (by simp) with h13202 | h13202
                      · linarith only [h11024, h13202, hlam]
                      · rcases p13026_3 (m.d 0 2) (by simp) with h13204 | h13204
                        · rcases p13026_3 (m.d 0 3) (by simp) with h13205 | h13205
                          · linarith only [h12797, h13205, hlam]
                          · rcases p13026_3 (m.d 0 4) (by simp) with h13207 | h13207
                            · rcases p13026_3 (m.d 0 5) (by simp) with h13208 | h13208
                              · rcases h0emin with h13209 | h13209 | h13209 | h13209 | h13209
                                · linarith only [h13209, h6793, hlam, p13026_1, u0elo4]
                                · rcases h2bigk with h13211c | h13211c | h13211c | h13211c | h13211c | h13211c | h13211c | h13211c | h13211c | h13211c | h13211c | h13211c | h13211c | h13211c | h13211c | h13211c | h13211c | h13211c | h13211c | h13211c | h13211c | h13211c | h13211c | h13211c | h13211c
                                  · have p13211_0 := h13211c.1
                                    have p13211_1 := h13211c.2.1
                                    have p13211_2 := h13211c.2.2.1
                                    have p13211_3 := h13211c.2.2.2
                                    linarith only [hlam, p13211_0]
                                  · have p13211_0 := h13211c.1
                                    have p13211_1 := h13211c.2.1
                                    have p13211_2 := h13211c.2.2.1
                                    have p13211_3 := h13211c.2.2.2
                                    linarith only [h0, hlam, p13211_1]
                                  · have p13211_0 := h13211c.1
                                    have p13211_1 := h13211c.2.1
                                    have p13211_2 := h13211c.2.2.1
                                    have p13211_3 := h13211c.2.2.2
                                    rcases p13211_3 (m.d 0 2) (by simp) with h13214 | h13214
                                    · rcases p13211_3 (m.d 1 2) (by simp) with h13215 | h13215
                                      · rcases p13211_3 (m.d 2 3) (by simp) with h13216 | h13216
                                        · linarith only [h13216, hlam, p13211_0]
                                        · rcases p13211_3 (m.d 2 4) (by simp) with h13218 | h13218
                                          · linarith only [h11559, h13218, hlam]
                                          · linarith only [h13020, h13218, hlam]
                                      · linarith only [h12916, h13215, hlam]
                                    · linarith only [h13214, hlam, p13211_0]
                                  · have p13211_0 := h13211c.1
                                    have p13211_1 := h13211c.2.1
                                    have p13211_2 := h13211c.2.2.1
                                    have p13211_3 := h13211c.2.2.2
                                    linarith only [h13024, hc45, hlam, hphi, ht0b, ht5b, p13211_1, u0elo1]
                                  · have p13211_0 := h13211c.1
                                    have p13211_1 := h13211c.2.1
                                    have p13211_2 := h13211c.2.2.1
                                    have p13211_3 := h13211c.2.2.2
                                    rcases p13211_3 (m.d 0 2) (by simp) with h13224 | h13224
                                    · rcases p13211_3 (m.d 1 2) (by simp) with h13225 | h13225
                                      · rcases p13211_3 (m.d 2 3) (by simp) with h13226 | h13226
                                        · linarith only [h11558, h13226, hlam]
                                        · rcases p13211_3 (m.d 2 4) (by simp) with h13228 | h13228
                                          · linarith only [h11559, h13228, hlam]
                                          · linarith only [h13024, h13228, hlam]
                                      · linarith only [h12918, h13225, hlam]
                                    · linarith only [h13224, hlam, p13211_0]
                                  · have p13211_0 := h13211c.1
                                    have p13211_1 := h13211c.2.1
                                    have p13211_2 := h13211c.2.2.1
                                    have p13211_3 := h13211c.2.2.2
                                    linarith only [h11559, h12915, h6793, hc01, hc12, hlam, hphi, p13026_1, p13211_1]
                                  · have p13211_0 := h13211c.1
                                    have p13211_1 := h13211c.2.1
                                    have p13211_2 := h13211c.2.2.1
                                    have p13211_3 := h13211c.2.2.2
                                    linarith only [hlam, p13211_0]
                                  · have p13211_0 := h13211c.1
                                    have p13211_1 := h13211c.2.1
                                    have p13211_2 := h13211c.2.2.1
                                    have p13211_3 := h13211c.2.2.2
                                    rcases p13211_3 (m.d 0 2) (by simp) with h13235 | h13235
                                    · linarith only [h0, h13235, hlam]
                                    · linarith only [h11558, h13235, hlam]
                                  · have p13211_0 := h13211c.1
                                    have p13211_1 := h13211c.2.1
                                    have p13211_2 := h13211c.2.2.1
                                    have p13211_3 := h13211c.2.2.2
                                    rcases p13211_3 (m.d 0 2) (by simp) with h13238 | h13238
                                    · linarith only [h0, h13238, hlam]
                                    · linarith only [h11559, h13238, hlam]
                                  · have p13211_0 := h13211c.1
                                    have p13211_1 := h13211c.2.1
                                    have p13211_2 := h13211c.2.2.1
                                    have p13211_3 := h13211c.2.2.2
                                    rcases p13211_3 (m.d 0 2) (by simp) with h13241 | h13241
                                    · linarith only [h0, h13241, hlam]
                                    · linarith only [h11560, h13241, hlam]
                                  · have p13211_0 := h13211c.1
                                    have p13211_1 := h13211c.2.1
                                    have p13211_2 := h13211c.2.2.1
                                    have p13211_3 := h13211c.2.2.2
                                    linarith only [h11558, hlam, p13211_0]
                                  · have p13211_0 := h13211c.1
                                    have p13211_1 := h13211c.2.1
                                    have p13211_2 := h13211c.2.2.1
                                    have p13211_3 := h13211c.2.2.2
                                    linarith only [h12916, hlam, p13211_0]
                                  · have p13211_0 := h13211c.1
                                    have p13211_1 := h13211c.2.1
                                    have p13211_2 := h13211c.2.2.1
                                    have p13211_3 := h13211c.2.2.2
                                    linarith only [hlam, p13211_0]
                                  · have p13211_0 := h13211c.1
                                    have p13211_1 := h13211c.2.1
                                    have p13211_2 := h13211c.2.2.1
                                    have p13211_3 := h13211c.2.2.2
                                    linarith only [h13020, hlam, p13211_0]
                                  · have p13211_0 := h13211c.1
                                    have p13211_1 := h13211c.2.1
                                    have p13211_2 := h13211c.2.2.1
                                    have p13211_3 := h13211c.2.2.2
                                    linarith only [h13022, hlam, p13211_0]
                                  · have p13211_0 := h13211c.1
                                    have p13211_1 := h13211c.2.1
                                    have p13211_2 := h13211c.2.2.1
                                    have p13211_3 := h13211c.2.2.2
                                    linarith only [h11559, hlam, p13211_0]
                                  · have p13211_0 := h13211c.1
                                    have p13211_1 := h13211c.2.1
                                    have p13211_2 := h13211c.2.2.1
                                    have p13211_3 := h13211c.2.2.2
                                    linarith only [h12917, hlam, p13211_0]
                                  · have p13211_0 := h13211c.1
                                    have p13211_1 := h13211c.2.1
                                    have p13211_2 := h13211c.2.2.1
                                    have p13211_3 := h13211c.2.2.2
                                    linarith only [h11559, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13211_1, u0elo1]
                                  · have p13211_0 := h13211c.1
                                    have p13211_1 := h13211c.2.1
                                    have p13211_2 := h13211c.2.2.1
                                    have p13211_3 := h13211c.2.2.2
                                    linarith only [hlam, p13211_0]
                                  · have p13211_0 := h13211c.1
                                    have p13211_1 := h13211c.2.1
                                    have p13211_2 := h13211c.2.2.1
                                    have p13211_3 := h13211c.2.2.2
                                    linarith only [h11559, hc25, hlam, hphi, ht0b, ht5b, p13211_1, u0elo1]
                                  · have p13211_0 := h13211c.1
                                    have p13211_1 := h13211c.2.1
                                    have p13211_2 := h13211c.2.2.1
                                    have p13211_3 := h13211c.2.2.2
                                    linarith only [h11560, hlam, p13211_0]
                                  · have p13211_0 := h13211c.1
                                    have p13211_1 := h13211c.2.1
                                    have p13211_2 := h13211c.2.2.1
                                    have p13211_3 := h13211c.2.2.2
                                    linarith only [h12918, hlam, p13211_0]
                                  · have p13211_0 := h13211c.1
                                    have p13211_1 := h13211c.2.1
                                    have p13211_2 := h13211c.2.2.1
                                    have p13211_3 := h13211c.2.2.2
                                    linarith only [h11560, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13211_1, u0elo1]
                                  · have p13211_0 := h13211c.1
                                    have p13211_1 := h13211c.2.1
                                    have p13211_2 := h13211c.2.2.1
                                    have p13211_3 := h13211c.2.2.2
                                    linarith only [h13024, hlam, p13211_0]
                                  · have p13211_0 := h13211c.1
                                    have p13211_1 := h13211c.2.1
                                    have p13211_2 := h13211c.2.2.1
                                    have p13211_3 := h13211c.2.2.2
                                    linarith only [hlam, p13211_0]
                                · linarith only [h11559, h12915, h13209, hlam, p13026_1, u0elo1]
                                · rcases h2bigk with h13260c | h13260c | h13260c | h13260c | h13260c | h13260c | h13260c | h13260c | h13260c | h13260c | h13260c | h13260c | h13260c | h13260c | h13260c | h13260c | h13260c | h13260c | h13260c | h13260c | h13260c | h13260c | h13260c | h13260c | h13260c
                                  · have p13260_0 := h13260c.1
                                    have p13260_1 := h13260c.2.1
                                    have p13260_2 := h13260c.2.2.1
                                    have p13260_3 := h13260c.2.2.2
                                    linarith only [hlam, p13260_0]
                                  · have p13260_0 := h13260c.1
                                    have p13260_1 := h13260c.2.1
                                    have p13260_2 := h13260c.2.2.1
                                    have p13260_3 := h13260c.2.2.2
                                    linarith only [h0, hlam, p13260_1]
                                  · have p13260_0 := h13260c.1
                                    have p13260_1 := h13260c.2.1
                                    have p13260_2 := h13260c.2.2.1
                                    have p13260_3 := h13260c.2.2.2
                                    rcases p13260_3 (m.d 0 2) (by simp) with h13263 | h13263
                                    · rcases p13260_3 (m.d 1 2) (by simp) with h13264 | h13264
                                      · rcases p13260_3 (m.d 2 3) (by simp) with h13265 | h13265
                                        · linarith only [h13265, hlam, p13260_0]
                                        · rcases p13260_3 (m.d 2 4) (by simp) with h13267 | h13267
                                          · linarith only [h11559, h13267, hlam]
                                          · linarith only [h13020, h13267, hlam]
                                      · linarith only [h12916, h13264, hlam]
                                    · linarith only [h13263, hlam, p13260_0]
                                  · have p13260_0 := h13260c.1
                                    have p13260_1 := h13260c.2.1
                                    have p13260_2 := h13260c.2.2.1
                                    have p13260_3 := h13260c.2.2.2
                                    linarith only [h13024, hc45, hlam, hphi, ht0b, ht5b, p13260_1, u0elo1]
                                  · have p13260_0 := h13260c.1
                                    have p13260_1 := h13260c.2.1
                                    have p13260_2 := h13260c.2.2.1
                                    have p13260_3 := h13260c.2.2.2
                                    rcases p13260_3 (m.d 0 2) (by simp) with h13273 | h13273
                                    · rcases p13260_3 (m.d 1 2) (by simp) with h13274 | h13274
                                      · rcases p13260_3 (m.d 2 3) (by simp) with h13275 | h13275
                                        · linarith only [h11558, h13275, hlam]
                                        · rcases p13260_3 (m.d 2 4) (by simp) with h13277 | h13277
                                          · linarith only [h11559, h13277, hlam]
                                          · linarith only [h13024, h13277, hlam]
                                      · linarith only [h12918, h13274, hlam]
                                    · linarith only [h13273, hlam, p13260_0]
                                  · have p13260_0 := h13260c.1
                                    have p13260_1 := h13260c.2.1
                                    have p13260_2 := h13260c.2.2.1
                                    have p13260_3 := h13260c.2.2.2
                                    linarith only [h11559, h12915, h6793, hc01, hc12, hlam, hphi, p13026_1, p13260_1]
                                  · have p13260_0 := h13260c.1
                                    have p13260_1 := h13260c.2.1
                                    have p13260_2 := h13260c.2.2.1
                                    have p13260_3 := h13260c.2.2.2
                                    linarith only [hlam, p13260_0]
                                  · have p13260_0 := h13260c.1
                                    have p13260_1 := h13260c.2.1
                                    have p13260_2 := h13260c.2.2.1
                                    have p13260_3 := h13260c.2.2.2
                                    rcases p13260_3 (m.d 0 2) (by simp) with h13284 | h13284
                                    · linarith only [h0, h13284, hlam]
                                    · linarith only [h11558, h13284, hlam]
                                  · have p13260_0 := h13260c.1
                                    have p13260_1 := h13260c.2.1
                                    have p13260_2 := h13260c.2.2.1
                                    have p13260_3 := h13260c.2.2.2
                                    rcases p13260_3 (m.d 0 2) (by simp) with h13287 | h13287
                                    · linarith only [h0, h13287, hlam]
                                    · linarith only [h11559, h13287, hlam]
                                  · have p13260_0 := h13260c.1
                                    have p13260_1 := h13260c.2.1
                                    have p13260_2 := h13260c.2.2.1
                                    have p13260_3 := h13260c.2.2.2
                                    rcases p13260_3 (m.d 0 2) (by simp) with h13290 | h13290
                                    · linarith only [h0, h13290, hlam]
                                    · linarith only [h11560, h13290, hlam]
                                  · have p13260_0 := h13260c.1
                                    have p13260_1 := h13260c.2.1
                                    have p13260_2 := h13260c.2.2.1
                                    have p13260_3 := h13260c.2.2.2
                                    linarith only [h11558, hlam, p13260_0]
                                  · have p13260_0 := h13260c.1
                                    have p13260_1 := h13260c.2.1
                                    have p13260_2 := h13260c.2.2.1
                                    have p13260_3 := h13260c.2.2.2
                                    linarith only [h12916, hlam, p13260_0]
                                  · have p13260_0 := h13260c.1
                                    have p13260_1 := h13260c.2.1
                                    have p13260_2 := h13260c.2.2.1
                                    have p13260_3 := h13260c.2.2.2
                                    linarith only [hlam, p13260_0]
                                  · have p13260_0 := h13260c.1
                                    have p13260_1 := h13260c.2.1
                                    have p13260_2 := h13260c.2.2.1
                                    have p13260_3 := h13260c.2.2.2
                                    linarith only [h13020, hlam, p13260_0]
                                  · have p13260_0 := h13260c.1
                                    have p13260_1 := h13260c.2.1
                                    have p13260_2 := h13260c.2.2.1
                                    have p13260_3 := h13260c.2.2.2
                                    linarith only [h13022, hlam, p13260_0]
                                  · have p13260_0 := h13260c.1
                                    have p13260_1 := h13260c.2.1
                                    have p13260_2 := h13260c.2.2.1
                                    have p13260_3 := h13260c.2.2.2
                                    linarith only [h11559, hlam, p13260_0]
                                  · have p13260_0 := h13260c.1
                                    have p13260_1 := h13260c.2.1
                                    have p13260_2 := h13260c.2.2.1
                                    have p13260_3 := h13260c.2.2.2
                                    linarith only [h12917, hlam, p13260_0]
                                  · have p13260_0 := h13260c.1
                                    have p13260_1 := h13260c.2.1
                                    have p13260_2 := h13260c.2.2.1
                                    have p13260_3 := h13260c.2.2.2
                                    linarith only [h11559, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13260_1, u0elo1]
                                  · have p13260_0 := h13260c.1
                                    have p13260_1 := h13260c.2.1
                                    have p13260_2 := h13260c.2.2.1
                                    have p13260_3 := h13260c.2.2.2
                                    linarith only [hlam, p13260_0]
                                  · have p13260_0 := h13260c.1
                                    have p13260_1 := h13260c.2.1
                                    have p13260_2 := h13260c.2.2.1
                                    have p13260_3 := h13260c.2.2.2
                                    linarith only [h11559, hc25, hlam, hphi, ht0b, ht5b, p13260_1, u0elo1]
                                  · have p13260_0 := h13260c.1
                                    have p13260_1 := h13260c.2.1
                                    have p13260_2 := h13260c.2.2.1
                                    have p13260_3 := h13260c.2.2.2
                                    linarith only [h11560, hlam, p13260_0]
                                  · have p13260_0 := h13260c.1
                                    have p13260_1 := h13260c.2.1
                                    have p13260_2 := h13260c.2.2.1
                                    have p13260_3 := h13260c.2.2.2
                                    linarith only [h12918, hlam, p13260_0]
                                  · have p13260_0 := h13260c.1
                                    have p13260_1 := h13260c.2.1
                                    have p13260_2 := h13260c.2.2.1
                                    have p13260_3 := h13260c.2.2.2
                                    linarith only [h11560, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13260_1, u0elo1]
                                  · have p13260_0 := h13260c.1
                                    have p13260_1 := h13260c.2.1
                                    have p13260_2 := h13260c.2.2.1
                                    have p13260_3 := h13260c.2.2.2
                                    linarith only [h13024, hlam, p13260_0]
                                  · have p13260_0 := h13260c.1
                                    have p13260_1 := h13260c.2.1
                                    have p13260_2 := h13260c.2.2.1
                                    have p13260_3 := h13260c.2.2.2
                                    linarith only [hlam, p13260_0]
                                · rcases h2bigk with h13308c | h13308c | h13308c | h13308c | h13308c | h13308c | h13308c | h13308c | h13308c | h13308c | h13308c | h13308c | h13308c | h13308c | h13308c | h13308c | h13308c | h13308c | h13308c | h13308c | h13308c | h13308c | h13308c | h13308c | h13308c
                                  · have p13308_0 := h13308c.1
                                    have p13308_1 := h13308c.2.1
                                    have p13308_2 := h13308c.2.2.1
                                    have p13308_3 := h13308c.2.2.2
                                    linarith only [hlam, p13308_0]
                                  · have p13308_0 := h13308c.1
                                    have p13308_1 := h13308c.2.1
                                    have p13308_2 := h13308c.2.2.1
                                    have p13308_3 := h13308c.2.2.2
                                    linarith only [h0, hlam, p13308_1]
                                  · have p13308_0 := h13308c.1
                                    have p13308_1 := h13308c.2.1
                                    have p13308_2 := h13308c.2.2.1
                                    have p13308_3 := h13308c.2.2.2
                                    rcases p13308_3 (m.d 0 2) (by simp) with h13311 | h13311
                                    · rcases p13308_3 (m.d 1 2) (by simp) with h13312 | h13312
                                      · rcases p13308_3 (m.d 2 3) (by simp) with h13313 | h13313
                                        · linarith only [h13313, hlam, p13308_0]
                                        · rcases p13308_3 (m.d 2 4) (by simp) with h13315 | h13315
                                          · linarith only [h11559, h13315, hlam]
                                          · linarith only [h13020, h13315, hlam]
                                      · linarith only [h12916, h13312, hlam]
                                    · linarith only [h13311, hlam, p13308_0]
                                  · have p13308_0 := h13308c.1
                                    have p13308_1 := h13308c.2.1
                                    have p13308_2 := h13308c.2.2.1
                                    have p13308_3 := h13308c.2.2.2
                                    linarith only [h13024, hc45, hlam, hphi, ht0b, ht5b, p13308_1, u0elo1]
                                  · have p13308_0 := h13308c.1
                                    have p13308_1 := h13308c.2.1
                                    have p13308_2 := h13308c.2.2.1
                                    have p13308_3 := h13308c.2.2.2
                                    rcases p13308_3 (m.d 0 2) (by simp) with h13321 | h13321
                                    · rcases p13308_3 (m.d 1 2) (by simp) with h13322 | h13322
                                      · rcases p13308_3 (m.d 2 3) (by simp) with h13323 | h13323
                                        · linarith only [h11558, h13323, hlam]
                                        · rcases p13308_3 (m.d 2 4) (by simp) with h13325 | h13325
                                          · linarith only [h11559, h13325, hlam]
                                          · linarith only [h13024, h13325, hlam]
                                      · linarith only [h12918, h13322, hlam]
                                    · linarith only [h13321, hlam, p13308_0]
                                  · have p13308_0 := h13308c.1
                                    have p13308_1 := h13308c.2.1
                                    have p13308_2 := h13308c.2.2.1
                                    have p13308_3 := h13308c.2.2.2
                                    linarith only [h11559, h12915, h6793, hc01, hc12, hlam, hphi, p13026_1, p13308_1]
                                  · have p13308_0 := h13308c.1
                                    have p13308_1 := h13308c.2.1
                                    have p13308_2 := h13308c.2.2.1
                                    have p13308_3 := h13308c.2.2.2
                                    linarith only [hlam, p13308_0]
                                  · have p13308_0 := h13308c.1
                                    have p13308_1 := h13308c.2.1
                                    have p13308_2 := h13308c.2.2.1
                                    have p13308_3 := h13308c.2.2.2
                                    rcases p13308_3 (m.d 0 2) (by simp) with h13332 | h13332
                                    · linarith only [h0, h13332, hlam]
                                    · linarith only [h11558, h13332, hlam]
                                  · have p13308_0 := h13308c.1
                                    have p13308_1 := h13308c.2.1
                                    have p13308_2 := h13308c.2.2.1
                                    have p13308_3 := h13308c.2.2.2
                                    rcases p13308_3 (m.d 0 2) (by simp) with h13335 | h13335
                                    · linarith only [h0, h13335, hlam]
                                    · linarith only [h11559, h13335, hlam]
                                  · have p13308_0 := h13308c.1
                                    have p13308_1 := h13308c.2.1
                                    have p13308_2 := h13308c.2.2.1
                                    have p13308_3 := h13308c.2.2.2
                                    rcases p13308_3 (m.d 0 2) (by simp) with h13338 | h13338
                                    · linarith only [h0, h13338, hlam]
                                    · linarith only [h11560, h13338, hlam]
                                  · have p13308_0 := h13308c.1
                                    have p13308_1 := h13308c.2.1
                                    have p13308_2 := h13308c.2.2.1
                                    have p13308_3 := h13308c.2.2.2
                                    linarith only [h11558, hlam, p13308_0]
                                  · have p13308_0 := h13308c.1
                                    have p13308_1 := h13308c.2.1
                                    have p13308_2 := h13308c.2.2.1
                                    have p13308_3 := h13308c.2.2.2
                                    linarith only [h12916, hlam, p13308_0]
                                  · have p13308_0 := h13308c.1
                                    have p13308_1 := h13308c.2.1
                                    have p13308_2 := h13308c.2.2.1
                                    have p13308_3 := h13308c.2.2.2
                                    linarith only [hlam, p13308_0]
                                  · have p13308_0 := h13308c.1
                                    have p13308_1 := h13308c.2.1
                                    have p13308_2 := h13308c.2.2.1
                                    have p13308_3 := h13308c.2.2.2
                                    linarith only [h13020, hlam, p13308_0]
                                  · have p13308_0 := h13308c.1
                                    have p13308_1 := h13308c.2.1
                                    have p13308_2 := h13308c.2.2.1
                                    have p13308_3 := h13308c.2.2.2
                                    linarith only [h13022, hlam, p13308_0]
                                  · have p13308_0 := h13308c.1
                                    have p13308_1 := h13308c.2.1
                                    have p13308_2 := h13308c.2.2.1
                                    have p13308_3 := h13308c.2.2.2
                                    linarith only [h11559, hlam, p13308_0]
                                  · have p13308_0 := h13308c.1
                                    have p13308_1 := h13308c.2.1
                                    have p13308_2 := h13308c.2.2.1
                                    have p13308_3 := h13308c.2.2.2
                                    linarith only [h12917, hlam, p13308_0]
                                  · have p13308_0 := h13308c.1
                                    have p13308_1 := h13308c.2.1
                                    have p13308_2 := h13308c.2.2.1
                                    have p13308_3 := h13308c.2.2.2
                                    linarith only [h11559, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13308_1, u0elo1]
                                  · have p13308_0 := h13308c.1
                                    have p13308_1 := h13308c.2.1
                                    have p13308_2 := h13308c.2.2.1
                                    have p13308_3 := h13308c.2.2.2
                                    linarith only [hlam, p13308_0]
                                  · have p13308_0 := h13308c.1
                                    have p13308_1 := h13308c.2.1
                                    have p13308_2 := h13308c.2.2.1
                                    have p13308_3 := h13308c.2.2.2
                                    linarith only [h11559, hc25, hlam, hphi, ht0b, ht5b, p13308_1, u0elo1]
                                  · have p13308_0 := h13308c.1
                                    have p13308_1 := h13308c.2.1
                                    have p13308_2 := h13308c.2.2.1
                                    have p13308_3 := h13308c.2.2.2
                                    linarith only [h11560, hlam, p13308_0]
                                  · have p13308_0 := h13308c.1
                                    have p13308_1 := h13308c.2.1
                                    have p13308_2 := h13308c.2.2.1
                                    have p13308_3 := h13308c.2.2.2
                                    linarith only [h12918, hlam, p13308_0]
                                  · have p13308_0 := h13308c.1
                                    have p13308_1 := h13308c.2.1
                                    have p13308_2 := h13308c.2.2.1
                                    have p13308_3 := h13308c.2.2.2
                                    linarith only [h11560, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13308_1, u0elo1]
                                  · have p13308_0 := h13308c.1
                                    have p13308_1 := h13308c.2.1
                                    have p13308_2 := h13308c.2.2.1
                                    have p13308_3 := h13308c.2.2.2
                                    linarith only [h13024, hlam, p13308_0]
                                  · have p13308_0 := h13308c.1
                                    have p13308_1 := h13308c.2.1
                                    have p13308_2 := h13308c.2.2.1
                                    have p13308_3 := h13308c.2.2.2
                                    linarith only [hlam, p13308_0]
                              · linarith only [h12797, h13208, hlam]
                            · linarith only [h11561, h13207, hlam]
                        · linarith only [h11558, h13204, hlam]
                    · have p13026_0 := h13026c.1
                      have p13026_1 := h13026c.2.1
                      have p13026_2 := h13026c.2.2.1
                      have p13026_3 := h13026c.2.2.2
                      linarith only [h12915, hlam, p13026_1]
                    · have p13026_0 := h13026c.1
                      have p13026_1 := h13026c.2.1
                      have p13026_2 := h13026c.2.2.1
                      have p13026_3 := h13026c.2.2.2
                      linarith only [hlam, p13026_0]
                  · linarith only [h12919, h13025, h6793, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h13362 | h13362
                  · rcases h0bigk with h13363c | h13363c | h13363c | h13363c | h13363c | h13363c | h13363c | h13363c | h13363c | h13363c | h13363c | h13363c | h13363c | h13363c | h13363c | h13363c | h13363c | h13363c | h13363c | h13363c | h13363c | h13363c | h13363c | h13363c | h13363c
                    · have p13363_0 := h13363c.1
                      have p13363_1 := h13363c.2.1
                      have p13363_2 := h13363c.2.2.1
                      have p13363_3 := h13363c.2.2.2
                      linarith only [hlam, p13363_0]
                    · have p13363_0 := h13363c.1
                      have p13363_1 := h13363c.2.1
                      have p13363_2 := h13363c.2.2.1
                      have p13363_3 := h13363c.2.2.2
                      linarith only [h0, hlam, p13363_1]
                    · have p13363_0 := h13363c.1
                      have p13363_1 := h13363c.2.1
                      have p13363_2 := h13363c.2.2.1
                      have p13363_3 := h13363c.2.2.2
                      linarith only [h6793, hlam, p13363_0]
                    · have p13363_0 := h13363c.1
                      have p13363_1 := h13363c.2.1
                      have p13363_2 := h13363c.2.2.1
                      have p13363_3 := h13363c.2.2.2
                      linarith only [h10058, hlam, p13363_1]
                    · have p13363_0 := h13363c.1
                      have p13363_1 := h13363c.2.1
                      have p13363_2 := h13363c.2.2.1
                      have p13363_3 := h13363c.2.2.2
                      linarith only [h11024, hlam, p13363_1]
                    · have p13363_0 := h13363c.1
                      have p13363_1 := h13363c.2.1
                      have p13363_2 := h13363c.2.2.1
                      have p13363_3 := h13363c.2.2.2
                      rcases p13363_3 (m.d 0 1) (by simp) with h13369 | h13369
                      · linarith only [h0, h13369, hlam]
                      · rcases p13363_3 (m.d 0 2) (by simp) with h13371 | h13371
                        · rcases p13363_3 (m.d 0 3) (by simp) with h13372 | h13372
                          · linarith only [h11558, h13372, hlam]
                          · linarith only [h13372, h6793, hlam]
                        · linarith only [h0, h13371, hlam]
                    · have p13363_0 := h13363c.1
                      have p13363_1 := h13363c.2.1
                      have p13363_2 := h13363c.2.2.1
                      have p13363_3 := h13363c.2.2.2
                      linarith only [hlam, p13363_0]
                    · have p13363_0 := h13363c.1
                      have p13363_1 := h13363c.2.1
                      have p13363_2 := h13363c.2.2.1
                      have p13363_3 := h13363c.2.2.2
                      rcases p13363_3 (m.d 0 1) (by simp) with h13377 | h13377
                      · linarith only [h0, h13377, hlam]
                      · rcases p13363_3 (m.d 0 2) (by simp) with h13379 | h13379
                        · rcases p13363_3 (m.d 0 3) (by simp) with h13380 | h13380
                          · linarith only [h11558, h13380, hlam]
                          · rcases p13363_3 (m.d 0 4) (by simp) with h13382 | h13382
                            · linarith only [h11559, h13382, hlam]
                            · linarith only [h11561, h13382, hlam]
                        · linarith only [h11558, h13379, hlam]
                    · have p13363_0 := h13363c.1
                      have p13363_1 := h13363c.2.1
                      have p13363_2 := h13363c.2.2.1
                      have p13363_3 := h13363c.2.2.2
                      linarith only [h12915, h13024, hc24, hlam, hphi, ht0b, ht45, ht5b, p13363_1, u0elo1]
                    · have p13363_0 := h13363c.1
                      have p13363_1 := h13363c.2.1
                      have p13363_2 := h13363c.2.2.1
                      have p13363_3 := h13363c.2.2.2
                      linarith only [h12915, h13024, hc24, hlam, hphi, ht0b, ht45, ht5b, p13363_1, u0elo1]
                    · have p13363_0 := h13363c.1
                      have p13363_1 := h13363c.2.1
                      have p13363_2 := h13363c.2.2.1
                      have p13363_3 := h13363c.2.2.2
                      linarith only [h11561, hc01, hc34, hlam, hphi, ht12, ht23, p13363_1]
                    · have p13363_0 := h13363c.1
                      have p13363_1 := h13363c.2.1
                      have p13363_2 := h13363c.2.2.1
                      have p13363_3 := h13363c.2.2.2
                      linarith only [h11558, hlam, p13363_1]
                    · have p13363_0 := h13363c.1
                      have p13363_1 := h13363c.2.1
                      have p13363_2 := h13363c.2.2.1
                      have p13363_3 := h13363c.2.2.2
                      linarith only [hlam, p13363_0]
                    · have p13363_0 := h13363c.1
                      have p13363_1 := h13363c.2.1
                      have p13363_2 := h13363c.2.2.1
                      have p13363_3 := h13363c.2.2.2
                      linarith only [h11561, hlam, p13363_1]
                    · have p13363_0 := h13363c.1
                      have p13363_1 := h13363c.2.1
                      have p13363_2 := h13363c.2.2.1
                      have p13363_3 := h13363c.2.2.2
                      linarith only [h12797, hlam, p13363_1]
                    · have p13363_0 := h13363c.1
                      have p13363_1 := h13363c.2.1
                      have p13363_2 := h13363c.2.2.1
                      have p13363_3 := h13363c.2.2.2
                      rcases p13363_3 (m.d 0 1) (by simp) with h13393 | h13393
                      · linarith only [h10058, h13393, hlam]
                      · rcases p13363_3 (m.d 0 2) (by simp) with h13395 | h13395
                        · rcases p13363_3 (m.d 0 3) (by simp) with h13396 | h13396
                          · linarith only [h11561, h13396, hlam]
                          · linarith only [h13396, h6793, hlam]
                        · linarith only [h0, h13395, hlam]
                    · have p13363_0 := h13363c.1
                      have p13363_1 := h13363c.2.1
                      have p13363_2 := h13363c.2.2.1
                      have p13363_3 := h13363c.2.2.2
                      linarith only [h11559, hlam, p13363_0]
                    · have p13363_0 := h13363c.1
                      have p13363_1 := h13363c.2.1
                      have p13363_2 := h13363c.2.2.1
                      have p13363_3 := h13363c.2.2.2
                      rcases p13363_3 (m.d 0 1) (by simp) with h13401 | h13401
                      · linarith only [h10058, h13401, hlam]
                      · rcases p13363_3 (m.d 0 2) (by simp) with h13403 | h13403
                        · rcases p13363_3 (m.d 0 3) (by simp) with h13404 | h13404
                          · linarith only [h11561, h13404, hlam]
                          · rcases p13363_3 (m.d 0 4) (by simp) with h13406 | h13406
                            · rcases p13363_3 (m.d 0 5) (by simp) with h13407 | h13407
                              · linarith only [h12915, h13407, hlam]
                              · linarith only [h12797, h13407, hlam]
                            · linarith only [h11561, h13406, hlam]
                        · linarith only [h11558, h13403, hlam]
                    · have p13363_0 := h13363c.1
                      have p13363_1 := h13363c.2.1
                      have p13363_2 := h13363c.2.2.1
                      have p13363_3 := h13363c.2.2.2
                      linarith only [hlam, p13363_0]
                    · have p13363_0 := h13363c.1
                      have p13363_1 := h13363c.2.1
                      have p13363_2 := h13363c.2.2.1
                      have p13363_3 := h13363c.2.2.2
                      linarith only [h12915, h13020, h13024, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13363_1, u0elo3]
                    · have p13363_0 := h13363c.1
                      have p13363_1 := h13363c.2.1
                      have p13363_2 := h13363c.2.2.1
                      have p13363_3 := h13363c.2.2.2
                      rcases p13363_3 (m.d 0 1) (by simp) with h13414 | h13414
                      · linarith only [h11024, h13414, hlam]
                      · rcases p13363_3 (m.d 0 2) (by simp) with h13416 | h13416
                        · rcases p13363_3 (m.d 0 3) (by simp) with h13417 | h13417
                          · linarith only [h12797, h13417, hlam]
                          · linarith only [h13417, h6793, hlam]
                        · linarith only [h0, h13416, hlam]
                    · have p13363_0 := h13363c.1
                      have p13363_1 := h13363c.2.1
                      have p13363_2 := h13363c.2.2.1
                      have p13363_3 := h13363c.2.2.2
                      linarith only [h11560, hlam, p13363_1]
                    · have p13363_0 := h13363c.1
                      have p13363_1 := h13363c.2.1
                      have p13363_2 := h13363c.2.2.1
                      have p13363_3 := h13363c.2.2.2
                      rcases p13363_3 (m.d 0 1) (by simp) with h13422 | h13422
                      · linarith only [h11024, h13422, hlam]
                      · rcases p13363_3 (m.d 0 2) (by simp) with h13424 | h13424
                        · rcases p13363_3 (m.d 0 3) (by simp) with h13425 | h13425
                          · linarith only [h12797, h13425, hlam]
                          · rcases p13363_3 (m.d 0 4) (by simp) with h13427 | h13427
                            · rcases p13363_3 (m.d 0 5) (by simp) with h13428 | h13428
                              · rcases h0emin with h13429 | h13429 | h13429 | h13429 | h13429
                                · linarith only [h13429, h6793, hlam, p13363_1, u0elo4]
                                · rcases h2bigk with h13431c | h13431c | h13431c | h13431c | h13431c | h13431c | h13431c | h13431c | h13431c | h13431c | h13431c | h13431c | h13431c | h13431c | h13431c | h13431c | h13431c | h13431c | h13431c | h13431c | h13431c | h13431c | h13431c | h13431c | h13431c
                                  · have p13431_0 := h13431c.1
                                    have p13431_1 := h13431c.2.1
                                    have p13431_2 := h13431c.2.2.1
                                    have p13431_3 := h13431c.2.2.2
                                    linarith only [hlam, p13431_0]
                                  · have p13431_0 := h13431c.1
                                    have p13431_1 := h13431c.2.1
                                    have p13431_2 := h13431c.2.2.1
                                    have p13431_3 := h13431c.2.2.2
                                    linarith only [h0, hlam, p13431_1]
                                  · have p13431_0 := h13431c.1
                                    have p13431_1 := h13431c.2.1
                                    have p13431_2 := h13431c.2.2.1
                                    have p13431_3 := h13431c.2.2.2
                                    rcases p13431_3 (m.d 0 2) (by simp) with h13434 | h13434
                                    · rcases p13431_3 (m.d 1 2) (by simp) with h13435 | h13435
                                      · rcases p13431_3 (m.d 2 3) (by simp) with h13436 | h13436
                                        · linarith only [h13436, hlam, p13431_0]
                                        · rcases p13431_3 (m.d 2 4) (by simp) with h13438 | h13438
                                          · linarith only [h11559, h13438, hlam]
                                          · linarith only [h13020, h13438, hlam]
                                      · linarith only [h12916, h13435, hlam]
                                    · linarith only [h13434, hlam, p13431_0]
                                  · have p13431_0 := h13431c.1
                                    have p13431_1 := h13431c.2.1
                                    have p13431_2 := h13431c.2.2.1
                                    have p13431_3 := h13431c.2.2.2
                                    rcases p13431_3 (m.d 0 2) (by simp) with h13443 | h13443
                                    · rcases p13431_3 (m.d 1 2) (by simp) with h13444 | h13444
                                      · rcases p13431_3 (m.d 2 3) (by simp) with h13445 | h13445
                                        · linarith only [h11558, h13445, hlam]
                                        · rcases p13431_3 (m.d 2 4) (by simp) with h13447 | h13447
                                          · linarith only [h13447, hlam, p13431_0]
                                          · rcases p13431_3 (m.d 2 5) (by simp) with h13449 | h13449
                                            · linarith only [h11560, h13449, hlam]
                                            · linarith only [h13024, h13449, hlam]
                                      · linarith only [h12917, h13444, hlam]
                                    · linarith only [h13443, hlam, p13431_0]
                                  · have p13431_0 := h13431c.1
                                    have p13431_1 := h13431c.2.1
                                    have p13431_2 := h13431c.2.2.1
                                    have p13431_3 := h13431c.2.2.2
                                    rcases p13431_3 (m.d 0 2) (by simp) with h13454 | h13454
                                    · rcases p13431_3 (m.d 1 2) (by simp) with h13455 | h13455
                                      · rcases p13431_3 (m.d 2 3) (by simp) with h13456 | h13456
                                        · linarith only [h11558, h13456, hlam]
                                        · rcases p13431_3 (m.d 2 4) (by simp) with h13458 | h13458
                                          · linarith only [h11559, h13458, hlam]
                                          · rcases p13431_3 (m.d 2 5) (by simp) with h13460 | h13460
                                            · linarith only [h13460, hlam, p13431_0]
                                            · rcases h4bigk with h13462c | h13462c | h13462c | h13462c | h13462c | h13462c | h13462c | h13462c | h13462c | h13462c | h13462c | h13462c | h13462c | h13462c | h13462c | h13462c | h13462c | h13462c | h13462c | h13462c | h13462c | h13462c | h13462c | h13462c | h13462c
                                              · have p13462_0 := h13462c.1
                                                have p13462_1 := h13462c.2.1
                                                have p13462_2 := h13462c.2.2.1
                                                have p13462_3 := h13462c.2.2.2
                                                linarith only [hlam, p13462_0]
                                              · have p13462_0 := h13462c.1
                                                have p13462_1 := h13462c.2.1
                                                have p13462_2 := h13462c.2.2.1
                                                have p13462_3 := h13462c.2.2.2
                                                linarith only [h10058, hlam, p13462_0]
                                              · have p13462_0 := h13462c.1
                                                have p13462_1 := h13462c.2.1
                                                have p13462_2 := h13462c.2.2.1
                                                have p13462_3 := h13462c.2.2.2
                                                rcases p13462_3 (m.d 0 4) (by simp) with h13465 | h13465
                                                · rcases p13462_3 (m.d 1 4) (by simp) with h13466 | h13466
                                                  · rcases p13462_3 (m.d 2 4) (by simp) with h13467 | h13467
                                                    · linarith only [h11559, h13467, hlam]
                                                    · rcases p13462_3 (m.d 3 4) (by simp) with h13469 | h13469
                                                      · rcases p13462_3 (m.d 4 5) (by simp) with h13470 | h13470
                                                        · linarith only [h12915, h13470, hlam]
                                                        · linarith only [h13024, h13470, hlam]
                                                      · linarith only [h13020, h13469, hlam]
                                                  · linarith only [h12917, h13466, hlam]
                                                · linarith only [h11559, h13465, hlam]
                                              · have p13462_0 := h13462c.1
                                                have p13462_1 := h13462c.2.1
                                                have p13462_2 := h13462c.2.2.1
                                                have p13462_3 := h13462c.2.2.2
                                                linarith only [h11561, hlam, p13462_0]
                                              · have p13462_0 := h13462c.1
                                                have p13462_1 := h13462c.2.1
                                                have p13462_2 := h13462c.2.2.1
                                                have p13462_3 := h13462c.2.2.2
                                                linarith only [h11559, h13020, h13024, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13462_1, u0elo1]
                                              · have p13462_0 := h13462c.1
                                                have p13462_1 := h13462c.2.1
                                                have p13462_2 := h13462c.2.2.1
                                                have p13462_3 := h13462c.2.2.2
                                                linarith only [h12915, h13020, h13024, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13462_1]
                                              · have p13462_0 := h13462c.1
                                                have p13462_1 := h13462c.2.1
                                                have p13462_2 := h13462c.2.2.1
                                                have p13462_3 := h13462c.2.2.2
                                                linarith only [hlam, p13462_0]
                                              · have p13462_0 := h13462c.1
                                                have p13462_1 := h13462c.2.1
                                                have p13462_2 := h13462c.2.2.1
                                                have p13462_3 := h13462c.2.2.2
                                                rcases p13462_3 (m.d 0 4) (by simp) with h13480 | h13480
                                                · linarith only [h10058, h13480, hlam]
                                                · linarith only [h11559, h13480, hlam]
                                              · have p13462_0 := h13462c.1
                                                have p13462_1 := h13462c.2.1
                                                have p13462_2 := h13462c.2.2.1
                                                have p13462_3 := h13462c.2.2.2
                                                linarith only [h12919, hlam, p13462_1]
                                              · have p13462_0 := h13462c.1
                                                have p13462_1 := h13462c.2.1
                                                have p13462_2 := h13462c.2.2.1
                                                have p13462_3 := h13462c.2.2.2
                                                linarith only [h12919, h13020, h13024, hc23, hc34, hlam, hphi, p13462_1]
                                              · have p13462_0 := h13462c.1
                                                have p13462_1 := h13462c.2.1
                                                have p13462_2 := h13462c.2.2.1
                                                have p13462_3 := h13462c.2.2.2
                                                linarith only [h11559, hlam, p13462_1]
                                              · have p13462_0 := h13462c.1
                                                have p13462_1 := h13462c.2.1
                                                have p13462_2 := h13462c.2.2.1
                                                have p13462_3 := h13462c.2.2.2
                                                linarith only [h12917, hlam, p13462_1]
                                              · have p13462_0 := h13462c.1
                                                have p13462_1 := h13462c.2.1
                                                have p13462_2 := h13462c.2.2.1
                                                have p13462_3 := h13462c.2.2.2
                                                linarith only [hlam, p13462_0]
                                              · have p13462_0 := h13462c.1
                                                have p13462_1 := h13462c.2.1
                                                have p13462_2 := h13462c.2.2.1
                                                have p13462_3 := h13462c.2.2.2
                                                linarith only [h13020, hlam, p13462_1]
                                              · have p13462_0 := h13462c.1
                                                have p13462_1 := h13462c.2.1
                                                have p13462_2 := h13462c.2.2.1
                                                have p13462_3 := h13462c.2.2.2
                                                linarith only [h13024, hlam, p13462_0]
                                              · have p13462_0 := h13462c.1
                                                have p13462_1 := h13462c.2.1
                                                have p13462_2 := h13462c.2.2.1
                                                have p13462_3 := h13462c.2.2.2
                                                linarith only [h12915, h6793, hc01, hc34, hlam, hphi, ht12, ht23, p13363_1, p13462_1]
                                              · have p13462_0 := h13462c.1
                                                have p13462_1 := h13462c.2.1
                                                have p13462_2 := h13462c.2.2.1
                                                have p13462_3 := h13462c.2.2.2
                                                linarith only [h10058, hc01, hc34, hlam, hphi, ht12, ht23, p13462_1]
                                              · have p13462_0 := h13462c.1
                                                have p13462_1 := h13462c.2.1
                                                have p13462_2 := h13462c.2.2.1
                                                have p13462_3 := h13462c.2.2.2
                                                rcases p13462_3 (m.d 0 4) (by simp) with h13492 | h13492
                                                · linarith only [h11561, h13492, hlam]
                                                · linarith only [h11559, h13492, hlam]
                                              · have p13462_0 := h13462c.1
                                                have p13462_1 := h13462c.2.1
                                                have p13462_2 := h13462c.2.2.1
                                                have p13462_3 := h13462c.2.2.2
                                                linarith only [hlam, p13462_0]
                                              · have p13462_0 := h13462c.1
                                                have p13462_1 := h13462c.2.1
                                                have p13462_2 := h13462c.2.2.1
                                                have p13462_3 := h13462c.2.2.2
                                                linarith only [h13020, h13024, hc23, hc34, hlam, hphi, p13462_1]
                                              · have p13462_0 := h13462c.1
                                                have p13462_1 := h13462c.2.1
                                                have p13462_2 := h13462c.2.2.1
                                                have p13462_3 := h13462c.2.2.2
                                                linarith only [h12915, hlam, p13462_0]
                                              · have p13462_0 := h13462c.1
                                                have p13462_1 := h13462c.2.1
                                                have p13462_2 := h13462c.2.2.1
                                                have p13462_3 := h13462c.2.2.2
                                                linarith only [h13019, hlam, p13462_0]
                                              · have p13462_0 := h13462c.1
                                                have p13462_1 := h13462c.2.1
                                                have p13462_2 := h13462c.2.2.1
                                                have p13462_3 := h13462c.2.2.2
                                                linarith only [h12915, h13020, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13462_1, u0elo3]
                                              · have p13462_0 := h13462c.1
                                                have p13462_1 := h13462c.2.1
                                                have p13462_2 := h13462c.2.2.1
                                                have p13462_3 := h13462c.2.2.2
                                                linarith only [h13362, hlam, p13462_0]
                                              · have p13462_0 := h13462c.1
                                                have p13462_1 := h13462c.2.1
                                                have p13462_2 := h13462c.2.2.1
                                                have p13462_3 := h13462c.2.2.2
                                                linarith only [hlam, p13462_0]
                                      · linarith only [h12918, h13455, hlam]
                                    · linarith only [h13454, hlam, p13431_0]
                                  · have p13431_0 := h13431c.1
                                    have p13431_1 := h13431c.2.1
                                    have p13431_2 := h13431c.2.2.1
                                    have p13431_3 := h13431c.2.2.2
                                    linarith only [h13429, hc12, hlam, ht01, p13431_1]
                                  · have p13431_0 := h13431c.1
                                    have p13431_1 := h13431c.2.1
                                    have p13431_2 := h13431c.2.2.1
                                    have p13431_3 := h13431c.2.2.2
                                    linarith only [hlam, p13431_0]
                                  · have p13431_0 := h13431c.1
                                    have p13431_1 := h13431c.2.1
                                    have p13431_2 := h13431c.2.2.1
                                    have p13431_3 := h13431c.2.2.2
                                    rcases p13431_3 (m.d 0 2) (by simp) with h13506 | h13506
                                    · linarith only [h0, h13506, hlam]
                                    · linarith only [h11558, h13506, hlam]
                                  · have p13431_0 := h13431c.1
                                    have p13431_1 := h13431c.2.1
                                    have p13431_2 := h13431c.2.2.1
                                    have p13431_3 := h13431c.2.2.2
                                    rcases p13431_3 (m.d 0 2) (by simp) with h13509 | h13509
                                    · linarith only [h0, h13509, hlam]
                                    · linarith only [h11559, h13509, hlam]
                                  · have p13431_0 := h13431c.1
                                    have p13431_1 := h13431c.2.1
                                    have p13431_2 := h13431c.2.2.1
                                    have p13431_3 := h13431c.2.2.2
                                    rcases p13431_3 (m.d 0 2) (by simp) with h13512 | h13512
                                    · linarith only [h0, h13512, hlam]
                                    · linarith only [h11560, h13512, hlam]
                                  · have p13431_0 := h13431c.1
                                    have p13431_1 := h13431c.2.1
                                    have p13431_2 := h13431c.2.2.1
                                    have p13431_3 := h13431c.2.2.2
                                    linarith only [h11558, hlam, p13431_0]
                                  · have p13431_0 := h13431c.1
                                    have p13431_1 := h13431c.2.1
                                    have p13431_2 := h13431c.2.2.1
                                    have p13431_3 := h13431c.2.2.2
                                    linarith only [h12916, hlam, p13431_0]
                                  · have p13431_0 := h13431c.1
                                    have p13431_1 := h13431c.2.1
                                    have p13431_2 := h13431c.2.2.1
                                    have p13431_3 := h13431c.2.2.2
                                    linarith only [hlam, p13431_0]
                                  · have p13431_0 := h13431c.1
                                    have p13431_1 := h13431c.2.1
                                    have p13431_2 := h13431c.2.2.1
                                    have p13431_3 := h13431c.2.2.2
                                    linarith only [h13020, hlam, p13431_0]
                                  · have p13431_0 := h13431c.1
                                    have p13431_1 := h13431c.2.1
                                    have p13431_2 := h13431c.2.2.1
                                    have p13431_3 := h13431c.2.2.2
                                    linarith only [h13022, hlam, p13431_0]
                                  · have p13431_0 := h13431c.1
                                    have p13431_1 := h13431c.2.1
                                    have p13431_2 := h13431c.2.2.1
                                    have p13431_3 := h13431c.2.2.2
                                    linarith only [h11559, hlam, p13431_0]
                                  · have p13431_0 := h13431c.1
                                    have p13431_1 := h13431c.2.1
                                    have p13431_2 := h13431c.2.2.1
                                    have p13431_3 := h13431c.2.2.2
                                    linarith only [h12917, hlam, p13431_0]
                                  · have p13431_0 := h13431c.1
                                    have p13431_1 := h13431c.2.1
                                    have p13431_2 := h13431c.2.2.1
                                    have p13431_3 := h13431c.2.2.2
                                    linarith only [h11559, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13431_1, u0elo1]
                                  · have p13431_0 := h13431c.1
                                    have p13431_1 := h13431c.2.1
                                    have p13431_2 := h13431c.2.2.1
                                    have p13431_3 := h13431c.2.2.2
                                    linarith only [hlam, p13431_0]
                                  · have p13431_0 := h13431c.1
                                    have p13431_1 := h13431c.2.1
                                    have p13431_2 := h13431c.2.2.1
                                    have p13431_3 := h13431c.2.2.2
                                    linarith only [h13024, hlam, p13431_1]
                                  · have p13431_0 := h13431c.1
                                    have p13431_1 := h13431c.2.1
                                    have p13431_2 := h13431c.2.2.1
                                    have p13431_3 := h13431c.2.2.2
                                    linarith only [h11560, hlam, p13431_0]
                                  · have p13431_0 := h13431c.1
                                    have p13431_1 := h13431c.2.1
                                    have p13431_2 := h13431c.2.2.1
                                    have p13431_3 := h13431c.2.2.2
                                    linarith only [h12918, hlam, p13431_0]
                                  · have p13431_0 := h13431c.1
                                    have p13431_1 := h13431c.2.1
                                    have p13431_2 := h13431c.2.2.1
                                    have p13431_3 := h13431c.2.2.2
                                    linarith only [h11560, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13431_1, u0elo1]
                                  · have p13431_0 := h13431c.1
                                    have p13431_1 := h13431c.2.1
                                    have p13431_2 := h13431c.2.2.1
                                    have p13431_3 := h13431c.2.2.2
                                    linarith only [h11560, hc24, hlam, hphi, ht0b, ht45, ht5b, p13431_1, u0elo1]
                                  · have p13431_0 := h13431c.1
                                    have p13431_1 := h13431c.2.1
                                    have p13431_2 := h13431c.2.2.1
                                    have p13431_3 := h13431c.2.2.2
                                    linarith only [hlam, p13431_0]
                                · linarith only [h12915, h13429, hlam, p13363_1, u0elo3]
                                · rcases h2bigk with h13531c | h13531c | h13531c | h13531c | h13531c | h13531c | h13531c | h13531c | h13531c | h13531c | h13531c | h13531c | h13531c | h13531c | h13531c | h13531c | h13531c | h13531c | h13531c | h13531c | h13531c | h13531c | h13531c | h13531c | h13531c
                                  · have p13531_0 := h13531c.1
                                    have p13531_1 := h13531c.2.1
                                    have p13531_2 := h13531c.2.2.1
                                    have p13531_3 := h13531c.2.2.2
                                    linarith only [hlam, p13531_0]
                                  · have p13531_0 := h13531c.1
                                    have p13531_1 := h13531c.2.1
                                    have p13531_2 := h13531c.2.2.1
                                    have p13531_3 := h13531c.2.2.2
                                    linarith only [h0, hlam, p13531_1]
                                  · have p13531_0 := h13531c.1
                                    have p13531_1 := h13531c.2.1
                                    have p13531_2 := h13531c.2.2.1
                                    have p13531_3 := h13531c.2.2.2
                                    rcases p13531_3 (m.d 0 2) (by simp) with h13534 | h13534
                                    · rcases p13531_3 (m.d 1 2) (by simp) with h13535 | h13535
                                      · rcases p13531_3 (m.d 2 3) (by simp) with h13536 | h13536
                                        · linarith only [h13536, hlam, p13531_0]
                                        · rcases p13531_3 (m.d 2 4) (by simp) with h13538 | h13538
                                          · linarith only [h11559, h13538, hlam]
                                          · linarith only [h13020, h13538, hlam]
                                      · linarith only [h12916, h13535, hlam]
                                    · linarith only [h13534, hlam, p13531_0]
                                  · have p13531_0 := h13531c.1
                                    have p13531_1 := h13531c.2.1
                                    have p13531_2 := h13531c.2.2.1
                                    have p13531_3 := h13531c.2.2.2
                                    rcases p13531_3 (m.d 0 2) (by simp) with h13543 | h13543
                                    · rcases p13531_3 (m.d 1 2) (by simp) with h13544 | h13544
                                      · rcases p13531_3 (m.d 2 3) (by simp) with h13545 | h13545
                                        · linarith only [h11558, h13545, hlam]
                                        · rcases p13531_3 (m.d 2 4) (by simp) with h13547 | h13547
                                          · linarith only [h13547, hlam, p13531_0]
                                          · rcases p13531_3 (m.d 2 5) (by simp) with h13549 | h13549
                                            · linarith only [h11560, h13549, hlam]
                                            · linarith only [h13024, h13549, hlam]
                                      · linarith only [h12917, h13544, hlam]
                                    · linarith only [h13543, hlam, p13531_0]
                                  · have p13531_0 := h13531c.1
                                    have p13531_1 := h13531c.2.1
                                    have p13531_2 := h13531c.2.2.1
                                    have p13531_3 := h13531c.2.2.2
                                    rcases p13531_3 (m.d 0 2) (by simp) with h13554 | h13554
                                    · rcases p13531_3 (m.d 1 2) (by simp) with h13555 | h13555
                                      · rcases p13531_3 (m.d 2 3) (by simp) with h13556 | h13556
                                        · linarith only [h11558, h13556, hlam]
                                        · rcases p13531_3 (m.d 2 4) (by simp) with h13558 | h13558
                                          · linarith only [h11559, h13558, hlam]
                                          · rcases p13531_3 (m.d 2 5) (by simp) with h13560 | h13560
                                            · linarith only [h13560, hlam, p13531_0]
                                            · rcases h4bigk with h13562c | h13562c | h13562c | h13562c | h13562c | h13562c | h13562c | h13562c | h13562c | h13562c | h13562c | h13562c | h13562c | h13562c | h13562c | h13562c | h13562c | h13562c | h13562c | h13562c | h13562c | h13562c | h13562c | h13562c | h13562c
                                              · have p13562_0 := h13562c.1
                                                have p13562_1 := h13562c.2.1
                                                have p13562_2 := h13562c.2.2.1
                                                have p13562_3 := h13562c.2.2.2
                                                linarith only [hlam, p13562_0]
                                              · have p13562_0 := h13562c.1
                                                have p13562_1 := h13562c.2.1
                                                have p13562_2 := h13562c.2.2.1
                                                have p13562_3 := h13562c.2.2.2
                                                linarith only [h10058, hlam, p13562_0]
                                              · have p13562_0 := h13562c.1
                                                have p13562_1 := h13562c.2.1
                                                have p13562_2 := h13562c.2.2.1
                                                have p13562_3 := h13562c.2.2.2
                                                rcases p13562_3 (m.d 0 4) (by simp) with h13565 | h13565
                                                · rcases p13562_3 (m.d 1 4) (by simp) with h13566 | h13566
                                                  · rcases p13562_3 (m.d 2 4) (by simp) with h13567 | h13567
                                                    · linarith only [h11559, h13567, hlam]
                                                    · rcases p13562_3 (m.d 3 4) (by simp) with h13569 | h13569
                                                      · rcases p13562_3 (m.d 4 5) (by simp) with h13570 | h13570
                                                        · linarith only [h12915, h13570, hlam]
                                                        · linarith only [h13024, h13570, hlam]
                                                      · linarith only [h13020, h13569, hlam]
                                                  · linarith only [h12917, h13566, hlam]
                                                · linarith only [h11559, h13565, hlam]
                                              · have p13562_0 := h13562c.1
                                                have p13562_1 := h13562c.2.1
                                                have p13562_2 := h13562c.2.2.1
                                                have p13562_3 := h13562c.2.2.2
                                                linarith only [h11561, hlam, p13562_0]
                                              · have p13562_0 := h13562c.1
                                                have p13562_1 := h13562c.2.1
                                                have p13562_2 := h13562c.2.2.1
                                                have p13562_3 := h13562c.2.2.2
                                                linarith only [h11559, h13020, h13024, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13562_1, u0elo1]
                                              · have p13562_0 := h13562c.1
                                                have p13562_1 := h13562c.2.1
                                                have p13562_2 := h13562c.2.2.1
                                                have p13562_3 := h13562c.2.2.2
                                                linarith only [h12915, h6793, hc01, hc14, hlam, hphi, p13363_1, p13562_1]
                                              · have p13562_0 := h13562c.1
                                                have p13562_1 := h13562c.2.1
                                                have p13562_2 := h13562c.2.2.1
                                                have p13562_3 := h13562c.2.2.2
                                                linarith only [hlam, p13562_0]
                                              · have p13562_0 := h13562c.1
                                                have p13562_1 := h13562c.2.1
                                                have p13562_2 := h13562c.2.2.1
                                                have p13562_3 := h13562c.2.2.2
                                                rcases p13562_3 (m.d 0 4) (by simp) with h13580 | h13580
                                                · linarith only [h10058, h13580, hlam]
                                                · linarith only [h11559, h13580, hlam]
                                              · have p13562_0 := h13562c.1
                                                have p13562_1 := h13562c.2.1
                                                have p13562_2 := h13562c.2.2.1
                                                have p13562_3 := h13562c.2.2.2
                                                linarith only [h12919, hlam, p13562_1]
                                              · have p13562_0 := h13562c.1
                                                have p13562_1 := h13562c.2.1
                                                have p13562_2 := h13562c.2.2.1
                                                have p13562_3 := h13562c.2.2.2
                                                linarith only [h12919, h13020, h13024, hc23, hc34, hlam, hphi, p13562_1]
                                              · have p13562_0 := h13562c.1
                                                have p13562_1 := h13562c.2.1
                                                have p13562_2 := h13562c.2.2.1
                                                have p13562_3 := h13562c.2.2.2
                                                linarith only [h11559, hlam, p13562_1]
                                              · have p13562_0 := h13562c.1
                                                have p13562_1 := h13562c.2.1
                                                have p13562_2 := h13562c.2.2.1
                                                have p13562_3 := h13562c.2.2.2
                                                linarith only [h12917, hlam, p13562_1]
                                              · have p13562_0 := h13562c.1
                                                have p13562_1 := h13562c.2.1
                                                have p13562_2 := h13562c.2.2.1
                                                have p13562_3 := h13562c.2.2.2
                                                linarith only [hlam, p13562_0]
                                              · have p13562_0 := h13562c.1
                                                have p13562_1 := h13562c.2.1
                                                have p13562_2 := h13562c.2.2.1
                                                have p13562_3 := h13562c.2.2.2
                                                linarith only [h13020, hlam, p13562_1]
                                              · have p13562_0 := h13562c.1
                                                have p13562_1 := h13562c.2.1
                                                have p13562_2 := h13562c.2.2.1
                                                have p13562_3 := h13562c.2.2.2
                                                linarith only [h13024, hlam, p13562_0]
                                              · have p13562_0 := h13562c.1
                                                have p13562_1 := h13562c.2.1
                                                have p13562_2 := h13562c.2.2.1
                                                have p13562_3 := h13562c.2.2.2
                                                linarith only [h12915, h6793, hc01, hc34, hlam, hphi, ht12, ht23, p13363_1, p13562_1]
                                              · have p13562_0 := h13562c.1
                                                have p13562_1 := h13562c.2.1
                                                have p13562_2 := h13562c.2.2.1
                                                have p13562_3 := h13562c.2.2.2
                                                linarith only [h10058, hc01, hc34, hlam, hphi, ht12, ht23, p13562_1]
                                              · have p13562_0 := h13562c.1
                                                have p13562_1 := h13562c.2.1
                                                have p13562_2 := h13562c.2.2.1
                                                have p13562_3 := h13562c.2.2.2
                                                rcases p13562_3 (m.d 0 4) (by simp) with h13592 | h13592
                                                · linarith only [h11561, h13592, hlam]
                                                · linarith only [h11559, h13592, hlam]
                                              · have p13562_0 := h13562c.1
                                                have p13562_1 := h13562c.2.1
                                                have p13562_2 := h13562c.2.2.1
                                                have p13562_3 := h13562c.2.2.2
                                                linarith only [hlam, p13562_0]
                                              · have p13562_0 := h13562c.1
                                                have p13562_1 := h13562c.2.1
                                                have p13562_2 := h13562c.2.2.1
                                                have p13562_3 := h13562c.2.2.2
                                                linarith only [h13020, h13024, hc23, hc34, hlam, hphi, p13562_1]
                                              · have p13562_0 := h13562c.1
                                                have p13562_1 := h13562c.2.1
                                                have p13562_2 := h13562c.2.2.1
                                                have p13562_3 := h13562c.2.2.2
                                                linarith only [h12915, hlam, p13562_0]
                                              · have p13562_0 := h13562c.1
                                                have p13562_1 := h13562c.2.1
                                                have p13562_2 := h13562c.2.2.1
                                                have p13562_3 := h13562c.2.2.2
                                                linarith only [h13019, hlam, p13562_0]
                                              · have p13562_0 := h13562c.1
                                                have p13562_1 := h13562c.2.1
                                                have p13562_2 := h13562c.2.2.1
                                                have p13562_3 := h13562c.2.2.2
                                                linarith only [h11559, h12915, h13020, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13562_1, u0elo1]
                                              · have p13562_0 := h13562c.1
                                                have p13562_1 := h13562c.2.1
                                                have p13562_2 := h13562c.2.2.1
                                                have p13562_3 := h13562c.2.2.2
                                                linarith only [h13362, hlam, p13562_0]
                                              · have p13562_0 := h13562c.1
                                                have p13562_1 := h13562c.2.1
                                                have p13562_2 := h13562c.2.2.1
                                                have p13562_3 := h13562c.2.2.2
                                                linarith only [hlam, p13562_0]
                                      · linarith only [h12918, h13555, hlam]
                                    · linarith only [h13554, hlam, p13531_0]
                                  · have p13531_0 := h13531c.1
                                    have p13531_1 := h13531c.2.1
                                    have p13531_2 := h13531c.2.2.1
                                    have p13531_3 := h13531c.2.2.2
                                    linarith only [h11559, h12915, h6793, hc01, hc12, hlam, hphi, p13363_1, p13531_1]
                                  · have p13531_0 := h13531c.1
                                    have p13531_1 := h13531c.2.1
                                    have p13531_2 := h13531c.2.2.1
                                    have p13531_3 := h13531c.2.2.2
                                    linarith only [hlam, p13531_0]
                                  · have p13531_0 := h13531c.1
                                    have p13531_1 := h13531c.2.1
                                    have p13531_2 := h13531c.2.2.1
                                    have p13531_3 := h13531c.2.2.2
                                    rcases p13531_3 (m.d 0 2) (by simp) with h13606 | h13606
                                    · linarith only [h0, h13606, hlam]
                                    · linarith only [h11558, h13606, hlam]
                                  · have p13531_0 := h13531c.1
                                    have p13531_1 := h13531c.2.1
                                    have p13531_2 := h13531c.2.2.1
                                    have p13531_3 := h13531c.2.2.2
                                    rcases p13531_3 (m.d 0 2) (by simp) with h13609 | h13609
                                    · linarith only [h0, h13609, hlam]
                                    · linarith only [h11559, h13609, hlam]
                                  · have p13531_0 := h13531c.1
                                    have p13531_1 := h13531c.2.1
                                    have p13531_2 := h13531c.2.2.1
                                    have p13531_3 := h13531c.2.2.2
                                    rcases p13531_3 (m.d 0 2) (by simp) with h13612 | h13612
                                    · linarith only [h0, h13612, hlam]
                                    · linarith only [h11560, h13612, hlam]
                                  · have p13531_0 := h13531c.1
                                    have p13531_1 := h13531c.2.1
                                    have p13531_2 := h13531c.2.2.1
                                    have p13531_3 := h13531c.2.2.2
                                    linarith only [h11558, hlam, p13531_0]
                                  · have p13531_0 := h13531c.1
                                    have p13531_1 := h13531c.2.1
                                    have p13531_2 := h13531c.2.2.1
                                    have p13531_3 := h13531c.2.2.2
                                    linarith only [h12916, hlam, p13531_0]
                                  · have p13531_0 := h13531c.1
                                    have p13531_1 := h13531c.2.1
                                    have p13531_2 := h13531c.2.2.1
                                    have p13531_3 := h13531c.2.2.2
                                    linarith only [hlam, p13531_0]
                                  · have p13531_0 := h13531c.1
                                    have p13531_1 := h13531c.2.1
                                    have p13531_2 := h13531c.2.2.1
                                    have p13531_3 := h13531c.2.2.2
                                    linarith only [h13020, hlam, p13531_0]
                                  · have p13531_0 := h13531c.1
                                    have p13531_1 := h13531c.2.1
                                    have p13531_2 := h13531c.2.2.1
                                    have p13531_3 := h13531c.2.2.2
                                    linarith only [h13022, hlam, p13531_0]
                                  · have p13531_0 := h13531c.1
                                    have p13531_1 := h13531c.2.1
                                    have p13531_2 := h13531c.2.2.1
                                    have p13531_3 := h13531c.2.2.2
                                    linarith only [h11559, hlam, p13531_0]
                                  · have p13531_0 := h13531c.1
                                    have p13531_1 := h13531c.2.1
                                    have p13531_2 := h13531c.2.2.1
                                    have p13531_3 := h13531c.2.2.2
                                    linarith only [h12917, hlam, p13531_0]
                                  · have p13531_0 := h13531c.1
                                    have p13531_1 := h13531c.2.1
                                    have p13531_2 := h13531c.2.2.1
                                    have p13531_3 := h13531c.2.2.2
                                    linarith only [h11559, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13531_1, u0elo1]
                                  · have p13531_0 := h13531c.1
                                    have p13531_1 := h13531c.2.1
                                    have p13531_2 := h13531c.2.2.1
                                    have p13531_3 := h13531c.2.2.2
                                    linarith only [hlam, p13531_0]
                                  · have p13531_0 := h13531c.1
                                    have p13531_1 := h13531c.2.1
                                    have p13531_2 := h13531c.2.2.1
                                    have p13531_3 := h13531c.2.2.2
                                    linarith only [h13024, hlam, p13531_1]
                                  · have p13531_0 := h13531c.1
                                    have p13531_1 := h13531c.2.1
                                    have p13531_2 := h13531c.2.2.1
                                    have p13531_3 := h13531c.2.2.2
                                    linarith only [h11560, hlam, p13531_0]
                                  · have p13531_0 := h13531c.1
                                    have p13531_1 := h13531c.2.1
                                    have p13531_2 := h13531c.2.2.1
                                    have p13531_3 := h13531c.2.2.2
                                    linarith only [h12918, hlam, p13531_0]
                                  · have p13531_0 := h13531c.1
                                    have p13531_1 := h13531c.2.1
                                    have p13531_2 := h13531c.2.2.1
                                    have p13531_3 := h13531c.2.2.2
                                    linarith only [h11560, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13531_1, u0elo1]
                                  · have p13531_0 := h13531c.1
                                    have p13531_1 := h13531c.2.1
                                    have p13531_2 := h13531c.2.2.1
                                    have p13531_3 := h13531c.2.2.2
                                    linarith only [h11559, h12915, h13024, hc24, hlam, hphi, ht0b, ht45, ht5b, p13531_1, u0elo1]
                                  · have p13531_0 := h13531c.1
                                    have p13531_1 := h13531c.2.1
                                    have p13531_2 := h13531c.2.2.1
                                    have p13531_3 := h13531c.2.2.2
                                    linarith only [hlam, p13531_0]
                                · rcases h2bigk with h13630c | h13630c | h13630c | h13630c | h13630c | h13630c | h13630c | h13630c | h13630c | h13630c | h13630c | h13630c | h13630c | h13630c | h13630c | h13630c | h13630c | h13630c | h13630c | h13630c | h13630c | h13630c | h13630c | h13630c | h13630c
                                  · have p13630_0 := h13630c.1
                                    have p13630_1 := h13630c.2.1
                                    have p13630_2 := h13630c.2.2.1
                                    have p13630_3 := h13630c.2.2.2
                                    linarith only [hlam, p13630_0]
                                  · have p13630_0 := h13630c.1
                                    have p13630_1 := h13630c.2.1
                                    have p13630_2 := h13630c.2.2.1
                                    have p13630_3 := h13630c.2.2.2
                                    linarith only [h0, hlam, p13630_1]
                                  · have p13630_0 := h13630c.1
                                    have p13630_1 := h13630c.2.1
                                    have p13630_2 := h13630c.2.2.1
                                    have p13630_3 := h13630c.2.2.2
                                    rcases p13630_3 (m.d 0 2) (by simp) with h13633 | h13633
                                    · rcases p13630_3 (m.d 1 2) (by simp) with h13634 | h13634
                                      · rcases p13630_3 (m.d 2 3) (by simp) with h13635 | h13635
                                        · linarith only [h13635, hlam, p13630_0]
                                        · rcases p13630_3 (m.d 2 4) (by simp) with h13637 | h13637
                                          · linarith only [h11559, h13637, hlam]
                                          · linarith only [h13020, h13637, hlam]
                                      · linarith only [h12916, h13634, hlam]
                                    · linarith only [h13633, hlam, p13630_0]
                                  · have p13630_0 := h13630c.1
                                    have p13630_1 := h13630c.2.1
                                    have p13630_2 := h13630c.2.2.1
                                    have p13630_3 := h13630c.2.2.2
                                    rcases p13630_3 (m.d 0 2) (by simp) with h13642 | h13642
                                    · rcases p13630_3 (m.d 1 2) (by simp) with h13643 | h13643
                                      · rcases p13630_3 (m.d 2 3) (by simp) with h13644 | h13644
                                        · linarith only [h11558, h13644, hlam]
                                        · rcases p13630_3 (m.d 2 4) (by simp) with h13646 | h13646
                                          · linarith only [h13646, hlam, p13630_0]
                                          · rcases p13630_3 (m.d 2 5) (by simp) with h13648 | h13648
                                            · linarith only [h11560, h13648, hlam]
                                            · linarith only [h13024, h13648, hlam]
                                      · linarith only [h12917, h13643, hlam]
                                    · linarith only [h13642, hlam, p13630_0]
                                  · have p13630_0 := h13630c.1
                                    have p13630_1 := h13630c.2.1
                                    have p13630_2 := h13630c.2.2.1
                                    have p13630_3 := h13630c.2.2.2
                                    rcases p13630_3 (m.d 0 2) (by simp) with h13653 | h13653
                                    · rcases p13630_3 (m.d 1 2) (by simp) with h13654 | h13654
                                      · rcases p13630_3 (m.d 2 3) (by simp) with h13655 | h13655
                                        · linarith only [h11558, h13655, hlam]
                                        · rcases p13630_3 (m.d 2 4) (by simp) with h13657 | h13657
                                          · linarith only [h11559, h13657, hlam]
                                          · rcases p13630_3 (m.d 2 5) (by simp) with h13659 | h13659
                                            · linarith only [h13659, hlam, p13630_0]
                                            · rcases h4bigk with h13661c | h13661c | h13661c | h13661c | h13661c | h13661c | h13661c | h13661c | h13661c | h13661c | h13661c | h13661c | h13661c | h13661c | h13661c | h13661c | h13661c | h13661c | h13661c | h13661c | h13661c | h13661c | h13661c | h13661c | h13661c
                                              · have p13661_0 := h13661c.1
                                                have p13661_1 := h13661c.2.1
                                                have p13661_2 := h13661c.2.2.1
                                                have p13661_3 := h13661c.2.2.2
                                                linarith only [hlam, p13661_0]
                                              · have p13661_0 := h13661c.1
                                                have p13661_1 := h13661c.2.1
                                                have p13661_2 := h13661c.2.2.1
                                                have p13661_3 := h13661c.2.2.2
                                                linarith only [h10058, hlam, p13661_0]
                                              · have p13661_0 := h13661c.1
                                                have p13661_1 := h13661c.2.1
                                                have p13661_2 := h13661c.2.2.1
                                                have p13661_3 := h13661c.2.2.2
                                                rcases p13661_3 (m.d 0 4) (by simp) with h13664 | h13664
                                                · rcases p13661_3 (m.d 1 4) (by simp) with h13665 | h13665
                                                  · rcases p13661_3 (m.d 2 4) (by simp) with h13666 | h13666
                                                    · linarith only [h11559, h13666, hlam]
                                                    · rcases p13661_3 (m.d 3 4) (by simp) with h13668 | h13668
                                                      · rcases p13661_3 (m.d 4 5) (by simp) with h13669 | h13669
                                                        · linarith only [h12915, h13669, hlam]
                                                        · linarith only [h13024, h13669, hlam]
                                                      · linarith only [h13020, h13668, hlam]
                                                  · linarith only [h12917, h13665, hlam]
                                                · linarith only [h11559, h13664, hlam]
                                              · have p13661_0 := h13661c.1
                                                have p13661_1 := h13661c.2.1
                                                have p13661_2 := h13661c.2.2.1
                                                have p13661_3 := h13661c.2.2.2
                                                linarith only [h11561, hlam, p13661_0]
                                              · have p13661_0 := h13661c.1
                                                have p13661_1 := h13661c.2.1
                                                have p13661_2 := h13661c.2.2.1
                                                have p13661_3 := h13661c.2.2.2
                                                linarith only [h11559, h13020, h13024, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13661_1, u0elo1]
                                              · have p13661_0 := h13661c.1
                                                have p13661_1 := h13661c.2.1
                                                have p13661_2 := h13661c.2.2.1
                                                have p13661_3 := h13661c.2.2.2
                                                linarith only [h12915, h6793, hc01, hc14, hlam, hphi, p13363_1, p13661_1]
                                              · have p13661_0 := h13661c.1
                                                have p13661_1 := h13661c.2.1
                                                have p13661_2 := h13661c.2.2.1
                                                have p13661_3 := h13661c.2.2.2
                                                linarith only [hlam, p13661_0]
                                              · have p13661_0 := h13661c.1
                                                have p13661_1 := h13661c.2.1
                                                have p13661_2 := h13661c.2.2.1
                                                have p13661_3 := h13661c.2.2.2
                                                rcases p13661_3 (m.d 0 4) (by simp) with h13679 | h13679
                                                · linarith only [h10058, h13679, hlam]
                                                · linarith only [h11559, h13679, hlam]
                                              · have p13661_0 := h13661c.1
                                                have p13661_1 := h13661c.2.1
                                                have p13661_2 := h13661c.2.2.1
                                                have p13661_3 := h13661c.2.2.2
                                                linarith only [h12919, hlam, p13661_1]
                                              · have p13661_0 := h13661c.1
                                                have p13661_1 := h13661c.2.1
                                                have p13661_2 := h13661c.2.2.1
                                                have p13661_3 := h13661c.2.2.2
                                                linarith only [h12919, h13020, h13024, hc23, hc34, hlam, hphi, p13661_1]
                                              · have p13661_0 := h13661c.1
                                                have p13661_1 := h13661c.2.1
                                                have p13661_2 := h13661c.2.2.1
                                                have p13661_3 := h13661c.2.2.2
                                                linarith only [h11559, hlam, p13661_1]
                                              · have p13661_0 := h13661c.1
                                                have p13661_1 := h13661c.2.1
                                                have p13661_2 := h13661c.2.2.1
                                                have p13661_3 := h13661c.2.2.2
                                                linarith only [h12917, hlam, p13661_1]
                                              · have p13661_0 := h13661c.1
                                                have p13661_1 := h13661c.2.1
                                                have p13661_2 := h13661c.2.2.1
                                                have p13661_3 := h13661c.2.2.2
                                                linarith only [hlam, p13661_0]
                                              · have p13661_0 := h13661c.1
                                                have p13661_1 := h13661c.2.1
                                                have p13661_2 := h13661c.2.2.1
                                                have p13661_3 := h13661c.2.2.2
                                                linarith only [h13020, hlam, p13661_1]
                                              · have p13661_0 := h13661c.1
                                                have p13661_1 := h13661c.2.1
                                                have p13661_2 := h13661c.2.2.1
                                                have p13661_3 := h13661c.2.2.2
                                                linarith only [h13024, hlam, p13661_0]
                                              · have p13661_0 := h13661c.1
                                                have p13661_1 := h13661c.2.1
                                                have p13661_2 := h13661c.2.2.1
                                                have p13661_3 := h13661c.2.2.2
                                                linarith only [h12915, h6793, hc01, hc34, hlam, hphi, ht12, ht23, p13363_1, p13661_1]
                                              · have p13661_0 := h13661c.1
                                                have p13661_1 := h13661c.2.1
                                                have p13661_2 := h13661c.2.2.1
                                                have p13661_3 := h13661c.2.2.2
                                                linarith only [h10058, hc01, hc34, hlam, hphi, ht12, ht23, p13661_1]
                                              · have p13661_0 := h13661c.1
                                                have p13661_1 := h13661c.2.1
                                                have p13661_2 := h13661c.2.2.1
                                                have p13661_3 := h13661c.2.2.2
                                                rcases p13661_3 (m.d 0 4) (by simp) with h13691 | h13691
                                                · linarith only [h11561, h13691, hlam]
                                                · linarith only [h11559, h13691, hlam]
                                              · have p13661_0 := h13661c.1
                                                have p13661_1 := h13661c.2.1
                                                have p13661_2 := h13661c.2.2.1
                                                have p13661_3 := h13661c.2.2.2
                                                linarith only [hlam, p13661_0]
                                              · have p13661_0 := h13661c.1
                                                have p13661_1 := h13661c.2.1
                                                have p13661_2 := h13661c.2.2.1
                                                have p13661_3 := h13661c.2.2.2
                                                linarith only [h13020, h13024, hc23, hc34, hlam, hphi, p13661_1]
                                              · have p13661_0 := h13661c.1
                                                have p13661_1 := h13661c.2.1
                                                have p13661_2 := h13661c.2.2.1
                                                have p13661_3 := h13661c.2.2.2
                                                linarith only [h12915, hlam, p13661_0]
                                              · have p13661_0 := h13661c.1
                                                have p13661_1 := h13661c.2.1
                                                have p13661_2 := h13661c.2.2.1
                                                have p13661_3 := h13661c.2.2.2
                                                linarith only [h13019, hlam, p13661_0]
                                              · have p13661_0 := h13661c.1
                                                have p13661_1 := h13661c.2.1
                                                have p13661_2 := h13661c.2.2.1
                                                have p13661_3 := h13661c.2.2.2
                                                linarith only [h11559, h12915, h13020, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13661_1, u0elo1]
                                              · have p13661_0 := h13661c.1
                                                have p13661_1 := h13661c.2.1
                                                have p13661_2 := h13661c.2.2.1
                                                have p13661_3 := h13661c.2.2.2
                                                linarith only [h13362, hlam, p13661_0]
                                              · have p13661_0 := h13661c.1
                                                have p13661_1 := h13661c.2.1
                                                have p13661_2 := h13661c.2.2.1
                                                have p13661_3 := h13661c.2.2.2
                                                linarith only [hlam, p13661_0]
                                      · linarith only [h12918, h13654, hlam]
                                    · linarith only [h13653, hlam, p13630_0]
                                  · have p13630_0 := h13630c.1
                                    have p13630_1 := h13630c.2.1
                                    have p13630_2 := h13630c.2.2.1
                                    have p13630_3 := h13630c.2.2.2
                                    linarith only [h11559, h12915, h6793, hc01, hc12, hlam, hphi, p13363_1, p13630_1]
                                  · have p13630_0 := h13630c.1
                                    have p13630_1 := h13630c.2.1
                                    have p13630_2 := h13630c.2.2.1
                                    have p13630_3 := h13630c.2.2.2
                                    linarith only [hlam, p13630_0]
                                  · have p13630_0 := h13630c.1
                                    have p13630_1 := h13630c.2.1
                                    have p13630_2 := h13630c.2.2.1
                                    have p13630_3 := h13630c.2.2.2
                                    rcases p13630_3 (m.d 0 2) (by simp) with h13705 | h13705
                                    · linarith only [h0, h13705, hlam]
                                    · linarith only [h11558, h13705, hlam]
                                  · have p13630_0 := h13630c.1
                                    have p13630_1 := h13630c.2.1
                                    have p13630_2 := h13630c.2.2.1
                                    have p13630_3 := h13630c.2.2.2
                                    rcases p13630_3 (m.d 0 2) (by simp) with h13708 | h13708
                                    · linarith only [h0, h13708, hlam]
                                    · linarith only [h11559, h13708, hlam]
                                  · have p13630_0 := h13630c.1
                                    have p13630_1 := h13630c.2.1
                                    have p13630_2 := h13630c.2.2.1
                                    have p13630_3 := h13630c.2.2.2
                                    rcases p13630_3 (m.d 0 2) (by simp) with h13711 | h13711
                                    · linarith only [h0, h13711, hlam]
                                    · linarith only [h11560, h13711, hlam]
                                  · have p13630_0 := h13630c.1
                                    have p13630_1 := h13630c.2.1
                                    have p13630_2 := h13630c.2.2.1
                                    have p13630_3 := h13630c.2.2.2
                                    linarith only [h11558, hlam, p13630_0]
                                  · have p13630_0 := h13630c.1
                                    have p13630_1 := h13630c.2.1
                                    have p13630_2 := h13630c.2.2.1
                                    have p13630_3 := h13630c.2.2.2
                                    linarith only [h12916, hlam, p13630_0]
                                  · have p13630_0 := h13630c.1
                                    have p13630_1 := h13630c.2.1
                                    have p13630_2 := h13630c.2.2.1
                                    have p13630_3 := h13630c.2.2.2
                                    linarith only [hlam, p13630_0]
                                  · have p13630_0 := h13630c.1
                                    have p13630_1 := h13630c.2.1
                                    have p13630_2 := h13630c.2.2.1
                                    have p13630_3 := h13630c.2.2.2
                                    linarith only [h13020, hlam, p13630_0]
                                  · have p13630_0 := h13630c.1
                                    have p13630_1 := h13630c.2.1
                                    have p13630_2 := h13630c.2.2.1
                                    have p13630_3 := h13630c.2.2.2
                                    linarith only [h13022, hlam, p13630_0]
                                  · have p13630_0 := h13630c.1
                                    have p13630_1 := h13630c.2.1
                                    have p13630_2 := h13630c.2.2.1
                                    have p13630_3 := h13630c.2.2.2
                                    linarith only [h11559, hlam, p13630_0]
                                  · have p13630_0 := h13630c.1
                                    have p13630_1 := h13630c.2.1
                                    have p13630_2 := h13630c.2.2.1
                                    have p13630_3 := h13630c.2.2.2
                                    linarith only [h12917, hlam, p13630_0]
                                  · have p13630_0 := h13630c.1
                                    have p13630_1 := h13630c.2.1
                                    have p13630_2 := h13630c.2.2.1
                                    have p13630_3 := h13630c.2.2.2
                                    linarith only [h11559, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13630_1, u0elo1]
                                  · have p13630_0 := h13630c.1
                                    have p13630_1 := h13630c.2.1
                                    have p13630_2 := h13630c.2.2.1
                                    have p13630_3 := h13630c.2.2.2
                                    linarith only [hlam, p13630_0]
                                  · have p13630_0 := h13630c.1
                                    have p13630_1 := h13630c.2.1
                                    have p13630_2 := h13630c.2.2.1
                                    have p13630_3 := h13630c.2.2.2
                                    linarith only [h13024, hlam, p13630_1]
                                  · have p13630_0 := h13630c.1
                                    have p13630_1 := h13630c.2.1
                                    have p13630_2 := h13630c.2.2.1
                                    have p13630_3 := h13630c.2.2.2
                                    linarith only [h11560, hlam, p13630_0]
                                  · have p13630_0 := h13630c.1
                                    have p13630_1 := h13630c.2.1
                                    have p13630_2 := h13630c.2.2.1
                                    have p13630_3 := h13630c.2.2.2
                                    linarith only [h12918, hlam, p13630_0]
                                  · have p13630_0 := h13630c.1
                                    have p13630_1 := h13630c.2.1
                                    have p13630_2 := h13630c.2.2.1
                                    have p13630_3 := h13630c.2.2.2
                                    linarith only [h11560, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13630_1, u0elo1]
                                  · have p13630_0 := h13630c.1
                                    have p13630_1 := h13630c.2.1
                                    have p13630_2 := h13630c.2.2.1
                                    have p13630_3 := h13630c.2.2.2
                                    linarith only [h11559, h12915, h13024, hc24, hlam, hphi, ht0b, ht45, ht5b, p13630_1, u0elo1]
                                  · have p13630_0 := h13630c.1
                                    have p13630_1 := h13630c.2.1
                                    have p13630_2 := h13630c.2.2.1
                                    have p13630_3 := h13630c.2.2.2
                                    linarith only [hlam, p13630_0]
                              · linarith only [h12797, h13428, hlam]
                            · linarith only [h11561, h13427, hlam]
                        · linarith only [h11558, h13424, hlam]
                    · have p13363_0 := h13363c.1
                      have p13363_1 := h13363c.2.1
                      have p13363_2 := h13363c.2.2.1
                      have p13363_3 := h13363c.2.2.2
                      linarith only [h12915, hlam, p13363_1]
                    · have p13363_0 := h13363c.1
                      have p13363_1 := h13363c.2.1
                      have p13363_2 := h13363c.2.2.1
                      have p13363_3 := h13363c.2.2.2
                      linarith only [hlam, p13363_0]
                  · linarith only [h11559, h11561, h12915, h13362, h6793, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · linarith only [h10058, h12915, h13019, hlam]
      · linarith only [h0, h11560, h12918, hlam]
    · linarith only [h0, h11559, h12917, hlam]
  · linarith only [h0, h11558, h12916, hlam]

end R2N4
