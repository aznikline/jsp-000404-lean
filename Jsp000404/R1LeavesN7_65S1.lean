import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_65S0

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_0_L_0_L_I_M_LI_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h0elo := hb0.1
  have h2elo := hb2.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h710 | h710
  · rcases m.htr 0 2 4 (by decide) (by decide) with h711 | h711
    · rcases m.htr 0 2 5 (by decide) (by decide) with h712 | h712
      · rcases m.htr 0 3 4 (by decide) (by decide) with h713 | h713
        · rcases m.htr 0 3 5 (by decide) (by decide) with h714 | h714
          · rcases m.htr 0 4 5 (by decide) (by decide) with h715 | h715
            · rcases m.htr 1 2 4 (by decide) (by decide) with h716 | h716
              · rcases m.htr 1 2 5 (by decide) (by decide) with h717 | h717
                · rcases m.htr 1 4 5 (by decide) (by decide) with h718 | h718
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h719 | h719
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h720 | h720
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h721 | h721
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h722 | h722
                          · linarith only [h710, h719, h722, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                          · linarith only [h710, h719, h721, h722, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h725 | h725
                          · linarith only [h710, h713, h721, h725, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                          · rcases h5bigk with h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [hlam, p727_0]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h0, hlam, p727_1]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h0, hc25, hlam, hphi, p727_1, u5elo1]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h0, hc35, hlam, hphi, p727_1, u5elo1]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h0, h719, h721, hc34, hlam, hphi, ht45, p727_1, u5elo1]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [hc05, hlam, hphi, p727_1, u5elo1]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [hlam, p727_0]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [hc25, hlam, hphi, p727_1, u5elo1]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h725, hc34, hlam, hphi, ht45, p727_1, u5elo1]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h719, h721, hc34, hlam, hphi, ht45, p727_1, u5elo1]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h712, hlam, p727_1]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h717, hlam, p727_1]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [hlam, p727_0]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h725, hc34, hlam, hphi, ht45, p727_1, u5elo2]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h721, hlam, p727_1]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h714, hlam, p727_0]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [hc15, hlam, hphi, p727_1, u5elo3]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h720, hlam, p727_0]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [hlam, p727_0]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h725, hlam, p727_1]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h715, hlam, p727_0]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h718, hlam, p727_0]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h716, h718, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p727_1, u2elo1]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h710, h713, h715, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p727_1, u2elo0]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [hlam, p727_0]
                      · linarith only [h710, h714, h719, h720, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h754 | h754
                      · linarith only [h710, h713, h719, h754, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h756 | h756
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h757 | h757
                          · rcases h5bigk with h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c | h758c
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [hlam, p758_0]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h0, hlam, p758_1]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h754, hc23, hlam, hphi, ht34, ht45, p758_1, u5elo0]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h0, h754, hc23, hlam, hphi, ht34, ht45, p758_1, u5elo1]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h0, hc45, hlam, hphi, p758_1, u5elo1]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [hc05, hlam, hphi, p758_1, u5elo1]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [hlam, p758_0]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h754, hc23, hlam, hphi, ht34, ht45, p758_1, u5elo1]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h754, hc23, hlam, hphi, ht34, ht45, p758_1, u5elo1]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [hc45, hlam, hphi, p758_1, u5elo1]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h712, hlam, p758_1]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h717, hlam, p758_1]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [hlam, p758_0]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h754, hlam, p758_1]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [hc45, hlam, hphi, p758_1, u5elo2]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h714, hlam, p758_0]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h710, h713, h757, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p758_1, u2elo0]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h710, h713, h757, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p758_1, u2elo0]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [hlam, p758_0]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h710, h713, h757, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p758_1, u2elo0]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h715, hlam, p758_0]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h718, hlam, p758_0]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h756, hlam, p758_0]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [h757, hlam, p758_0]
                            · have p758_0 := h758c.1
                              have p758_1 := h758c.2.1
                              have p758_2 := h758c.2.2.1
                              have p758_3 := h758c.2.2.2
                              linarith only [hlam, p758_0]
                          · linarith only [h711, h756, h757, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h785 | h785
                          · linarith only [h713, h719, h756, h785, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h715, h719, h785, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h710, h713, h715, h718, hc01, hlam, hphi, ht12, u2elo0]
                · linarith only [h712, h717, hc12, hlam, hphi, u2elo0]
              · linarith only [h711, h716, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h791 | h791
              · rcases m.htr 1 2 5 (by decide) (by decide) with h792 | h792
                · rcases m.htr 1 4 5 (by decide) (by decide) with h793 | h793
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h794 | h794
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h795 | h795
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h796 | h796
                        · linarith only [h711, h715, h796, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h798 | h798
                          · linarith only [h715, h794, h798, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                          · rcases h5bigk with h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c | h800c
                            · have p800_0 := h800c.1
                              have p800_1 := h800c.2.1
                              have p800_2 := h800c.2.2.1
                              have p800_3 := h800c.2.2.2
                              linarith only [hlam, p800_0]
                            · have p800_0 := h800c.1
                              have p800_1 := h800c.2.1
                              have p800_2 := h800c.2.2.1
                              have p800_3 := h800c.2.2.2
                              linarith only [h0, hlam, p800_1]
                            · have p800_0 := h800c.1
                              have p800_1 := h800c.2.1
                              have p800_2 := h800c.2.2.1
                              have p800_3 := h800c.2.2.2
                              linarith only [hc25, hlam, hphi, p800_1, u5elo0]
                            · have p800_0 := h800c.1
                              have p800_1 := h800c.2.1
                              have p800_2 := h800c.2.2.1
                              have p800_3 := h800c.2.2.2
                              linarith only [h715, hc35, hlam, hphi, p800_1, u5elo4]
                            · have p800_0 := h800c.1
                              have p800_1 := h800c.2.1
                              have p800_2 := h800c.2.2.1
                              have p800_3 := h800c.2.2.2
                              linarith only [h715, hlam, p800_1]
                            · have p800_0 := h800c.1
                              have p800_1 := h800c.2.1
                              have p800_2 := h800c.2.2.1
                              have p800_3 := h800c.2.2.2
                              linarith only [hc05, hlam, hphi, p800_1, u5elo1]
                            · have p800_0 := h800c.1
                              have p800_1 := h800c.2.1
                              have p800_2 := h800c.2.2.1
                              have p800_3 := h800c.2.2.2
                              linarith only [hlam, p800_0]
                            · have p800_0 := h800c.1
                              have p800_1 := h800c.2.1
                              have p800_2 := h800c.2.2.1
                              have p800_3 := h800c.2.2.2
                              linarith only [hc25, hlam, hphi, p800_1, u5elo1]
                            · have p800_0 := h800c.1
                              have p800_1 := h800c.2.1
                              have p800_2 := h800c.2.2.1
                              have p800_3 := h800c.2.2.2
                              linarith only [h798, hc34, hlam, hphi, ht45, p800_1, u5elo1]
                            · have p800_0 := h800c.1
                              have p800_1 := h800c.2.1
                              have p800_2 := h800c.2.2.1
                              have p800_3 := h800c.2.2.2
                              linarith only [hc45, hlam, hphi, p800_1, u5elo1]
                            · have p800_0 := h800c.1
                              have p800_1 := h800c.2.1
                              have p800_2 := h800c.2.2.1
                              have p800_3 := h800c.2.2.2
                              linarith only [h712, hlam, p800_1]
                            · have p800_0 := h800c.1
                              have p800_1 := h800c.2.1
                              have p800_2 := h800c.2.2.1
                              have p800_3 := h800c.2.2.2
                              linarith only [h792, hlam, p800_1]
                            · have p800_0 := h800c.1
                              have p800_1 := h800c.2.1
                              have p800_2 := h800c.2.2.1
                              have p800_3 := h800c.2.2.2
                              linarith only [hlam, p800_0]
                            · have p800_0 := h800c.1
                              have p800_1 := h800c.2.1
                              have p800_2 := h800c.2.2.1
                              have p800_3 := h800c.2.2.2
                              linarith only [h798, hc34, hlam, hphi, ht45, p800_1, u5elo2]
                            · have p800_0 := h800c.1
                              have p800_1 := h800c.2.1
                              have p800_2 := h800c.2.2.1
                              have p800_3 := h800c.2.2.2
                              linarith only [h796, hlam, p800_1]
                            · have p800_0 := h800c.1
                              have p800_1 := h800c.2.1
                              have p800_2 := h800c.2.2.1
                              have p800_3 := h800c.2.2.2
                              linarith only [h714, hlam, p800_0]
                            · have p800_0 := h800c.1
                              have p800_1 := h800c.2.1
                              have p800_2 := h800c.2.2.1
                              have p800_3 := h800c.2.2.2
                              linarith only [hc15, hlam, hphi, p800_1, u5elo3]
                            · have p800_0 := h800c.1
                              have p800_1 := h800c.2.1
                              have p800_2 := h800c.2.2.1
                              have p800_3 := h800c.2.2.2
                              linarith only [h795, hlam, p800_0]
                            · have p800_0 := h800c.1
                              have p800_1 := h800c.2.1
                              have p800_2 := h800c.2.2.1
                              have p800_3 := h800c.2.2.2
                              linarith only [hlam, p800_0]
                            · have p800_0 := h800c.1
                              have p800_1 := h800c.2.1
                              have p800_2 := h800c.2.2.1
                              have p800_3 := h800c.2.2.2
                              linarith only [h798, hlam, p800_1]
                            · have p800_0 := h800c.1
                              have p800_1 := h800c.2.1
                              have p800_2 := h800c.2.2.1
                              have p800_3 := h800c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p800_1, u5elo4]
                            · have p800_0 := h800c.1
                              have p800_1 := h800c.2.1
                              have p800_2 := h800c.2.2.1
                              have p800_3 := h800c.2.2.2
                              linarith only [h793, hlam, p800_0]
                            · have p800_0 := h800c.1
                              have p800_1 := h800c.2.1
                              have p800_2 := h800c.2.2.1
                              have p800_3 := h800c.2.2.2
                              linarith only [h791, h793, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p800_1, u2elo1]
                            · have p800_0 := h800c.1
                              have p800_1 := h800c.2.1
                              have p800_2 := h800c.2.2.1
                              have p800_3 := h800c.2.2.2
                              linarith only [h791, h793, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p800_1, u2elo1]
                            · have p800_0 := h800c.1
                              have p800_1 := h800c.2.1
                              have p800_2 := h800c.2.2.1
                              have p800_3 := h800c.2.2.2
                              linarith only [hlam, p800_0]
                      · linarith only [h714, h794, h795, hc34, hlam, hphi, ht45, u5elo0]
                    · linarith only [h713, h715, h791, h793, h794, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h828 | h828
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h829 | h829
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h830 | h830
                        · linarith only [h0, h793, h830, hc01, hlam, hphi, ht12, u2elo3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h832 | h832
                          · linarith only [h715, h828, h832, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                          · rcases h5bigk with h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c | h834c
                            · have p834_0 := h834c.1
                              have p834_1 := h834c.2.1
                              have p834_2 := h834c.2.2.1
                              have p834_3 := h834c.2.2.2
                              linarith only [hlam, p834_0]
                            · have p834_0 := h834c.1
                              have p834_1 := h834c.2.1
                              have p834_2 := h834c.2.2.1
                              have p834_3 := h834c.2.2.2
                              linarith only [h0, hlam, p834_1]
                            · have p834_0 := h834c.1
                              have p834_1 := h834c.2.1
                              have p834_2 := h834c.2.2.1
                              have p834_3 := h834c.2.2.2
                              linarith only [hc25, hlam, hphi, p834_1, u5elo0]
                            · have p834_0 := h834c.1
                              have p834_1 := h834c.2.1
                              have p834_2 := h834c.2.2.1
                              have p834_3 := h834c.2.2.2
                              linarith only [h0, h793, h832, hc34, hlam, hphi, ht45, p834_1, u5elo4]
                            · have p834_0 := h834c.1
                              have p834_1 := h834c.2.1
                              have p834_2 := h834c.2.2.1
                              have p834_3 := h834c.2.2.2
                              linarith only [h715, hlam, p834_1]
                            · have p834_0 := h834c.1
                              have p834_1 := h834c.2.1
                              have p834_2 := h834c.2.2.1
                              have p834_3 := h834c.2.2.2
                              linarith only [h793, hc05, hlam, hphi, p834_1, u5elo4]
                            · have p834_0 := h834c.1
                              have p834_1 := h834c.2.1
                              have p834_2 := h834c.2.2.1
                              have p834_3 := h834c.2.2.2
                              linarith only [hlam, p834_0]
                            · have p834_0 := h834c.1
                              have p834_1 := h834c.2.1
                              have p834_2 := h834c.2.2.1
                              have p834_3 := h834c.2.2.2
                              linarith only [h793, hc25, hlam, hphi, p834_1, u5elo4]
                            · have p834_0 := h834c.1
                              have p834_1 := h834c.2.1
                              have p834_2 := h834c.2.2.1
                              have p834_3 := h834c.2.2.2
                              linarith only [h793, h832, hc34, hlam, hphi, ht45, p834_1, u5elo4]
                            · have p834_0 := h834c.1
                              have p834_1 := h834c.2.1
                              have p834_2 := h834c.2.2.1
                              have p834_3 := h834c.2.2.2
                              linarith only [h793, hlam, p834_1]
                            · have p834_0 := h834c.1
                              have p834_1 := h834c.2.1
                              have p834_2 := h834c.2.2.1
                              have p834_3 := h834c.2.2.2
                              linarith only [h712, hlam, p834_1]
                            · have p834_0 := h834c.1
                              have p834_1 := h834c.2.1
                              have p834_2 := h834c.2.2.1
                              have p834_3 := h834c.2.2.2
                              linarith only [h792, hlam, p834_1]
                            · have p834_0 := h834c.1
                              have p834_1 := h834c.2.1
                              have p834_2 := h834c.2.2.1
                              have p834_3 := h834c.2.2.2
                              linarith only [hlam, p834_0]
                            · have p834_0 := h834c.1
                              have p834_1 := h834c.2.1
                              have p834_2 := h834c.2.2.1
                              have p834_3 := h834c.2.2.2
                              linarith only [h832, hc34, hlam, hphi, ht45, p834_1, u5elo2]
                            · have p834_0 := h834c.1
                              have p834_1 := h834c.2.1
                              have p834_2 := h834c.2.2.1
                              have p834_3 := h834c.2.2.2
                              linarith only [h830, hlam, p834_1]
                            · have p834_0 := h834c.1
                              have p834_1 := h834c.2.1
                              have p834_2 := h834c.2.2.1
                              have p834_3 := h834c.2.2.2
                              linarith only [h714, hlam, p834_0]
                            · have p834_0 := h834c.1
                              have p834_1 := h834c.2.1
                              have p834_2 := h834c.2.2.1
                              have p834_3 := h834c.2.2.2
                              linarith only [hc15, hlam, hphi, p834_1, u5elo3]
                            · have p834_0 := h834c.1
                              have p834_1 := h834c.2.1
                              have p834_2 := h834c.2.2.1
                              have p834_3 := h834c.2.2.2
                              linarith only [h829, hlam, p834_0]
                            · have p834_0 := h834c.1
                              have p834_1 := h834c.2.1
                              have p834_2 := h834c.2.2.1
                              have p834_3 := h834c.2.2.2
                              linarith only [hlam, p834_0]
                            · have p834_0 := h834c.1
                              have p834_1 := h834c.2.1
                              have p834_2 := h834c.2.2.1
                              have p834_3 := h834c.2.2.2
                              linarith only [h832, hlam, p834_1]
                            · have p834_0 := h834c.1
                              have p834_1 := h834c.2.1
                              have p834_2 := h834c.2.2.1
                              have p834_3 := h834c.2.2.2
                              linarith only [hc05, hlam, hphi, p834_1, u5elo4]
                            · have p834_0 := h834c.1
                              have p834_1 := h834c.2.1
                              have p834_2 := h834c.2.2.1
                              have p834_3 := h834c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p834_1, u5elo4]
                            · have p834_0 := h834c.1
                              have p834_1 := h834c.2.1
                              have p834_2 := h834c.2.2.1
                              have p834_3 := h834c.2.2.2
                              linarith only [h829, hc35, hlam, hphi, p834_1, u5elo4]
                            · have p834_0 := h834c.1
                              have p834_1 := h834c.2.1
                              have p834_2 := h834c.2.2.1
                              have p834_3 := h834c.2.2.2
                              linarith only [hc35, hlam, hphi, p834_1, u5elo4]
                            · have p834_0 := h834c.1
                              have p834_1 := h834c.2.1
                              have p834_2 := h834c.2.2.1
                              have p834_3 := h834c.2.2.2
                              linarith only [hlam, p834_0]
                      · linarith only [h710, h714, h828, h829, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                    · linarith only [h713, h715, h828, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h712, h792, hc12, hlam, hphi, u2elo0]
              · linarith only [h711, h715, h791, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
          · linarith only [h713, h714, hc34, hlam, hphi, ht45, u5elo3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h865 | h865
          · rcases m.htr 0 4 5 (by decide) (by decide) with h866 | h866
            · rcases m.htr 1 2 4 (by decide) (by decide) with h867 | h867
              · rcases m.htr 1 2 5 (by decide) (by decide) with h868 | h868
                · rcases m.htr 1 4 5 (by decide) (by decide) with h869 | h869
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h870 | h870
                    · linarith only [h713, h865, h870, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h872 | h872
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h873 | h873
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h874 | h874
                          · rcases h5bigk with h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c | h875c
                            · have p875_0 := h875c.1
                              have p875_1 := h875c.2.1
                              have p875_2 := h875c.2.2.1
                              have p875_3 := h875c.2.2.2
                              linarith only [hlam, p875_0]
                            · have p875_0 := h875c.1
                              have p875_1 := h875c.2.1
                              have p875_2 := h875c.2.2.1
                              have p875_3 := h875c.2.2.2
                              linarith only [h0, hlam, p875_1]
                            · have p875_0 := h875c.1
                              have p875_1 := h875c.2.1
                              have p875_2 := h875c.2.2.1
                              have p875_3 := h875c.2.2.2
                              linarith only [hc25, hlam, hphi, p875_1, u5elo0]
                            · have p875_0 := h875c.1
                              have p875_1 := h875c.2.1
                              have p875_2 := h875c.2.2.1
                              have p875_3 := h875c.2.2.2
                              linarith only [h0, h874, hc45, hlam, hphi, p875_1, u5elo1]
                            · have p875_0 := h875c.1
                              have p875_1 := h875c.2.1
                              have p875_2 := h875c.2.2.1
                              have p875_3 := h875c.2.2.2
                              linarith only [h0, hc45, hlam, hphi, p875_1, u5elo1]
                            · have p875_0 := h875c.1
                              have p875_1 := h875c.2.1
                              have p875_2 := h875c.2.2.1
                              have p875_3 := h875c.2.2.2
                              linarith only [hc05, hlam, hphi, p875_1, u5elo1]
                            · have p875_0 := h875c.1
                              have p875_1 := h875c.2.1
                              have p875_2 := h875c.2.2.1
                              have p875_3 := h875c.2.2.2
                              linarith only [hlam, p875_0]
                            · have p875_0 := h875c.1
                              have p875_1 := h875c.2.1
                              have p875_2 := h875c.2.2.1
                              have p875_3 := h875c.2.2.2
                              linarith only [hc25, hlam, hphi, p875_1, u5elo1]
                            · have p875_0 := h875c.1
                              have p875_1 := h875c.2.1
                              have p875_2 := h875c.2.2.1
                              have p875_3 := h875c.2.2.2
                              linarith only [h874, hc45, hlam, hphi, p875_1, u5elo1]
                            · have p875_0 := h875c.1
                              have p875_1 := h875c.2.1
                              have p875_2 := h875c.2.2.1
                              have p875_3 := h875c.2.2.2
                              linarith only [hc45, hlam, hphi, p875_1, u5elo1]
                            · have p875_0 := h875c.1
                              have p875_1 := h875c.2.1
                              have p875_2 := h875c.2.2.1
                              have p875_3 := h875c.2.2.2
                              linarith only [h712, hlam, p875_1]
                            · have p875_0 := h875c.1
                              have p875_1 := h875c.2.1
                              have p875_2 := h875c.2.2.1
                              have p875_3 := h875c.2.2.2
                              linarith only [h868, hlam, p875_1]
                            · have p875_0 := h875c.1
                              have p875_1 := h875c.2.1
                              have p875_2 := h875c.2.2.1
                              have p875_3 := h875c.2.2.2
                              linarith only [hlam, p875_0]
                            · have p875_0 := h875c.1
                              have p875_1 := h875c.2.1
                              have p875_2 := h875c.2.2.1
                              have p875_3 := h875c.2.2.2
                              linarith only [h874, hc45, hlam, hphi, p875_1, u5elo2]
                            · have p875_0 := h875c.1
                              have p875_1 := h875c.2.1
                              have p875_2 := h875c.2.2.1
                              have p875_3 := h875c.2.2.2
                              linarith only [h711, h870, h872, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p875_1, u2elo0]
                            · have p875_0 := h875c.1
                              have p875_1 := h875c.2.1
                              have p875_2 := h875c.2.2.1
                              have p875_3 := h875c.2.2.2
                              linarith only [h865, hlam, p875_0]
                            · have p875_0 := h875c.1
                              have p875_1 := h875c.2.1
                              have p875_2 := h875c.2.2.1
                              have p875_3 := h875c.2.2.2
                              linarith only [hc15, hlam, hphi, p875_1, u5elo3]
                            · have p875_0 := h875c.1
                              have p875_1 := h875c.2.1
                              have p875_2 := h875c.2.2.1
                              have p875_3 := h875c.2.2.2
                              linarith only [h872, hlam, p875_0]
                            · have p875_0 := h875c.1
                              have p875_1 := h875c.2.1
                              have p875_2 := h875c.2.2.1
                              have p875_3 := h875c.2.2.2
                              linarith only [hlam, p875_0]
                            · have p875_0 := h875c.1
                              have p875_1 := h875c.2.1
                              have p875_2 := h875c.2.2.1
                              have p875_3 := h875c.2.2.2
                              linarith only [h711, h870, h872, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p875_1, u2elo0]
                            · have p875_0 := h875c.1
                              have p875_1 := h875c.2.1
                              have p875_2 := h875c.2.2.1
                              have p875_3 := h875c.2.2.2
                              linarith only [h866, hlam, p875_0]
                            · have p875_0 := h875c.1
                              have p875_1 := h875c.2.1
                              have p875_2 := h875c.2.2.1
                              have p875_3 := h875c.2.2.2
                              linarith only [h869, hlam, p875_0]
                            · have p875_0 := h875c.1
                              have p875_1 := h875c.2.1
                              have p875_2 := h875c.2.2.1
                              have p875_3 := h875c.2.2.2
                              linarith only [h873, hlam, p875_0]
                            · have p875_0 := h875c.1
                              have p875_1 := h875c.2.1
                              have p875_2 := h875c.2.2.1
                              have p875_3 := h875c.2.2.2
                              linarith only [h874, hlam, p875_0]
                            · have p875_0 := h875c.1
                              have p875_1 := h875c.2.1
                              have p875_2 := h875c.2.2.1
                              have p875_3 := h875c.2.2.2
                              linarith only [hlam, p875_0]
                          · linarith only [h713, h874, hc03, hlam, hphi, ht34, ht45, u5elo4]
                        · linarith only [h866, h870, h872, h873, hc35, hlam, hphi, u5elo0]
                      · linarith only [h713, h865, h872, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h711, h866, h869, hc01, hlam, hphi, ht12, u2elo0]
                · linarith only [h712, h868, hc12, hlam, hphi, u2elo0]
              · linarith only [h711, h867, hc12, hlam, hphi, u2elo0]
            · linarith only [h713, h865, h866, hc35, hlam, hphi, u5elo4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h908 | h908
            · rcases m.htr 1 2 4 (by decide) (by decide) with h909 | h909
              · rcases m.htr 1 2 5 (by decide) (by decide) with h910 | h910
                · rcases m.htr 1 4 5 (by decide) (by decide) with h911 | h911
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h912 | h912
                    · linarith only [h710, h865, h912, hc34, hlam, hphi, ht45, u5elo3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h914 | h914
                      · linarith only [h710, h865, h914, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h916 | h916
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h917 | h917
                          · rcases h5bigk with h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c | h918c
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [hlam, p918_0]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [h0, hlam, p918_1]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [hc25, hlam, hphi, p918_1, u5elo0]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [h865, hlam, p918_1]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [h0, hc45, hlam, hphi, p918_1, u5elo1]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [hc05, hlam, hphi, p918_1, u5elo1]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [hlam, p918_0]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [hc25, hlam, hphi, p918_1, u5elo1]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [h865, hc03, hlam, hphi, ht34, ht45, p918_1, u5elo1]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [hc45, hlam, hphi, p918_1, u5elo1]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [h712, hlam, p918_1]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [h910, hlam, p918_1]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [hlam, p918_0]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [h914, hlam, p918_1]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [hc45, hlam, hphi, p918_1, u5elo2]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [hc05, hlam, hphi, p918_1, u5elo3]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [hc15, hlam, hphi, p918_1, u5elo3]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [h914, hc23, hlam, hphi, ht34, ht45, p918_1, u5elo3]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [hlam, p918_0]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [hc45, hlam, hphi, p918_1, u5elo3]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [h908, hlam, p918_0]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [h911, hlam, p918_0]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [h916, hlam, p918_0]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [h917, hlam, p918_0]
                            · have p918_0 := h918c.1
                              have p918_1 := h918c.2.1
                              have p918_2 := h918c.2.2.1
                              have p918_3 := h918c.2.2.2
                              linarith only [hlam, p918_0]
                          · linarith only [h710, h713, h917, hc23, hlam, hphi, ht34, ht45, u5elo4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h945 | h945
                          · rcases h5bigk with h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c | h946c
                            · have p946_0 := h946c.1
                              have p946_1 := h946c.2.1
                              have p946_2 := h946c.2.2.1
                              have p946_3 := h946c.2.2.2
                              linarith only [hlam, p946_0]
                            · have p946_0 := h946c.1
                              have p946_1 := h946c.2.1
                              have p946_2 := h946c.2.2.1
                              have p946_3 := h946c.2.2.2
                              linarith only [h0, hlam, p946_1]
                            · have p946_0 := h946c.1
                              have p946_1 := h946c.2.1
                              have p946_2 := h946c.2.2.1
                              have p946_3 := h946c.2.2.2
                              linarith only [h912, h916, hc23, hlam, hphi, ht34, ht45, p946_1, u5elo0]
                            · have p946_0 := h946c.1
                              have p946_1 := h946c.2.1
                              have p946_2 := h946c.2.2.1
                              have p946_3 := h946c.2.2.2
                              linarith only [h865, hlam, p946_1]
                            · have p946_0 := h946c.1
                              have p946_1 := h946c.2.1
                              have p946_2 := h946c.2.2.1
                              have p946_3 := h946c.2.2.2
                              linarith only [h0, hc45, hlam, hphi, p946_1, u5elo1]
                            · have p946_0 := h946c.1
                              have p946_1 := h946c.2.1
                              have p946_2 := h946c.2.2.1
                              have p946_3 := h946c.2.2.2
                              linarith only [hc05, hlam, hphi, p946_1, u5elo1]
                            · have p946_0 := h946c.1
                              have p946_1 := h946c.2.1
                              have p946_2 := h946c.2.2.1
                              have p946_3 := h946c.2.2.2
                              linarith only [hlam, p946_0]
                            · have p946_0 := h946c.1
                              have p946_1 := h946c.2.1
                              have p946_2 := h946c.2.2.1
                              have p946_3 := h946c.2.2.2
                              linarith only [h912, h916, hc23, hlam, hphi, ht34, ht45, p946_1, u5elo1]
                            · have p946_0 := h946c.1
                              have p946_1 := h946c.2.1
                              have p946_2 := h946c.2.2.1
                              have p946_3 := h946c.2.2.2
                              linarith only [hc35, hlam, hphi, p946_1, u5elo1]
                            · have p946_0 := h946c.1
                              have p946_1 := h946c.2.1
                              have p946_2 := h946c.2.2.1
                              have p946_3 := h946c.2.2.2
                              linarith only [h912, h916, hc23, hlam, hphi, ht34, ht45, p946_1, u5elo1]
                            · have p946_0 := h946c.1
                              have p946_1 := h946c.2.1
                              have p946_2 := h946c.2.2.1
                              have p946_3 := h946c.2.2.2
                              linarith only [h712, hlam, p946_1]
                            · have p946_0 := h946c.1
                              have p946_1 := h946c.2.1
                              have p946_2 := h946c.2.2.1
                              have p946_3 := h946c.2.2.2
                              linarith only [h910, hlam, p946_1]
                            · have p946_0 := h946c.1
                              have p946_1 := h946c.2.1
                              have p946_2 := h946c.2.2.1
                              have p946_3 := h946c.2.2.2
                              linarith only [hlam, p946_0]
                            · have p946_0 := h946c.1
                              have p946_1 := h946c.2.1
                              have p946_2 := h946c.2.2.1
                              have p946_3 := h946c.2.2.2
                              linarith only [h914, hlam, p946_1]
                            · have p946_0 := h946c.1
                              have p946_1 := h946c.2.1
                              have p946_2 := h946c.2.2.1
                              have p946_3 := h946c.2.2.2
                              linarith only [h916, hlam, p946_1]
                            · have p946_0 := h946c.1
                              have p946_1 := h946c.2.1
                              have p946_2 := h946c.2.2.1
                              have p946_3 := h946c.2.2.2
                              linarith only [h908, h912, h916, hc23, hc35, hlam, hphi, p946_1]
                            · have p946_0 := h946c.1
                              have p946_1 := h946c.2.1
                              have p946_2 := h946c.2.2.1
                              have p946_3 := h946c.2.2.2
                              linarith only [hc15, hlam, hphi, p946_1, u5elo3]
                            · have p946_0 := h946c.1
                              have p946_1 := h946c.2.1
                              have p946_2 := h946c.2.2.1
                              have p946_3 := h946c.2.2.2
                              linarith only [h912, h916, hc23, hlam, hphi, ht34, ht45, p946_1, u5elo3]
                            · have p946_0 := h946c.1
                              have p946_1 := h946c.2.1
                              have p946_2 := h946c.2.2.1
                              have p946_3 := h946c.2.2.2
                              linarith only [hlam, p946_0]
                            · have p946_0 := h946c.1
                              have p946_1 := h946c.2.1
                              have p946_2 := h946c.2.2.1
                              have p946_3 := h946c.2.2.2
                              linarith only [h912, h916, hc23, hlam, hphi, ht34, ht45, p946_1, u5elo3]
                            · have p946_0 := h946c.1
                              have p946_1 := h946c.2.1
                              have p946_2 := h946c.2.2.1
                              have p946_3 := h946c.2.2.2
                              linarith only [h908, hlam, p946_0]
                            · have p946_0 := h946c.1
                              have p946_1 := h946c.2.1
                              have p946_2 := h946c.2.2.1
                              have p946_3 := h946c.2.2.2
                              linarith only [h911, hlam, p946_0]
                            · have p946_0 := h946c.1
                              have p946_1 := h946c.2.1
                              have p946_2 := h946c.2.2.1
                              have p946_3 := h946c.2.2.2
                              linarith only [h908, h912, h916, hc23, hlam, hphi, ht34, ht45, p946_1, u5elo0]
                            · have p946_0 := h946c.1
                              have p946_1 := h946c.2.1
                              have p946_2 := h946c.2.2.1
                              have p946_3 := h946c.2.2.2
                              linarith only [h945, hlam, p946_0]
                            · have p946_0 := h946c.1
                              have p946_1 := h946c.2.1
                              have p946_2 := h946c.2.2.1
                              have p946_3 := h946c.2.2.2
                              linarith only [hlam, p946_0]
                          · linarith only [h713, h908, h945, hlam]
                  · linarith only [h0, h711, h908, h911, hc01, hlam, hphi, ht12, u2elo0]
                · linarith only [h712, h910, hc12, hlam, hphi, u2elo0]
              · linarith only [h711, h909, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h976 | h976
              · rcases m.htr 1 2 5 (by decide) (by decide) with h977 | h977
                · rcases m.htr 1 4 5 (by decide) (by decide) with h978 | h978
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h979 | h979
                    · linarith only [h710, h713, h979, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h981 | h981
                      · linarith only [h710, h713, h908, h976, h978, h981, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h983 | h983
                        · linarith only [h711, h908, h983, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h985 | h985
                          · rcases h5bigk with h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c | h986c
                            · have p986_0 := h986c.1
                              have p986_1 := h986c.2.1
                              have p986_2 := h986c.2.2.1
                              have p986_3 := h986c.2.2.2
                              linarith only [hlam, p986_0]
                            · have p986_0 := h986c.1
                              have p986_1 := h986c.2.1
                              have p986_2 := h986c.2.2.1
                              have p986_3 := h986c.2.2.2
                              linarith only [h0, hlam, p986_1]
                            · have p986_0 := h986c.1
                              have p986_1 := h986c.2.1
                              have p986_2 := h986c.2.2.1
                              have p986_3 := h986c.2.2.2
                              linarith only [h908, h976, h978, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p986_1, u2elo1]
                            · have p986_0 := h986c.1
                              have p986_1 := h986c.2.1
                              have p986_2 := h986c.2.2.1
                              have p986_3 := h986c.2.2.2
                              linarith only [h865, hlam, p986_1]
                            · have p986_0 := h986c.1
                              have p986_1 := h986c.2.1
                              have p986_2 := h986c.2.2.1
                              have p986_3 := h986c.2.2.2
                              linarith only [h908, hlam, p986_1]
                            · have p986_0 := h986c.1
                              have p986_1 := h986c.2.1
                              have p986_2 := h986c.2.2.1
                              have p986_3 := h986c.2.2.2
                              linarith only [hc05, hlam, hphi, p986_1, u5elo1]
                            · have p986_0 := h986c.1
                              have p986_1 := h986c.2.1
                              have p986_2 := h986c.2.2.1
                              have p986_3 := h986c.2.2.2
                              linarith only [hlam, p986_0]
                            · have p986_0 := h986c.1
                              have p986_1 := h986c.2.1
                              have p986_2 := h986c.2.2.1
                              have p986_3 := h986c.2.2.2
                              linarith only [hc25, hlam, hphi, p986_1, u5elo1]
                            · have p986_0 := h986c.1
                              have p986_1 := h986c.2.1
                              have p986_2 := h986c.2.2.1
                              have p986_3 := h986c.2.2.2
                              linarith only [h710, h713, h908, h985, hc23, hlam, hphi, ht34, ht45, p986_1, u5elo1]
                            · have p986_0 := h986c.1
                              have p986_1 := h986c.2.1
                              have p986_2 := h986c.2.2.1
                              have p986_3 := h986c.2.2.2
                              linarith only [h710, h713, h908, hc23, hlam, hphi, ht34, ht45, p986_1, u5elo1]
                            · have p986_0 := h986c.1
                              have p986_1 := h986c.2.1
                              have p986_2 := h986c.2.2.1
                              have p986_3 := h986c.2.2.2
                              linarith only [h712, hlam, p986_1]
                            · have p986_0 := h986c.1
                              have p986_1 := h986c.2.1
                              have p986_2 := h986c.2.2.1
                              have p986_3 := h986c.2.2.2
                              linarith only [h977, hlam, p986_1]
                            · have p986_0 := h986c.1
                              have p986_1 := h986c.2.1
                              have p986_2 := h986c.2.2.1
                              have p986_3 := h986c.2.2.2
                              linarith only [hlam, p986_0]
                            · have p986_0 := h986c.1
                              have p986_1 := h986c.2.1
                              have p986_2 := h986c.2.2.1
                              have p986_3 := h986c.2.2.2
                              linarith only [h981, hlam, p986_1]
                            · have p986_0 := h986c.1
                              have p986_1 := h986c.2.1
                              have p986_2 := h986c.2.2.1
                              have p986_3 := h986c.2.2.2
                              linarith only [h983, hlam, p986_1]
                            · have p986_0 := h986c.1
                              have p986_1 := h986c.2.1
                              have p986_2 := h986c.2.2.1
                              have p986_3 := h986c.2.2.2
                              linarith only [h0, h710, h713, h908, h976, h978, hc01, hc23, hlam, hphi, ht12, ht34, ht45, p986_1, u2elo1, u5elo3]
                            · have p986_0 := h986c.1
                              have p986_1 := h986c.2.1
                              have p986_2 := h986c.2.2.1
                              have p986_3 := h986c.2.2.2
                              linarith only [hc15, hlam, hphi, p986_1, u5elo3]
                            · have p986_0 := h986c.1
                              have p986_1 := h986c.2.1
                              have p986_2 := h986c.2.2.1
                              have p986_3 := h986c.2.2.2
                              linarith only [h979, h983, hc23, hlam, hphi, ht34, ht45, p986_1, u5elo3]
                            · have p986_0 := h986c.1
                              have p986_1 := h986c.2.1
                              have p986_2 := h986c.2.2.1
                              have p986_3 := h986c.2.2.2
                              linarith only [hlam, p986_0]
                            · have p986_0 := h986c.1
                              have p986_1 := h986c.2.1
                              have p986_2 := h986c.2.2.1
                              have p986_3 := h986c.2.2.2
                              linarith only [h710, h713, h908, hc23, hlam, hphi, ht34, ht45, p986_1, u5elo3]
                            · have p986_0 := h986c.1
                              have p986_1 := h986c.2.1
                              have p986_2 := h986c.2.2.1
                              have p986_3 := h986c.2.2.2
                              linarith only [h0, h976, h978, hc01, hlam, hphi, ht12, p986_1, u2elo1]
                            · have p986_0 := h986c.1
                              have p986_1 := h986c.2.1
                              have p986_2 := h986c.2.2.1
                              have p986_3 := h986c.2.2.2
                              linarith only [h978, hlam, p986_0]
                            · have p986_0 := h986c.1
                              have p986_1 := h986c.2.1
                              have p986_2 := h986c.2.2.1
                              have p986_3 := h986c.2.2.2
                              linarith only [h976, h978, h979, h983, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p986_1, u2elo1]
                            · have p986_0 := h986c.1
                              have p986_1 := h986c.2.1
                              have p986_2 := h986c.2.2.1
                              have p986_3 := h986c.2.2.2
                              linarith only [h985, hlam, p986_0]
                            · have p986_0 := h986c.1
                              have p986_1 := h986c.2.1
                              have p986_2 := h986c.2.2.1
                              have p986_3 := h986c.2.2.2
                              linarith only [hlam, p986_0]
                          · linarith only [h713, h976, h978, h985, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1013 | h1013
                    · linarith only [h1013, h710, h713, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1015 | h1015
                      · linarith only [h1015, h710, h865, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1017 | h1017
                        · linarith only [h1017, h710, h711, h713, h908, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1019 | h1019
                          · rcases h5bigk with h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c
                            · have p1020_0 := h1020c.1
                              have p1020_1 := h1020c.2.1
                              have p1020_2 := h1020c.2.2.1
                              have p1020_3 := h1020c.2.2.2
                              linarith only [hlam, p1020_0]
                            · have p1020_0 := h1020c.1
                              have p1020_1 := h1020c.2.1
                              have p1020_2 := h1020c.2.2.1
                              have p1020_3 := h1020c.2.2.2
                              linarith only [h0, hlam, p1020_1]
                            · have p1020_0 := h1020c.1
                              have p1020_1 := h1020c.2.1
                              have p1020_2 := h1020c.2.2.1
                              have p1020_3 := h1020c.2.2.2
                              linarith only [h1013, h1017, hc23, hlam, hphi, ht34, ht45, p1020_1, u5elo0]
                            · have p1020_0 := h1020c.1
                              have p1020_1 := h1020c.2.1
                              have p1020_2 := h1020c.2.2.1
                              have p1020_3 := h1020c.2.2.2
                              linarith only [h865, hlam, p1020_1]
                            · have p1020_0 := h1020c.1
                              have p1020_1 := h1020c.2.1
                              have p1020_2 := h1020c.2.2.1
                              have p1020_3 := h1020c.2.2.2
                              linarith only [h908, hlam, p1020_1]
                            · have p1020_0 := h1020c.1
                              have p1020_1 := h1020c.2.1
                              have p1020_2 := h1020c.2.2.1
                              have p1020_3 := h1020c.2.2.2
                              linarith only [h1019, h978, hc05, hlam, hphi, p1020_1, u5elo3]
                            · have p1020_0 := h1020c.1
                              have p1020_1 := h1020c.2.1
                              have p1020_2 := h1020c.2.2.1
                              have p1020_3 := h1020c.2.2.2
                              linarith only [hlam, p1020_0]
                            · have p1020_0 := h1020c.1
                              have p1020_1 := h1020c.2.1
                              have p1020_2 := h1020c.2.2.1
                              have p1020_3 := h1020c.2.2.2
                              linarith only [h1013, h1017, h1019, h978, hc23, hlam, hphi, ht34, ht45, p1020_1, u5elo3]
                            · have p1020_0 := h1020c.1
                              have p1020_1 := h1020c.2.1
                              have p1020_2 := h1020c.2.2.1
                              have p1020_3 := h1020c.2.2.2
                              linarith only [h1019, h978, hlam, p1020_1]
                            · have p1020_0 := h1020c.1
                              have p1020_1 := h1020c.2.1
                              have p1020_2 := h1020c.2.2.1
                              have p1020_3 := h1020c.2.2.2
                              linarith only [h978, hlam, p1020_1]
                            · have p1020_0 := h1020c.1
                              have p1020_1 := h1020c.2.1
                              have p1020_2 := h1020c.2.2.1
                              have p1020_3 := h1020c.2.2.2
                              linarith only [h712, hlam, p1020_1]
                            · have p1020_0 := h1020c.1
                              have p1020_1 := h1020c.2.1
                              have p1020_2 := h1020c.2.2.1
                              have p1020_3 := h1020c.2.2.2
                              linarith only [h977, hlam, p1020_1]
                            · have p1020_0 := h1020c.1
                              have p1020_1 := h1020c.2.1
                              have p1020_2 := h1020c.2.2.1
                              have p1020_3 := h1020c.2.2.2
                              linarith only [hlam, p1020_0]
                            · have p1020_0 := h1020c.1
                              have p1020_1 := h1020c.2.1
                              have p1020_2 := h1020c.2.2.1
                              have p1020_3 := h1020c.2.2.2
                              linarith only [h1015, hlam, p1020_1]
                            · have p1020_0 := h1020c.1
                              have p1020_1 := h1020c.2.1
                              have p1020_2 := h1020c.2.2.1
                              have p1020_3 := h1020c.2.2.2
                              linarith only [h1017, hlam, p1020_1]
                            · have p1020_0 := h1020c.1
                              have p1020_1 := h1020c.2.1
                              have p1020_2 := h1020c.2.2.1
                              have p1020_3 := h1020c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1020_1, u5elo3]
                            · have p1020_0 := h1020c.1
                              have p1020_1 := h1020c.2.1
                              have p1020_2 := h1020c.2.2.1
                              have p1020_3 := h1020c.2.2.2
                              linarith only [hc15, hlam, hphi, p1020_1, u5elo3]
                            · have p1020_0 := h1020c.1
                              have p1020_1 := h1020c.2.1
                              have p1020_2 := h1020c.2.2.1
                              have p1020_3 := h1020c.2.2.2
                              linarith only [h1013, h1017, hc23, hlam, hphi, ht34, ht45, p1020_1, u5elo3]
                            · have p1020_0 := h1020c.1
                              have p1020_1 := h1020c.2.1
                              have p1020_2 := h1020c.2.2.1
                              have p1020_3 := h1020c.2.2.2
                              linarith only [hlam, p1020_0]
                            · have p1020_0 := h1020c.1
                              have p1020_1 := h1020c.2.1
                              have p1020_2 := h1020c.2.2.1
                              have p1020_3 := h1020c.2.2.2
                              linarith only [h978, hc14, hlam, hphi, ht45, p1020_1, u5elo3]
                            · have p1020_0 := h1020c.1
                              have p1020_1 := h1020c.2.1
                              have p1020_2 := h1020c.2.2.1
                              have p1020_3 := h1020c.2.2.2
                              linarith only [h0, h1019, hc01, hc34, hlam, hphi, ht12, ht23, p1020_1]
                            · have p1020_0 := h1020c.1
                              have p1020_1 := h1020c.2.1
                              have p1020_2 := h1020c.2.2.1
                              have p1020_3 := h1020c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1020_1, u5elo4]
                            · have p1020_0 := h1020c.1
                              have p1020_1 := h1020c.2.1
                              have p1020_2 := h1020c.2.2.1
                              have p1020_3 := h1020c.2.2.2
                              linarith only [h1013, h1017, hc23, hlam, hphi, ht34, ht45, p1020_1, u5elo4]
                            · have p1020_0 := h1020c.1
                              have p1020_1 := h1020c.2.1
                              have p1020_2 := h1020c.2.2.1
                              have p1020_3 := h1020c.2.2.2
                              linarith only [h1019, hlam, p1020_0]
                            · have p1020_0 := h1020c.1
                              have p1020_1 := h1020c.2.1
                              have p1020_2 := h1020c.2.2.1
                              have p1020_3 := h1020c.2.2.2
                              linarith only [hlam, p1020_0]
                          · linarith only [h1019, h710, h713, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h712, h977, hc12, hlam, hphi, u2elo0]
              · linarith only [h711, h976, hc12, hlam, hphi, u2elo0]
      · linarith only [h710, h712, hc23, hlam, hphi, ht34, ht45, u5elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1050 | h1050
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1051 | h1051
        · linarith only [h1051, h710, h711, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1053 | h1053
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1054 | h1054
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1055 | h1055
              · linarith only [h1055, h710, h711, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1057 | h1057
                · linarith only [h0, h1055, h1057, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h1050, h1057, hc12, hlam, hphi, u2elo0]
            · linarith only [h1054, h710, h711, hc23, hlam, hphi, ht34, ht45, u5elo4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1061 | h1061
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1062 | h1062
              · linarith only [h1062, h710, h711, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1064 | h1064
                · linarith only [h0, h1062, h1064, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h1050, h1064, hc12, hlam, hphi, u2elo0]
            · linarith only [h1050, h1061, h711, hc25, hlam, hphi, u5elo4]
      · linarith only [h1050, h710, hc23, hlam, hphi, ht34, ht45, u5elo2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1069 | h1069
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1070 | h1070
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1071 | h1071
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1072 | h1072
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1073 | h1073
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1074 | h1074
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1075 | h1075
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1076 | h1076
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1077 | h1077
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1078 | h1078
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1079 | h1079
                        · linarith only [h1069, h1079, h710, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                        · linarith only [h1069, h1073, h1079, h710, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                      · linarith only [h1078, h710, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h1071, h1077, h710, hlam]
                  · linarith only [h1069, h1073, h1076, h710, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h1074, h1075, hc24, hlam, hphi, ht45, u5elo2]
              · linarith only [h1069, h1074, h710, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1087 | h1087
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1088 | h1088
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1089 | h1089
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1090 | h1090
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1091 | h1091
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1092 | h1092
                        · linarith only [h1069, h1073, h1092, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1094 | h1094
                          · linarith only [h1069, h1073, h1090, h1094, hlam]
                          · rcases h5bigk with h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c
                            · have p1096_0 := h1096c.1
                              have p1096_1 := h1096c.2.1
                              have p1096_2 := h1096c.2.2.1
                              have p1096_3 := h1096c.2.2.2
                              linarith only [hlam, p1096_0]
                            · have p1096_0 := h1096c.1
                              have p1096_1 := h1096c.2.1
                              have p1096_2 := h1096c.2.2.1
                              have p1096_3 := h1096c.2.2.2
                              linarith only [h0, hlam, p1096_1]
                            · have p1096_0 := h1096c.1
                              have p1096_1 := h1096c.2.1
                              have p1096_2 := h1096c.2.2.1
                              have p1096_3 := h1096c.2.2.2
                              linarith only [hc25, hlam, hphi, p1096_1, u5elo0]
                            · have p1096_0 := h1096c.1
                              have p1096_1 := h1096c.2.1
                              have p1096_2 := h1096c.2.2.1
                              have p1096_3 := h1096c.2.2.2
                              linarith only [h1070, h710, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1096_1, u2elo2]
                            · have p1096_0 := h1096c.1
                              have p1096_1 := h1096c.2.1
                              have p1096_2 := h1096c.2.2.1
                              have p1096_3 := h1096c.2.2.2
                              linarith only [h1073, hlam, p1096_1]
                            · have p1096_0 := h1096c.1
                              have p1096_1 := h1096c.2.1
                              have p1096_2 := h1096c.2.2.1
                              have p1096_3 := h1096c.2.2.2
                              linarith only [hc05, hlam, hphi, p1096_1, u5elo1]
                            · have p1096_0 := h1096c.1
                              have p1096_1 := h1096c.2.1
                              have p1096_2 := h1096c.2.2.1
                              have p1096_3 := h1096c.2.2.2
                              linarith only [hlam, p1096_0]
                            · have p1096_0 := h1096c.1
                              have p1096_1 := h1096c.2.1
                              have p1096_2 := h1096c.2.2.1
                              have p1096_3 := h1096c.2.2.2
                              linarith only [h1091, hc35, hlam, hphi, p1096_1, u5elo1]
                            · have p1096_0 := h1096c.1
                              have p1096_1 := h1096c.2.1
                              have p1096_2 := h1096c.2.2.1
                              have p1096_3 := h1096c.2.2.2
                              linarith only [h1094, hc34, hlam, hphi, ht45, p1096_1, u5elo1]
                            · have p1096_0 := h1096c.1
                              have p1096_1 := h1096c.2.1
                              have p1096_2 := h1096c.2.2.1
                              have p1096_3 := h1096c.2.2.2
                              linarith only [h1069, h1073, h1090, hc34, hlam, hphi, ht45, p1096_1, u5elo1]
                            · have p1096_0 := h1096c.1
                              have p1096_1 := h1096c.2.1
                              have p1096_2 := h1096c.2.2.1
                              have p1096_3 := h1096c.2.2.2
                              linarith only [h1070, hlam, p1096_1]
                            · have p1096_0 := h1096c.1
                              have p1096_1 := h1096c.2.1
                              have p1096_2 := h1096c.2.2.1
                              have p1096_3 := h1096c.2.2.2
                              linarith only [h1088, hlam, p1096_1]
                            · have p1096_0 := h1096c.1
                              have p1096_1 := h1096c.2.1
                              have p1096_2 := h1096c.2.2.1
                              have p1096_3 := h1096c.2.2.2
                              linarith only [hlam, p1096_0]
                            · have p1096_0 := h1096c.1
                              have p1096_1 := h1096c.2.1
                              have p1096_2 := h1096c.2.2.1
                              have p1096_3 := h1096c.2.2.2
                              linarith only [h1094, hc34, hlam, hphi, ht45, p1096_1, u5elo2]
                            · have p1096_0 := h1096c.1
                              have p1096_1 := h1096c.2.1
                              have p1096_2 := h1096c.2.2.1
                              have p1096_3 := h1096c.2.2.2
                              linarith only [h1092, hlam, p1096_1]
                            · have p1096_0 := h1096c.1
                              have p1096_1 := h1096c.2.1
                              have p1096_2 := h1096c.2.2.1
                              have p1096_3 := h1096c.2.2.2
                              linarith only [h1072, hlam, p1096_0]
                            · have p1096_0 := h1096c.1
                              have p1096_1 := h1096c.2.1
                              have p1096_2 := h1096c.2.2.1
                              have p1096_3 := h1096c.2.2.2
                              linarith only [hc15, hlam, hphi, p1096_1, u5elo3]
                            · have p1096_0 := h1096c.1
                              have p1096_1 := h1096c.2.1
                              have p1096_2 := h1096c.2.2.1
                              have p1096_3 := h1096c.2.2.2
                              linarith only [h1091, hlam, p1096_0]
                            · have p1096_0 := h1096c.1
                              have p1096_1 := h1096c.2.1
                              have p1096_2 := h1096c.2.2.1
                              have p1096_3 := h1096c.2.2.2
                              linarith only [hlam, p1096_0]
                            · have p1096_0 := h1096c.1
                              have p1096_1 := h1096c.2.1
                              have p1096_2 := h1096c.2.2.1
                              have p1096_3 := h1096c.2.2.2
                              linarith only [h1094, hlam, p1096_1]
                            · have p1096_0 := h1096c.1
                              have p1096_1 := h1096c.2.1
                              have p1096_2 := h1096c.2.2.1
                              have p1096_3 := h1096c.2.2.2
                              linarith only [h0, h1087, h1089, hc01, hlam, hphi, ht12, p1096_1, u2elo1]
                            · have p1096_0 := h1096c.1
                              have p1096_1 := h1096c.2.1
                              have p1096_2 := h1096c.2.2.1
                              have p1096_3 := h1096c.2.2.2
                              linarith only [h1089, hlam, p1096_0]
                            · have p1096_0 := h1096c.1
                              have p1096_1 := h1096c.2.1
                              have p1096_2 := h1096c.2.2.1
                              have p1096_3 := h1096c.2.2.2
                              linarith only [h1087, h1089, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1096_1, u2elo1]
                            · have p1096_0 := h1096c.1
                              have p1096_1 := h1096c.2.1
                              have p1096_2 := h1096c.2.2.1
                              have p1096_3 := h1096c.2.2.2
                              linarith only [h1087, h1089, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1096_1, u2elo1]
                            · have p1096_0 := h1096c.1
                              have p1096_1 := h1096c.2.1
                              have p1096_2 := h1096c.2.2.1
                              have p1096_3 := h1096c.2.2.2
                              linarith only [hlam, p1096_0]
                      · linarith only [h1069, h1073, h1087, h1089, h1090, h1091, h710, hc02, hc34, hlam, hphi, ht45, u2elo1, u5elo3]
                    · linarith only [h1069, h1071, h1090, h710, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1124 | h1124
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1125 | h1125
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1126 | h1126
                        · linarith only [h0, h1069, h1089, h1126, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1128 | h1128
                          · linarith only [h0, h1070, h1089, h1124, h1126, h1128, h710, hc01, hlam, hphi, ht12, u2elo2]
                          · rcases h5bigk with h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c | h1130c
                            · have p1130_0 := h1130c.1
                              have p1130_1 := h1130c.2.1
                              have p1130_2 := h1130c.2.2.1
                              have p1130_3 := h1130c.2.2.2
                              linarith only [hlam, p1130_0]
                            · have p1130_0 := h1130c.1
                              have p1130_1 := h1130c.2.1
                              have p1130_2 := h1130c.2.2.1
                              have p1130_3 := h1130c.2.2.2
                              linarith only [h0, hlam, p1130_1]
                            · have p1130_0 := h1130c.1
                              have p1130_1 := h1130c.2.1
                              have p1130_2 := h1130c.2.2.1
                              have p1130_3 := h1130c.2.2.2
                              linarith only [h1124, h1126, hc34, hlam, hphi, ht45, p1130_1, u5elo0]
                            · have p1130_0 := h1130c.1
                              have p1130_1 := h1130c.2.1
                              have p1130_2 := h1130c.2.2.1
                              have p1130_3 := h1130c.2.2.2
                              linarith only [h1070, h1128, h710, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1130_1, u2elo2]
                            · have p1130_0 := h1130c.1
                              have p1130_1 := h1130c.2.1
                              have p1130_2 := h1130c.2.2.1
                              have p1130_3 := h1130c.2.2.2
                              linarith only [h1073, hlam, p1130_1]
                            · have p1130_0 := h1130c.1
                              have p1130_1 := h1130c.2.1
                              have p1130_2 := h1130c.2.2.1
                              have p1130_3 := h1130c.2.2.2
                              linarith only [hc05, hlam, hphi, p1130_1, u5elo1]
                            · have p1130_0 := h1130c.1
                              have p1130_1 := h1130c.2.1
                              have p1130_2 := h1130c.2.2.1
                              have p1130_3 := h1130c.2.2.2
                              linarith only [hlam, p1130_0]
                            · have p1130_0 := h1130c.1
                              have p1130_1 := h1130c.2.1
                              have p1130_2 := h1130c.2.2.1
                              have p1130_3 := h1130c.2.2.2
                              linarith only [h1089, h1126, hc24, hlam, hphi, ht45, p1130_1, u5elo4]
                            · have p1130_0 := h1130c.1
                              have p1130_1 := h1130c.2.1
                              have p1130_2 := h1130c.2.2.1
                              have p1130_3 := h1130c.2.2.2
                              linarith only [h1089, h1128, hc34, hlam, hphi, ht45, p1130_1, u5elo4]
                            · have p1130_0 := h1130c.1
                              have p1130_1 := h1130c.2.1
                              have p1130_2 := h1130c.2.2.1
                              have p1130_3 := h1130c.2.2.2
                              linarith only [h1089, hlam, p1130_1]
                            · have p1130_0 := h1130c.1
                              have p1130_1 := h1130c.2.1
                              have p1130_2 := h1130c.2.2.1
                              have p1130_3 := h1130c.2.2.2
                              linarith only [h1070, hlam, p1130_1]
                            · have p1130_0 := h1130c.1
                              have p1130_1 := h1130c.2.1
                              have p1130_2 := h1130c.2.2.1
                              have p1130_3 := h1130c.2.2.2
                              linarith only [h1088, hlam, p1130_1]
                            · have p1130_0 := h1130c.1
                              have p1130_1 := h1130c.2.1
                              have p1130_2 := h1130c.2.2.1
                              have p1130_3 := h1130c.2.2.2
                              linarith only [hlam, p1130_0]
                            · have p1130_0 := h1130c.1
                              have p1130_1 := h1130c.2.1
                              have p1130_2 := h1130c.2.2.1
                              have p1130_3 := h1130c.2.2.2
                              linarith only [h1128, hc34, hlam, hphi, ht45, p1130_1, u5elo2]
                            · have p1130_0 := h1130c.1
                              have p1130_1 := h1130c.2.1
                              have p1130_2 := h1130c.2.2.1
                              have p1130_3 := h1130c.2.2.2
                              linarith only [h1126, hlam, p1130_1]
                            · have p1130_0 := h1130c.1
                              have p1130_1 := h1130c.2.1
                              have p1130_2 := h1130c.2.2.1
                              have p1130_3 := h1130c.2.2.2
                              linarith only [h1072, hlam, p1130_0]
                            · have p1130_0 := h1130c.1
                              have p1130_1 := h1130c.2.1
                              have p1130_2 := h1130c.2.2.1
                              have p1130_3 := h1130c.2.2.2
                              linarith only [hc15, hlam, hphi, p1130_1, u5elo3]
                            · have p1130_0 := h1130c.1
                              have p1130_1 := h1130c.2.1
                              have p1130_2 := h1130c.2.2.1
                              have p1130_3 := h1130c.2.2.2
                              linarith only [h1125, hlam, p1130_0]
                            · have p1130_0 := h1130c.1
                              have p1130_1 := h1130c.2.1
                              have p1130_2 := h1130c.2.2.1
                              have p1130_3 := h1130c.2.2.2
                              linarith only [hlam, p1130_0]
                            · have p1130_0 := h1130c.1
                              have p1130_1 := h1130c.2.1
                              have p1130_2 := h1130c.2.2.1
                              have p1130_3 := h1130c.2.2.2
                              linarith only [h1128, hlam, p1130_1]
                            · have p1130_0 := h1130c.1
                              have p1130_1 := h1130c.2.1
                              have p1130_2 := h1130c.2.2.1
                              have p1130_3 := h1130c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1130_1, u5elo4]
                            · have p1130_0 := h1130c.1
                              have p1130_1 := h1130c.2.1
                              have p1130_2 := h1130c.2.2.1
                              have p1130_3 := h1130c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1130_1, u5elo4]
                            · have p1130_0 := h1130c.1
                              have p1130_1 := h1130c.2.1
                              have p1130_2 := h1130c.2.2.1
                              have p1130_3 := h1130c.2.2.2
                              linarith only [hc25, hlam, hphi, p1130_1, u5elo4]
                            · have p1130_0 := h1130c.1
                              have p1130_1 := h1130c.2.1
                              have p1130_2 := h1130c.2.2.1
                              have p1130_3 := h1130c.2.2.2
                              linarith only [hc35, hlam, hphi, p1130_1, u5elo4]
                            · have p1130_0 := h1130c.1
                              have p1130_1 := h1130c.2.1
                              have p1130_2 := h1130c.2.2.1
                              have p1130_3 := h1130c.2.2.2
                              linarith only [hlam, p1130_0]
                      · linarith only [h1125, h710, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h1071, h1124, h710, hlam]
                · linarith only [h1070, h1088, h710, hc12, hlam, hphi, u2elo2]
              · linarith only [h1069, h1087, h710, hc12, hlam, hphi, u2elo2]
          · linarith only [h1069, h1072, h710, hc24, hlam, hphi, ht45, u5elo3]
        · linarith only [h1069, h1071, h710, hlam]
      · linarith only [h1069, h1070, hc24, hlam, hphi, ht45, u5elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1163 | h1163
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1164 | h1164
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1165 | h1165
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1166 | h1166
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1167 | h1167
              · linarith only [h1069, h1167, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1169 | h1169
                · linarith only [h0, h1167, h1169, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h1163, h1169, hc12, hlam, hphi, u2elo0]
            · linarith only [h1069, h1163, h1166, hc25, hlam, hphi, u5elo4]
          · linarith only [h1069, h1163, h1164, h1165, hc25, hlam, hphi, u5elo3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1174 | h1174
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1175 | h1175
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1176 | h1176
              · linarith only [h1069, h1163, h1176, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1178 | h1178
                · linarith only [h0, h1176, h1178, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h1163, h1178, hc12, hlam, hphi, u2elo0]
            · linarith only [h1163, h1164, h1175, h710, hc25, hlam, hphi, u5elo4]
          · linarith only [h1163, h1174, h710, hc25, hlam, hphi, u5elo3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1183 | h1183
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1184 | h1184
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1185 | h1185
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1186 | h1186
              · linarith only [h1069, h1186, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1188 | h1188
                · linarith only [h1163, h1186, h1188, hc02, hlam, hphi, u2elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1190 | h1190
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1191 | h1191
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1192 | h1192
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1193 | h1193
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1194 | h1194
                          · rcases h5bigk with h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h0, hlam, p1195_1]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h1163, hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h1194, hc45, hlam, hphi, p1195_1, u5elo0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [hc45, hlam, hphi, p1195_1, u5elo0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [hc05, hlam, hphi, p1195_1, u5elo1]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h1188, hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h1188, h1194, hc45, hlam, hphi, p1195_1, u5elo2]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h1188, hc45, hlam, hphi, p1195_1, u5elo2]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1195_1, u5elo2]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [hc15, hlam, hphi, p1195_1, u5elo2]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h1194, hc45, hlam, hphi, p1195_1, u5elo2]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [hc45, hlam, hphi, p1195_1, u5elo2]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h1184, hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1195_1]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h1192, hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h1184, hc45, hlam, hphi, p1195_1, u5elo0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h1185, hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h1190, hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h1193, hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [h1194, hlam, p1195_0]
                            · have p1195_0 := h1195c.1
                              have p1195_1 := h1195c.2.1
                              have p1195_2 := h1195c.2.2.1
                              have p1195_3 := h1195c.2.2.2
                              linarith only [hlam, p1195_0]
                          · rcases h5bigk with h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c
                            · have p1221_0 := h1221c.1
                              have p1221_1 := h1221c.2.1
                              have p1221_2 := h1221c.2.2.1
                              have p1221_3 := h1221c.2.2.2
                              linarith only [hlam, p1221_0]
                            · have p1221_0 := h1221c.1
                              have p1221_1 := h1221c.2.1
                              have p1221_2 := h1221c.2.2.1
                              have p1221_3 := h1221c.2.2.2
                              linarith only [h0, hlam, p1221_1]
                            · have p1221_0 := h1221c.1
                              have p1221_1 := h1221c.2.1
                              have p1221_2 := h1221c.2.2.1
                              have p1221_3 := h1221c.2.2.2
                              linarith only [h1163, hlam, p1221_0]
                            · have p1221_0 := h1221c.1
                              have p1221_1 := h1221c.2.1
                              have p1221_2 := h1221c.2.2.1
                              have p1221_3 := h1221c.2.2.2
                              linarith only [h0, h1188, hc35, hlam, hphi, p1221_1, u5elo2]
                            · have p1221_0 := h1221c.1
                              have p1221_1 := h1221c.2.1
                              have p1221_2 := h1221c.2.2.1
                              have p1221_3 := h1221c.2.2.2
                              linarith only [h0, h1188, h1194, hc34, hlam, hphi, ht45, p1221_1, u5elo2]
                            · have p1221_0 := h1221c.1
                              have p1221_1 := h1221c.2.1
                              have p1221_2 := h1221c.2.2.1
                              have p1221_3 := h1221c.2.2.2
                              linarith only [h1188, hc05, hlam, hphi, p1221_1, u5elo2]
                            · have p1221_0 := h1221c.1
                              have p1221_1 := h1221c.2.1
                              have p1221_2 := h1221c.2.2.1
                              have p1221_3 := h1221c.2.2.2
                              linarith only [hlam, p1221_0]
                            · have p1221_0 := h1221c.1
                              have p1221_1 := h1221c.2.1
                              have p1221_2 := h1221c.2.2.1
                              have p1221_3 := h1221c.2.2.2
                              linarith only [h1188, hlam, p1221_0]
                            · have p1221_0 := h1221c.1
                              have p1221_1 := h1221c.2.1
                              have p1221_2 := h1221c.2.2.1
                              have p1221_3 := h1221c.2.2.2
                              linarith only [h1188, h1194, hc34, hlam, hphi, ht45, p1221_1, u5elo2]
                            · have p1221_0 := h1221c.1
                              have p1221_1 := h1221c.2.1
                              have p1221_2 := h1221c.2.2.1
                              have p1221_3 := h1221c.2.2.2
                              linarith only [h1188, h1194, hc34, hlam, hphi, ht45, p1221_1, u5elo2]
                            · have p1221_0 := h1221c.1
                              have p1221_1 := h1221c.2.1
                              have p1221_2 := h1221c.2.2.1
                              have p1221_3 := h1221c.2.2.2
                              linarith only [h1185, h1194, hc34, hlam, hphi, ht45, p1221_1, u5elo2]
                            · have p1221_0 := h1221c.1
                              have p1221_1 := h1221c.2.1
                              have p1221_2 := h1221c.2.2.1
                              have p1221_3 := h1221c.2.2.2
                              linarith only [hc15, hlam, hphi, p1221_1, u5elo2]
                            · have p1221_0 := h1221c.1
                              have p1221_1 := h1221c.2.1
                              have p1221_2 := h1221c.2.2.1
                              have p1221_3 := h1221c.2.2.2
                              linarith only [hlam, p1221_0]
                            · have p1221_0 := h1221c.1
                              have p1221_1 := h1221c.2.1
                              have p1221_2 := h1221c.2.2.1
                              have p1221_3 := h1221c.2.2.2
                              linarith only [h1194, hc34, hlam, hphi, ht45, p1221_1, u5elo2]
                            · have p1221_0 := h1221c.1
                              have p1221_1 := h1221c.2.1
                              have p1221_2 := h1221c.2.2.1
                              have p1221_3 := h1221c.2.2.2
                              linarith only [h1194, hc34, hlam, hphi, ht45, p1221_1, u5elo2]
                            · have p1221_0 := h1221c.1
                              have p1221_1 := h1221c.2.1
                              have p1221_2 := h1221c.2.2.1
                              have p1221_3 := h1221c.2.2.2
                              linarith only [h1184, hlam, p1221_0]
                            · have p1221_0 := h1221c.1
                              have p1221_1 := h1221c.2.1
                              have p1221_2 := h1221c.2.2.1
                              have p1221_3 := h1221c.2.2.2
                              linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p1221_1]
                            · have p1221_0 := h1221c.1
                              have p1221_1 := h1221c.2.1
                              have p1221_2 := h1221c.2.2.1
                              have p1221_3 := h1221c.2.2.2
                              linarith only [h1192, hlam, p1221_0]
                            · have p1221_0 := h1221c.1
                              have p1221_1 := h1221c.2.1
                              have p1221_2 := h1221c.2.2.1
                              have p1221_3 := h1221c.2.2.2
                              linarith only [hlam, p1221_0]
                            · have p1221_0 := h1221c.1
                              have p1221_1 := h1221c.2.1
                              have p1221_2 := h1221c.2.2.1
                              have p1221_3 := h1221c.2.2.2
                              linarith only [h1194, hlam, p1221_1]
                            · have p1221_0 := h1221c.1
                              have p1221_1 := h1221c.2.1
                              have p1221_2 := h1221c.2.2.1
                              have p1221_3 := h1221c.2.2.2
                              linarith only [h1185, hlam, p1221_0]
                            · have p1221_0 := h1221c.1
                              have p1221_1 := h1221c.2.1
                              have p1221_2 := h1221c.2.2.1
                              have p1221_3 := h1221c.2.2.2
                              linarith only [h1190, hlam, p1221_0]
                            · have p1221_0 := h1221c.1
                              have p1221_1 := h1221c.2.1
                              have p1221_2 := h1221c.2.2.1
                              have p1221_3 := h1221c.2.2.2
                              linarith only [h1193, hlam, p1221_0]
                            · have p1221_0 := h1221c.1
                              have p1221_1 := h1221c.2.1
                              have p1221_2 := h1221c.2.2.1
                              have p1221_3 := h1221c.2.2.2
                              linarith only [h1069, h1185, h1191, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1221_1, u2elo2]
                            · have p1221_0 := h1221c.1
                              have p1221_1 := h1221c.2.1
                              have p1221_2 := h1221c.2.2.1
                              have p1221_3 := h1221c.2.2.2
                              linarith only [hlam, p1221_0]
                        · linarith only [h1069, h1185, h1193, hlam]
                      · linarith only [h1069, h1185, h1191, h1192, hc45, hlam, hphi, u5elo3]
                    · linarith only [h1183, h1191, h710, hlam]
                  · linarith only [h1183, h1185, h1186, h1190, h710, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1251 | h1251
              · linarith only [h1069, h1251, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1253 | h1253
                · linarith only [h1163, h1253, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1255 | h1255
                  · linarith only [h1069, h1185, h1251, h1255, hc02, hlam, hphi, u2elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1257 | h1257
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1258 | h1258
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1259 | h1259
                        · linarith only [h0, h1255, h1257, h1259, hc01, hlam, hphi, ht12, u2elo2]
                        · linarith only [h1069, h1259, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                      · linarith only [h0, h1184, h1253, h1258, h710, hc02, hlam, hphi, u2elo4]
                    · linarith only [h1183, h1257, h710, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
          · linarith only [h1183, h1184, hc34, hlam, hphi, ht45, u5elo3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1265 | h1265
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1266 | h1266
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1267 | h1267
              · linarith only [h1069, h1267, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1269 | h1269
                · linarith only [h1163, h1267, h1269, hc02, hlam, hphi, u2elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1271 | h1271
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1272 | h1272
                    · linarith only [h1183, h1265, h1272, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1274 | h1274
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1275 | h1275
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1276 | h1276
                          · rcases h5bigk with h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c
                            · have p1277_0 := h1277c.1
                              have p1277_1 := h1277c.2.1
                              have p1277_2 := h1277c.2.2.1
                              have p1277_3 := h1277c.2.2.2
                              linarith only [hlam, p1277_0]
                            · have p1277_0 := h1277c.1
                              have p1277_1 := h1277c.2.1
                              have p1277_2 := h1277c.2.2.1
                              have p1277_3 := h1277c.2.2.2
                              linarith only [h0, hlam, p1277_1]
                            · have p1277_0 := h1277c.1
                              have p1277_1 := h1277c.2.1
                              have p1277_2 := h1277c.2.2.1
                              have p1277_3 := h1277c.2.2.2
                              linarith only [h1163, hlam, p1277_0]
                            · have p1277_0 := h1277c.1
                              have p1277_1 := h1277c.2.1
                              have p1277_2 := h1277c.2.2.1
                              have p1277_3 := h1277c.2.2.2
                              linarith only [h1276, hc45, hlam, hphi, p1277_1, u5elo0]
                            · have p1277_0 := h1277c.1
                              have p1277_1 := h1277c.2.1
                              have p1277_2 := h1277c.2.2.1
                              have p1277_3 := h1277c.2.2.2
                              linarith only [h0, hc45, hlam, hphi, p1277_1, u5elo1]
                            · have p1277_0 := h1277c.1
                              have p1277_1 := h1277c.2.1
                              have p1277_2 := h1277c.2.2.1
                              have p1277_3 := h1277c.2.2.2
                              linarith only [hc05, hlam, hphi, p1277_1, u5elo1]
                            · have p1277_0 := h1277c.1
                              have p1277_1 := h1277c.2.1
                              have p1277_2 := h1277c.2.2.1
                              have p1277_3 := h1277c.2.2.2
                              linarith only [hlam, p1277_0]
                            · have p1277_0 := h1277c.1
                              have p1277_1 := h1277c.2.1
                              have p1277_2 := h1277c.2.2.1
                              have p1277_3 := h1277c.2.2.2
                              linarith only [h1269, hlam, p1277_0]
                            · have p1277_0 := h1277c.1
                              have p1277_1 := h1277c.2.1
                              have p1277_2 := h1277c.2.2.1
                              have p1277_3 := h1277c.2.2.2
                              linarith only [h1269, h1276, hc45, hlam, hphi, p1277_1, u5elo2]
                            · have p1277_0 := h1277c.1
                              have p1277_1 := h1277c.2.1
                              have p1277_2 := h1277c.2.2.1
                              have p1277_3 := h1277c.2.2.2
                              linarith only [h1269, hc45, hlam, hphi, p1277_1, u5elo2]
                            · have p1277_0 := h1277c.1
                              have p1277_1 := h1277c.2.1
                              have p1277_2 := h1277c.2.2.1
                              have p1277_3 := h1277c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p1277_1, u5elo2]
                            · have p1277_0 := h1277c.1
                              have p1277_1 := h1277c.2.1
                              have p1277_2 := h1277c.2.2.1
                              have p1277_3 := h1277c.2.2.2
                              linarith only [hc15, hlam, hphi, p1277_1, u5elo2]
                            · have p1277_0 := h1277c.1
                              have p1277_1 := h1277c.2.1
                              have p1277_2 := h1277c.2.2.1
                              have p1277_3 := h1277c.2.2.2
                              linarith only [hlam, p1277_0]
                            · have p1277_0 := h1277c.1
                              have p1277_1 := h1277c.2.1
                              have p1277_2 := h1277c.2.2.1
                              have p1277_3 := h1277c.2.2.2
                              linarith only [h1276, hc45, hlam, hphi, p1277_1, u5elo2]
                            · have p1277_0 := h1277c.1
                              have p1277_1 := h1277c.2.1
                              have p1277_2 := h1277c.2.2.1
                              have p1277_3 := h1277c.2.2.2
                              linarith only [hc45, hlam, hphi, p1277_1, u5elo2]
                            · have p1277_0 := h1277c.1
                              have p1277_1 := h1277c.2.1
                              have p1277_2 := h1277c.2.2.1
                              have p1277_3 := h1277c.2.2.2
                              linarith only [h1265, hlam, p1277_0]
                            · have p1277_0 := h1277c.1
                              have p1277_1 := h1277c.2.1
                              have p1277_2 := h1277c.2.2.1
                              have p1277_3 := h1277c.2.2.2
                              linarith only [h0, h1265, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1277_1, u0elo2]
                            · have p1277_0 := h1277c.1
                              have p1277_1 := h1277c.2.1
                              have p1277_2 := h1277c.2.2.1
                              have p1277_3 := h1277c.2.2.2
                              linarith only [h1274, hlam, p1277_0]
                            · have p1277_0 := h1277c.1
                              have p1277_1 := h1277c.2.1
                              have p1277_2 := h1277c.2.2.1
                              have p1277_3 := h1277c.2.2.2
                              linarith only [hlam, p1277_0]
                            · have p1277_0 := h1277c.1
                              have p1277_1 := h1277c.2.1
                              have p1277_2 := h1277c.2.2.1
                              have p1277_3 := h1277c.2.2.2
                              linarith only [h1265, hc45, hlam, hphi, p1277_1, u5elo0]
                            · have p1277_0 := h1277c.1
                              have p1277_1 := h1277c.2.1
                              have p1277_2 := h1277c.2.2.1
                              have p1277_3 := h1277c.2.2.2
                              linarith only [h1266, hlam, p1277_0]
                            · have p1277_0 := h1277c.1
                              have p1277_1 := h1277c.2.1
                              have p1277_2 := h1277c.2.2.1
                              have p1277_3 := h1277c.2.2.2
                              linarith only [h1271, hlam, p1277_0]
                            · have p1277_0 := h1277c.1
                              have p1277_1 := h1277c.2.1
                              have p1277_2 := h1277c.2.2.1
                              have p1277_3 := h1277c.2.2.2
                              linarith only [h1275, hlam, p1277_0]
                            · have p1277_0 := h1277c.1
                              have p1277_1 := h1277c.2.1
                              have p1277_2 := h1277c.2.2.1
                              have p1277_3 := h1277c.2.2.2
                              linarith only [h1276, hlam, p1277_0]
                            · have p1277_0 := h1277c.1
                              have p1277_1 := h1277c.2.1
                              have p1277_2 := h1277c.2.2.1
                              have p1277_3 := h1277c.2.2.2
                              linarith only [hlam, p1277_0]
                          · linarith only [h1265, h1272, h1276, h710, hc35, hlam, hphi, u5elo4]
                        · linarith only [h1069, h1266, h1275, hlam]
                      · linarith only [h1274, h710, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · linarith only [h1069, h1266, h1267, h1271, hc12, hlam, hphi, u2elo3]
            · linarith only [h1183, h1265, h1266, hc35, hlam, hphi, u5elo4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1308 | h1308
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1309 | h1309
              · linarith only [h1069, h1309, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1311 | h1311
                · linarith only [h1163, h1309, h1311, hc02, hlam, hphi, u2elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1313 | h1313
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1314 | h1314
                    · linarith only [h1183, h1314, h710, hc02, hlam, hphi, u2elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1316 | h1316
                      · linarith only [h1265, h1314, h1316, h710, hc02, hc34, hlam, hphi, ht23]
                      · linarith only [h1316, h710, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · linarith only [h1069, h1308, h1309, h1313, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1320 | h1320
              · linarith only [h1069, h1320, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1322 | h1322
                · linarith only [h1163, h1320, h1322, hc02, hlam, hphi, u2elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1324 | h1324
                  · linarith only [h1069, h1308, h1320, h1324, hc02, hlam, hphi, u2elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1326 | h1326
                    · linarith only [h1183, h1326, h710, hc02, hlam, hphi, u2elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1328 | h1328
                      · linarith only [h1265, h1328, h710, hc02, hlam, hphi, u2elo2]
                      · linarith only [h1328, h710, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]

theorem r1l7_10_12_13_25_L_0_L_0_L_I_M_LI (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0elo := hb0.1
  have h2elo := hb2.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_13_25_L_0_L_0_L_I_M_LI_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_10_12_13_25_L_0_L_0_L_I_M_LI_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
