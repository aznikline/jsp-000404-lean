import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 13704000 in
set_option maxHeartbeats 13704000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s39_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h41027 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h45992 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h46639 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  have h39227 := hg39227
  rcases m.htr 0 3 4 (by decide) (by decide) with h46974 | h46974
  · rcases m.htr 0 3 5 (by decide) (by decide) with h46975 | h46975
    · rcases m.htr 0 4 5 (by decide) (by decide) with h46976 | h46976
      · rcases m.htr 1 2 3 (by decide) (by decide) with h46977 | h46977
        · rcases m.htr 1 2 4 (by decide) (by decide) with h46978 | h46978
          · rcases m.htr 1 2 5 (by decide) (by decide) with h46979 | h46979
            · rcases m.htr 1 3 4 (by decide) (by decide) with h46980 | h46980
              · rcases m.htr 1 3 5 (by decide) (by decide) with h46981 | h46981
                · rcases m.htr 1 4 5 (by decide) (by decide) with h46982 | h46982
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h46983 | h46983
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h46984 | h46984
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h46985 | h46985
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h46986 | h46986
                          · rcases h1bigk with h46987c | h46987c | h46987c | h46987c | h46987c | h46987c | h46987c | h46987c | h46987c | h46987c | h46987c | h46987c | h46987c | h46987c | h46987c | h46987c | h46987c | h46987c | h46987c | h46987c | h46987c | h46987c | h46987c | h46987c | h46987c
                            · have p46987_0 := h46987c.1
                              have p46987_1 := h46987c.2.1
                              have p46987_2 := h46987c.2.2.1
                              have p46987_3 := h46987c.2.2.2
                              linarith only [hlam, p46987_0]
                            · have p46987_0 := h46987c.1
                              have p46987_1 := h46987c.2.1
                              have p46987_2 := h46987c.2.2.1
                              have p46987_3 := h46987c.2.2.2
                              linarith only [h0, hlam, p46987_0]
                            · have p46987_0 := h46987c.1
                              have p46987_1 := h46987c.2.1
                              have p46987_2 := h46987c.2.2.1
                              have p46987_3 := h46987c.2.2.2
                              linarith only [h33187, hlam, p46987_0]
                            · have p46987_0 := h46987c.1
                              have p46987_1 := h46987c.2.1
                              have p46987_2 := h46987c.2.2.1
                              have p46987_3 := h46987c.2.2.2
                              linarith only [h36828, hlam, p46987_0]
                            · have p46987_0 := h46987c.1
                              have p46987_1 := h46987c.2.1
                              have p46987_2 := h46987c.2.2.1
                              have p46987_3 := h46987c.2.2.2
                              linarith only [h39227, hlam, p46987_0]
                            · have p46987_0 := h46987c.1
                              have p46987_1 := h46987c.2.1
                              have p46987_2 := h46987c.2.2.1
                              have p46987_3 := h46987c.2.2.2
                              rcases p46987_3 (m.d 0 1) (by simp) with h46993 | h46993
                              · linarith only [h46993, hlam, p46987_0]
                              · rcases p46987_3 (m.d 1 2) (by simp) with h46995 | h46995
                                · rcases p46987_3 (m.d 1 3) (by simp) with h46996 | h46996
                                  · linarith only [h46977, h46996, hlam]
                                  · linarith only [h33187, h46996, hlam]
                                · linarith only [h46995, hlam, p46987_0]
                            · have p46987_0 := h46987c.1
                              have p46987_1 := h46987c.2.1
                              have p46987_2 := h46987c.2.2.1
                              have p46987_3 := h46987c.2.2.2
                              linarith only [hlam, p46987_0]
                            · have p46987_0 := h46987c.1
                              have p46987_1 := h46987c.2.1
                              have p46987_2 := h46987c.2.2.1
                              have p46987_3 := h46987c.2.2.2
                              linarith only [h33187, hc01, hc12, hlam, hphi, p46987_1]
                            · have p46987_0 := h46987c.1
                              have p46987_1 := h46987c.2.1
                              have p46987_2 := h46987c.2.2.1
                              have p46987_3 := h46987c.2.2.2
                              linarith only [h36828, hc01, hc12, hlam, hphi, p46987_1]
                            · have p46987_0 := h46987c.1
                              have p46987_1 := h46987c.2.1
                              have p46987_2 := h46987c.2.2.1
                              have p46987_3 := h46987c.2.2.2
                              linarith only [h0, h46639, h46979, hc01, hc12, hlam, hphi, p46987_1]
                            · have p46987_0 := h46987c.1
                              have p46987_1 := h46987c.2.1
                              have p46987_2 := h46987c.2.2.1
                              have p46987_3 := h46987c.2.2.2
                              rcases p46987_3 (m.d 0 1) (by simp) with h47004 | h47004
                              · linarith only [h47004, hlam, p46987_0]
                              · rcases p46987_3 (m.d 1 2) (by simp) with h47006 | h47006
                                · rcases p46987_3 (m.d 1 3) (by simp) with h47007 | h47007
                                  · rcases p46987_3 (m.d 1 4) (by simp) with h47008 | h47008
                                    · linarith only [h46980, h47008, hlam]
                                    · linarith only [h36828, h47008, hlam]
                                  · linarith only [h47007, hlam, p46987_0]
                                · linarith only [h0, h47006, hlam]
                            · have p46987_0 := h46987c.1
                              have p46987_1 := h46987c.2.1
                              have p46987_2 := h46987c.2.2.1
                              have p46987_3 := h46987c.2.2.2
                              linarith only [h46977, hlam, p46987_0]
                            · have p46987_0 := h46987c.1
                              have p46987_1 := h46987c.2.1
                              have p46987_2 := h46987c.2.2.1
                              have p46987_3 := h46987c.2.2.2
                              linarith only [hlam, p46987_0]
                            · have p46987_0 := h46987c.1
                              have p46987_1 := h46987c.2.1
                              have p46987_2 := h46987c.2.2.1
                              have p46987_3 := h46987c.2.2.2
                              linarith only [h36828, hc01, hc13, hlam, hphi, p46987_1]
                            · have p46987_0 := h46987c.1
                              have p46987_1 := h46987c.2.1
                              have p46987_2 := h46987c.2.2.1
                              have p46987_3 := h46987c.2.2.2
                              linarith only [h0, h46639, h46977, h46979, hc01, hc12, hlam, hphi, p46987_1]
                            · have p46987_0 := h46987c.1
                              have p46987_1 := h46987c.2.1
                              have p46987_2 := h46987c.2.2.1
                              have p46987_3 := h46987c.2.2.2
                              rcases p46987_3 (m.d 0 1) (by simp) with h47017 | h47017
                              · linarith only [h47017, hlam, p46987_0]
                              · rcases p46987_3 (m.d 1 2) (by simp) with h47019 | h47019
                                · rcases p46987_3 (m.d 1 3) (by simp) with h47020 | h47020
                                  · rcases p46987_3 (m.d 1 4) (by simp) with h47021 | h47021
                                    · rcases p46987_3 (m.d 1 5) (by simp) with h47022 | h47022
                                      · linarith only [h46982, h47022, hlam]
                                      · linarith only [h39227, h47022, hlam]
                                    · linarith only [h47021, hlam, p46987_0]
                                  · linarith only [h33187, h47020, hlam]
                                · linarith only [h0, h47019, hlam]
                            · have p46987_0 := h46987c.1
                              have p46987_1 := h46987c.2.1
                              have p46987_2 := h46987c.2.2.1
                              have p46987_3 := h46987c.2.2.2
                              linarith only [h46978, hlam, p46987_0]
                            · have p46987_0 := h46987c.1
                              have p46987_1 := h46987c.2.1
                              have p46987_2 := h46987c.2.2.1
                              have p46987_3 := h46987c.2.2.2
                              linarith only [h46980, hlam, p46987_1]
                            · have p46987_0 := h46987c.1
                              have p46987_1 := h46987c.2.1
                              have p46987_2 := h46987c.2.2.1
                              have p46987_3 := h46987c.2.2.2
                              linarith only [hlam, p46987_0]
                            · have p46987_0 := h46987c.1
                              have p46987_1 := h46987c.2.1
                              have p46987_2 := h46987c.2.2.1
                              have p46987_3 := h46987c.2.2.2
                              linarith only [h0, h46639, h46979, hc01, hc14, hlam, hphi, p46987_1]
                            · have p46987_0 := h46987c.1
                              have p46987_1 := h46987c.2.1
                              have p46987_2 := h46987c.2.2.1
                              have p46987_3 := h46987c.2.2.2
                              rcases p46987_3 (m.d 0 1) (by simp) with h47032 | h47032
                              · linarith only [h47032, hlam, p46987_0]
                              · rcases p46987_3 (m.d 1 2) (by simp) with h47034 | h47034
                                · rcases p46987_3 (m.d 1 3) (by simp) with h47035 | h47035
                                  · rcases p46987_3 (m.d 1 4) (by simp) with h47036 | h47036
                                    · rcases p46987_3 (m.d 1 5) (by simp) with h47037 | h47037
                                      · rcases h1emax with h47038 | h47038 | h47038 | h47038 | h47038
                                        · rcases h2bigk with h47039c | h47039c | h47039c | h47039c | h47039c | h47039c | h47039c | h47039c | h47039c | h47039c | h47039c | h47039c | h47039c | h47039c | h47039c | h47039c | h47039c | h47039c | h47039c | h47039c | h47039c | h47039c | h47039c | h47039c | h47039c
                                          · have p47039_0 := h47039c.1
                                            have p47039_1 := h47039c.2.1
                                            have p47039_2 := h47039c.2.2.1
                                            have p47039_3 := h47039c.2.2.2
                                            linarith only [hlam, p47039_0]
                                          · have p47039_0 := h47039c.1
                                            have p47039_1 := h47039c.2.1
                                            have p47039_2 := h47039c.2.2.1
                                            have p47039_3 := h47039c.2.2.2
                                            linarith only [h0, hlam, p47039_0]
                                          · have p47039_0 := h47039c.1
                                            have p47039_1 := h47039c.2.1
                                            have p47039_2 := h47039c.2.2.1
                                            have p47039_3 := h47039c.2.2.2
                                            linarith only [h41027, hlam, p47039_0]
                                          · have p47039_0 := h47039c.1
                                            have p47039_1 := h47039c.2.1
                                            have p47039_2 := h47039c.2.2.1
                                            have p47039_3 := h47039c.2.2.2
                                            linarith only [h45992, hlam, p47039_0]
                                          · have p47039_0 := h47039c.1
                                            have p47039_1 := h47039c.2.1
                                            have p47039_2 := h47039c.2.2.1
                                            have p47039_3 := h47039c.2.2.2
                                            linarith only [h46639, hlam, p47039_0]
                                          · have p47039_0 := h47039c.1
                                            have p47039_1 := h47039c.2.1
                                            have p47039_2 := h47039c.2.2.1
                                            have p47039_3 := h47039c.2.2.2
                                            rcases p47039_3 (m.d 0 2) (by simp) with h47045 | h47045
                                            · linarith only [h0, h47045, hlam]
                                            · rcases p47039_3 (m.d 1 2) (by simp) with h47047 | h47047
                                              · rcases p47039_3 (m.d 2 3) (by simp) with h47048 | h47048
                                                · linarith only [h46977, h47048, hlam]
                                                · linarith only [h41027, h47048, hlam]
                                              · linarith only [h0, h47047, hlam]
                                          · have p47039_0 := h47039c.1
                                            have p47039_1 := h47039c.2.1
                                            have p47039_2 := h47039c.2.2.1
                                            have p47039_3 := h47039c.2.2.2
                                            linarith only [hlam, p47039_0]
                                          · have p47039_0 := h47039c.1
                                            have p47039_1 := h47039c.2.1
                                            have p47039_2 := h47039c.2.2.1
                                            have p47039_3 := h47039c.2.2.2
                                            linarith only [h0, h41027, hc01, hc12, hlam, hphi, p47039_1]
                                          · have p47039_0 := h47039c.1
                                            have p47039_1 := h47039c.2.1
                                            have p47039_2 := h47039c.2.2.1
                                            have p47039_3 := h47039c.2.2.2
                                            linarith only [h0, h46639, h46985, hc01, hc12, hlam, hphi, p47039_1]
                                          · have p47039_0 := h47039c.1
                                            have p47039_1 := h47039c.2.1
                                            have p47039_2 := h47039c.2.2.1
                                            have p47039_3 := h47039c.2.2.2
                                            linarith only [h0, h46639, hc01, hc12, hlam, hphi, p47039_1]
                                          · have p47039_0 := h47039c.1
                                            have p47039_1 := h47039c.2.1
                                            have p47039_2 := h47039c.2.2.1
                                            have p47039_3 := h47039c.2.2.2
                                            linarith only [h0, h46977, hc01, hc12, hlam, hphi, p47039_1]
                                          · have p47039_0 := h47039c.1
                                            have p47039_1 := h47039c.2.1
                                            have p47039_2 := h47039c.2.2.1
                                            have p47039_3 := h47039c.2.2.2
                                            linarith only [h46977, hlam, p47039_0]
                                          · have p47039_0 := h47039c.1
                                            have p47039_1 := h47039c.2.1
                                            have p47039_2 := h47039c.2.2.1
                                            have p47039_3 := h47039c.2.2.2
                                            linarith only [hlam, p47039_0]
                                          · have p47039_0 := h47039c.1
                                            have p47039_1 := h47039c.2.1
                                            have p47039_2 := h47039c.2.2.1
                                            have p47039_3 := h47039c.2.2.2
                                            linarith only [h0, h46639, h46977, h46985, hc01, hc12, hlam, hphi, p47039_1]
                                          · have p47039_0 := h47039c.1
                                            have p47039_1 := h47039c.2.1
                                            have p47039_2 := h47039c.2.2.1
                                            have p47039_3 := h47039c.2.2.2
                                            linarith only [h0, h46639, h46977, hc01, hc12, hlam, hphi, p47039_1]
                                          · have p47039_0 := h47039c.1
                                            have p47039_1 := h47039c.2.1
                                            have p47039_2 := h47039c.2.2.1
                                            have p47039_3 := h47039c.2.2.2
                                            linarith only [h0, h46978, hc01, hc12, hlam, hphi, p47039_1]
                                          · have p47039_0 := h47039c.1
                                            have p47039_1 := h47039c.2.1
                                            have p47039_2 := h47039c.2.2.1
                                            have p47039_3 := h47039c.2.2.2
                                            linarith only [h46978, hlam, p47039_0]
                                          · have p47039_0 := h47039c.1
                                            have p47039_1 := h47039c.2.1
                                            have p47039_2 := h47039c.2.2.1
                                            have p47039_3 := h47039c.2.2.2
                                            linarith only [h46983, hlam, p47039_0]
                                          · have p47039_0 := h47039c.1
                                            have p47039_1 := h47039c.2.1
                                            have p47039_2 := h47039c.2.2.1
                                            have p47039_3 := h47039c.2.2.2
                                            linarith only [hlam, p47039_0]
                                          · have p47039_0 := h47039c.1
                                            have p47039_1 := h47039c.2.1
                                            have p47039_2 := h47039c.2.2.1
                                            have p47039_3 := h47039c.2.2.2
                                            linarith only [h0, h46639, h46977, h46983, hc01, hc12, hlam, hphi, p47039_1]
                                          · have p47039_0 := h47039c.1
                                            have p47039_1 := h47039c.2.1
                                            have p47039_2 := h47039c.2.2.1
                                            have p47039_3 := h47039c.2.2.2
                                            linarith only [h0, h46979, hc01, hc12, hlam, hphi, p47039_1]
                                          · have p47039_0 := h47039c.1
                                            have p47039_1 := h47039c.2.1
                                            have p47039_2 := h47039c.2.2.1
                                            have p47039_3 := h47039c.2.2.2
                                            linarith only [h46979, hlam, p47039_0]
                                          · have p47039_0 := h47039c.1
                                            have p47039_1 := h47039c.2.1
                                            have p47039_2 := h47039c.2.2.1
                                            have p47039_3 := h47039c.2.2.2
                                            linarith only [h46984, hlam, p47039_0]
                                          · have p47039_0 := h47039c.1
                                            have p47039_1 := h47039c.2.1
                                            have p47039_2 := h47039c.2.2.1
                                            have p47039_3 := h47039c.2.2.2
                                            linarith only [h46985, hlam, p47039_1]
                                          · have p47039_0 := h47039c.1
                                            have p47039_1 := h47039c.2.1
                                            have p47039_2 := h47039c.2.2.1
                                            have p47039_3 := h47039c.2.2.2
                                            linarith only [hlam, p47039_0]
                                        · linarith only [h0, h47038, hc01, hlam]
                                        · linarith only [h46980, h46982, h47038, hc01, hlam, p46987_1]
                                        · linarith only [h46982, h47038, hc01, hlam, p46987_1]
                                        · linarith only [h47038, hc01, hlam, p46987_1]
                                      · linarith only [h47037, hlam, p46987_0]
                                    · linarith only [h36828, h47036, hlam]
                                  · linarith only [h33187, h47035, hlam]
                                · linarith only [h0, h47034, hlam]
                            · have p46987_0 := h46987c.1
                              have p46987_1 := h46987c.2.1
                              have p46987_2 := h46987c.2.2.1
                              have p46987_3 := h46987c.2.2.2
                              linarith only [h46979, hlam, p46987_0]
                            · have p46987_0 := h46987c.1
                              have p46987_1 := h46987c.2.1
                              have p46987_2 := h46987c.2.2.1
                              have p46987_3 := h46987c.2.2.2
                              linarith only [h46981, hlam, p46987_0]
                            · have p46987_0 := h46987c.1
                              have p46987_1 := h46987c.2.1
                              have p46987_2 := h46987c.2.2.1
                              have p46987_3 := h46987c.2.2.2
                              linarith only [h46982, hlam, p46987_0]
                            · have p46987_0 := h46987c.1
                              have p46987_1 := h46987c.2.1
                              have p46987_2 := h46987c.2.2.1
                              have p46987_3 := h46987c.2.2.2
                              linarith only [hlam, p46987_0]
                          · rcases h1bigk with h47083c | h47083c | h47083c | h47083c | h47083c | h47083c | h47083c | h47083c | h47083c | h47083c | h47083c | h47083c | h47083c | h47083c | h47083c | h47083c | h47083c | h47083c | h47083c | h47083c | h47083c | h47083c | h47083c | h47083c | h47083c
                            · have p47083_0 := h47083c.1
                              have p47083_1 := h47083c.2.1
                              have p47083_2 := h47083c.2.2.1
                              have p47083_3 := h47083c.2.2.2
                              linarith only [hlam, p47083_0]
                            · have p47083_0 := h47083c.1
                              have p47083_1 := h47083c.2.1
                              have p47083_2 := h47083c.2.2.1
                              have p47083_3 := h47083c.2.2.2
                              linarith only [h0, hlam, p47083_0]
                            · have p47083_0 := h47083c.1
                              have p47083_1 := h47083c.2.1
                              have p47083_2 := h47083c.2.2.1
                              have p47083_3 := h47083c.2.2.2
                              linarith only [h33187, hlam, p47083_0]
                            · have p47083_0 := h47083c.1
                              have p47083_1 := h47083c.2.1
                              have p47083_2 := h47083c.2.2.1
                              have p47083_3 := h47083c.2.2.2
                              linarith only [h36828, hlam, p47083_0]
                            · have p47083_0 := h47083c.1
                              have p47083_1 := h47083c.2.1
                              have p47083_2 := h47083c.2.2.1
                              have p47083_3 := h47083c.2.2.2
                              linarith only [h39227, hlam, p47083_0]
                            · have p47083_0 := h47083c.1
                              have p47083_1 := h47083c.2.1
                              have p47083_2 := h47083c.2.2.1
                              have p47083_3 := h47083c.2.2.2
                              rcases p47083_3 (m.d 0 1) (by simp) with h47089 | h47089
                              · linarith only [h47089, hlam, p47083_0]
                              · rcases p47083_3 (m.d 1 2) (by simp) with h47091 | h47091
                                · rcases p47083_3 (m.d 1 3) (by simp) with h47092 | h47092
                                  · linarith only [h46977, h47092, hlam]
                                  · linarith only [h33187, h47092, hlam]
                                · linarith only [h47091, hlam, p47083_0]
                            · have p47083_0 := h47083c.1
                              have p47083_1 := h47083c.2.1
                              have p47083_2 := h47083c.2.2.1
                              have p47083_3 := h47083c.2.2.2
                              linarith only [hlam, p47083_0]
                            · have p47083_0 := h47083c.1
                              have p47083_1 := h47083c.2.1
                              have p47083_2 := h47083c.2.2.1
                              have p47083_3 := h47083c.2.2.2
                              linarith only [h33187, hc01, hc12, hlam, hphi, p47083_1]
                            · have p47083_0 := h47083c.1
                              have p47083_1 := h47083c.2.1
                              have p47083_2 := h47083c.2.2.1
                              have p47083_3 := h47083c.2.2.2
                              linarith only [h36828, h46976, h46986, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p47083_1]
                            · have p47083_0 := h47083c.1
                              have p47083_1 := h47083c.2.1
                              have p47083_2 := h47083c.2.2.1
                              have p47083_3 := h47083c.2.2.2
                              linarith only [h39227, hc01, hc12, hlam, hphi, p47083_1]
                            · have p47083_0 := h47083c.1
                              have p47083_1 := h47083c.2.1
                              have p47083_2 := h47083c.2.2.1
                              have p47083_3 := h47083c.2.2.2
                              rcases p47083_3 (m.d 0 1) (by simp) with h47100 | h47100
                              · linarith only [h47100, hlam, p47083_0]
                              · rcases p47083_3 (m.d 1 2) (by simp) with h47102 | h47102
                                · rcases p47083_3 (m.d 1 3) (by simp) with h47103 | h47103
                                  · rcases p47083_3 (m.d 1 4) (by simp) with h47104 | h47104
                                    · linarith only [h46980, h47104, hlam]
                                    · linarith only [h36828, h47104, hlam]
                                  · linarith only [h47103, hlam, p47083_0]
                                · linarith only [h0, h47102, hlam]
                            · have p47083_0 := h47083c.1
                              have p47083_1 := h47083c.2.1
                              have p47083_2 := h47083c.2.2.1
                              have p47083_3 := h47083c.2.2.2
                              linarith only [h46977, hlam, p47083_0]
                            · have p47083_0 := h47083c.1
                              have p47083_1 := h47083c.2.1
                              have p47083_2 := h47083c.2.2.1
                              have p47083_3 := h47083c.2.2.2
                              linarith only [hlam, p47083_0]
                            · have p47083_0 := h47083c.1
                              have p47083_1 := h47083c.2.1
                              have p47083_2 := h47083c.2.2.1
                              have p47083_3 := h47083c.2.2.2
                              linarith only [h45992, h46976, h46978, h46986, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p47083_1]
                            · have p47083_0 := h47083c.1
                              have p47083_1 := h47083c.2.1
                              have p47083_2 := h47083c.2.2.1
                              have p47083_3 := h47083c.2.2.2
                              linarith only [h0, h46639, h46977, h46979, hc01, hc12, hlam, hphi, p47083_1]
                            · have p47083_0 := h47083c.1
                              have p47083_1 := h47083c.2.1
                              have p47083_2 := h47083c.2.2.1
                              have p47083_3 := h47083c.2.2.2
                              rcases p47083_3 (m.d 0 1) (by simp) with h47113 | h47113
                              · linarith only [h47113, hlam, p47083_0]
                              · rcases p47083_3 (m.d 1 2) (by simp) with h47115 | h47115
                                · rcases p47083_3 (m.d 1 3) (by simp) with h47116 | h47116
                                  · rcases p47083_3 (m.d 1 4) (by simp) with h47117 | h47117
                                    · rcases p47083_3 (m.d 1 5) (by simp) with h47118 | h47118
                                      · linarith only [h46982, h47118, hlam]
                                      · linarith only [h39227, h47118, hlam]
                                    · linarith only [h47117, hlam, p47083_0]
                                  · linarith only [h33187, h47116, hlam]
                                · linarith only [h0, h47115, hlam]
                            · have p47083_0 := h47083c.1
                              have p47083_1 := h47083c.2.1
                              have p47083_2 := h47083c.2.2.1
                              have p47083_3 := h47083c.2.2.2
                              linarith only [h46978, hlam, p47083_0]
                            · have p47083_0 := h47083c.1
                              have p47083_1 := h47083c.2.1
                              have p47083_2 := h47083c.2.2.1
                              have p47083_3 := h47083c.2.2.2
                              linarith only [h46980, hlam, p47083_1]
                            · have p47083_0 := h47083c.1
                              have p47083_1 := h47083c.2.1
                              have p47083_2 := h47083c.2.2.1
                              have p47083_3 := h47083c.2.2.2
                              linarith only [hlam, p47083_0]
                            · have p47083_0 := h47083c.1
                              have p47083_1 := h47083c.2.1
                              have p47083_2 := h47083c.2.2.1
                              have p47083_3 := h47083c.2.2.2
                              linarith only [h0, h46639, h46979, hc01, hc14, hlam, hphi, p47083_1]
                            · have p47083_0 := h47083c.1
                              have p47083_1 := h47083c.2.1
                              have p47083_2 := h47083c.2.2.1
                              have p47083_3 := h47083c.2.2.2
                              rcases p47083_3 (m.d 0 1) (by simp) with h47128 | h47128
                              · linarith only [h47128, hlam, p47083_0]
                              · rcases p47083_3 (m.d 1 2) (by simp) with h47130 | h47130
                                · rcases p47083_3 (m.d 1 3) (by simp) with h47131 | h47131
                                  · rcases p47083_3 (m.d 1 4) (by simp) with h47132 | h47132
                                    · rcases p47083_3 (m.d 1 5) (by simp) with h47133 | h47133
                                      · rcases h1emax with h47134 | h47134 | h47134 | h47134 | h47134
                                        · rcases h2bigk with h47135c | h47135c | h47135c | h47135c | h47135c | h47135c | h47135c | h47135c | h47135c | h47135c | h47135c | h47135c | h47135c | h47135c | h47135c | h47135c | h47135c | h47135c | h47135c | h47135c | h47135c | h47135c | h47135c | h47135c | h47135c
                                          · have p47135_0 := h47135c.1
                                            have p47135_1 := h47135c.2.1
                                            have p47135_2 := h47135c.2.2.1
                                            have p47135_3 := h47135c.2.2.2
                                            linarith only [hlam, p47135_0]
                                          · have p47135_0 := h47135c.1
                                            have p47135_1 := h47135c.2.1
                                            have p47135_2 := h47135c.2.2.1
                                            have p47135_3 := h47135c.2.2.2
                                            linarith only [h0, hlam, p47135_0]
                                          · have p47135_0 := h47135c.1
                                            have p47135_1 := h47135c.2.1
                                            have p47135_2 := h47135c.2.2.1
                                            have p47135_3 := h47135c.2.2.2
                                            linarith only [h41027, hlam, p47135_0]
                                          · have p47135_0 := h47135c.1
                                            have p47135_1 := h47135c.2.1
                                            have p47135_2 := h47135c.2.2.1
                                            have p47135_3 := h47135c.2.2.2
                                            linarith only [h45992, hlam, p47135_0]
                                          · have p47135_0 := h47135c.1
                                            have p47135_1 := h47135c.2.1
                                            have p47135_2 := h47135c.2.2.1
                                            have p47135_3 := h47135c.2.2.2
                                            linarith only [h46639, hlam, p47135_0]
                                          · have p47135_0 := h47135c.1
                                            have p47135_1 := h47135c.2.1
                                            have p47135_2 := h47135c.2.2.1
                                            have p47135_3 := h47135c.2.2.2
                                            rcases p47135_3 (m.d 0 2) (by simp) with h47141 | h47141
                                            · linarith only [h0, h47141, hlam]
                                            · rcases p47135_3 (m.d 1 2) (by simp) with h47143 | h47143
                                              · rcases p47135_3 (m.d 2 3) (by simp) with h47144 | h47144
                                                · linarith only [h46977, h47144, hlam]
                                                · linarith only [h41027, h47144, hlam]
                                              · linarith only [h0, h47143, hlam]
                                          · have p47135_0 := h47135c.1
                                            have p47135_1 := h47135c.2.1
                                            have p47135_2 := h47135c.2.2.1
                                            have p47135_3 := h47135c.2.2.2
                                            linarith only [hlam, p47135_0]
                                          · have p47135_0 := h47135c.1
                                            have p47135_1 := h47135c.2.1
                                            have p47135_2 := h47135c.2.2.1
                                            have p47135_3 := h47135c.2.2.2
                                            linarith only [h45992, h46976, h46983, h46986, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p47135_1]
                                          · have p47135_0 := h47135c.1
                                            have p47135_1 := h47135c.2.1
                                            have p47135_2 := h47135c.2.2.1
                                            have p47135_3 := h47135c.2.2.2
                                            linarith only [h45992, h46976, h46986, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p47135_1]
                                          · have p47135_0 := h47135c.1
                                            have p47135_1 := h47135c.2.1
                                            have p47135_2 := h47135c.2.2.1
                                            have p47135_3 := h47135c.2.2.2
                                            linarith only [h0, h46639, hc01, hc12, hlam, hphi, p47135_1]
                                          · have p47135_0 := h47135c.1
                                            have p47135_1 := h47135c.2.1
                                            have p47135_2 := h47135c.2.2.1
                                            have p47135_3 := h47135c.2.2.2
                                            linarith only [h0, h46977, hc01, hc12, hlam, hphi, p47135_1]
                                          · have p47135_0 := h47135c.1
                                            have p47135_1 := h47135c.2.1
                                            have p47135_2 := h47135c.2.2.1
                                            have p47135_3 := h47135c.2.2.2
                                            linarith only [h46977, hlam, p47135_0]
                                          · have p47135_0 := h47135c.1
                                            have p47135_1 := h47135c.2.1
                                            have p47135_2 := h47135c.2.2.1
                                            have p47135_3 := h47135c.2.2.2
                                            linarith only [hlam, p47135_0]
                                          · have p47135_0 := h47135c.1
                                            have p47135_1 := h47135c.2.1
                                            have p47135_2 := h47135c.2.2.1
                                            have p47135_3 := h47135c.2.2.2
                                            linarith only [h45992, h46976, h46977, h46986, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p47135_1]
                                          · have p47135_0 := h47135c.1
                                            have p47135_1 := h47135c.2.1
                                            have p47135_2 := h47135c.2.2.1
                                            have p47135_3 := h47135c.2.2.2
                                            linarith only [h0, h46639, h46977, hc01, hc12, hlam, hphi, p47135_1]
                                          · have p47135_0 := h47135c.1
                                            have p47135_1 := h47135c.2.1
                                            have p47135_2 := h47135c.2.2.1
                                            have p47135_3 := h47135c.2.2.2
                                            linarith only [h0, h46978, hc01, hc12, hlam, hphi, p47135_1]
                                          · have p47135_0 := h47135c.1
                                            have p47135_1 := h47135c.2.1
                                            have p47135_2 := h47135c.2.2.1
                                            have p47135_3 := h47135c.2.2.2
                                            linarith only [h46978, hlam, p47135_0]
                                          · have p47135_0 := h47135c.1
                                            have p47135_1 := h47135c.2.1
                                            have p47135_2 := h47135c.2.2.1
                                            have p47135_3 := h47135c.2.2.2
                                            linarith only [h46983, hlam, p47135_0]
                                          · have p47135_0 := h47135c.1
                                            have p47135_1 := h47135c.2.1
                                            have p47135_2 := h47135c.2.2.1
                                            have p47135_3 := h47135c.2.2.2
                                            linarith only [hlam, p47135_0]
                                          · have p47135_0 := h47135c.1
                                            have p47135_1 := h47135c.2.1
                                            have p47135_2 := h47135c.2.2.1
                                            have p47135_3 := h47135c.2.2.2
                                            linarith only [h0, h46639, h46977, h46983, hc01, hc12, hlam, hphi, p47135_1]
                                          · have p47135_0 := h47135c.1
                                            have p47135_1 := h47135c.2.1
                                            have p47135_2 := h47135c.2.2.1
                                            have p47135_3 := h47135c.2.2.2
                                            linarith only [h0, h46979, hc01, hc12, hlam, hphi, p47135_1]
                                          · have p47135_0 := h47135c.1
                                            have p47135_1 := h47135c.2.1
                                            have p47135_2 := h47135c.2.2.1
                                            have p47135_3 := h47135c.2.2.2
                                            linarith only [h46979, hlam, p47135_0]
                                          · have p47135_0 := h47135c.1
                                            have p47135_1 := h47135c.2.1
                                            have p47135_2 := h47135c.2.2.1
                                            have p47135_3 := h47135c.2.2.2
                                            linarith only [h46984, hlam, p47135_0]
                                          · have p47135_0 := h47135c.1
                                            have p47135_1 := h47135c.2.1
                                            have p47135_2 := h47135c.2.2.1
                                            have p47135_3 := h47135c.2.2.2
                                            linarith only [h46985, hlam, p47135_1]
                                          · have p47135_0 := h47135c.1
                                            have p47135_1 := h47135c.2.1
                                            have p47135_2 := h47135c.2.2.1
                                            have p47135_3 := h47135c.2.2.2
                                            linarith only [hlam, p47135_0]
                                        · linarith only [h0, h47134, hc01, hlam]
                                        · linarith only [h46980, h46982, h47134, hc01, hlam, p47083_1]
                                        · linarith only [h46982, h47134, hc01, hlam, p47083_1]
                                        · linarith only [h47134, hc01, hlam, p47083_1]
                                      · linarith only [h47133, hlam, p47083_0]
                                    · linarith only [h36828, h47132, hlam]
                                  · linarith only [h33187, h47131, hlam]
                                · linarith only [h0, h47130, hlam]
                            · have p47083_0 := h47083c.1
                              have p47083_1 := h47083c.2.1
                              have p47083_2 := h47083c.2.2.1
                              have p47083_3 := h47083c.2.2.2
                              linarith only [h46979, hlam, p47083_0]
                            · have p47083_0 := h47083c.1
                              have p47083_1 := h47083c.2.1
                              have p47083_2 := h47083c.2.2.1
                              have p47083_3 := h47083c.2.2.2
                              linarith only [h46981, hlam, p47083_0]
                            · have p47083_0 := h47083c.1
                              have p47083_1 := h47083c.2.1
                              have p47083_2 := h47083c.2.2.1
                              have p47083_3 := h47083c.2.2.2
                              linarith only [h46982, hlam, p47083_0]
                            · have p47083_0 := h47083c.1
                              have p47083_1 := h47083c.2.1
                              have p47083_2 := h47083c.2.2.1
                              have p47083_3 := h47083c.2.2.2
                              linarith only [hlam, p47083_0]
                        · linarith only [h0, h41027, h45992, h46974, h46976, h46977, h46985, hc01, hc12, hlam, hphi]
                      · linarith only [h41027, h46975, h46984, hlam]
                    · linarith only [h41027, h46974, h46983, hlam]
                  · linarith only [h45992, h46976, h46978, h46982, hlam]
                · linarith only [h41027, h46975, h46977, h46981, hlam]
              · linarith only [h41027, h46974, h46977, h46980, hlam]
            · linarith only [h0, h41027, h46977, h46979, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h41027, h46977, h46978, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h47187 | h47187
          · linarith only [h0, h45992, h46977, h47187, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h47189 | h47189
            · linarith only [h0, h46639, h46977, h47189, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h47191 | h47191
              · rcases m.htr 1 3 5 (by decide) (by decide) with h47192 | h47192
                · rcases m.htr 1 4 5 (by decide) (by decide) with h47193 | h47193
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h47194 | h47194
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h47195 | h47195
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h47196 | h47196
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h47197 | h47197
                          · rcases h1bigk with h47198c | h47198c | h47198c | h47198c | h47198c | h47198c | h47198c | h47198c | h47198c | h47198c | h47198c | h47198c | h47198c | h47198c | h47198c | h47198c | h47198c | h47198c | h47198c | h47198c | h47198c | h47198c | h47198c | h47198c | h47198c
                            · have p47198_0 := h47198c.1
                              have p47198_1 := h47198c.2.1
                              have p47198_2 := h47198c.2.2.1
                              have p47198_3 := h47198c.2.2.2
                              linarith only [hlam, p47198_0]
                            · have p47198_0 := h47198c.1
                              have p47198_1 := h47198c.2.1
                              have p47198_2 := h47198c.2.2.1
                              have p47198_3 := h47198c.2.2.2
                              linarith only [h0, hlam, p47198_0]
                            · have p47198_0 := h47198c.1
                              have p47198_1 := h47198c.2.1
                              have p47198_2 := h47198c.2.2.1
                              have p47198_3 := h47198c.2.2.2
                              linarith only [h33187, hlam, p47198_0]
                            · have p47198_0 := h47198c.1
                              have p47198_1 := h47198c.2.1
                              have p47198_2 := h47198c.2.2.1
                              have p47198_3 := h47198c.2.2.2
                              linarith only [h36828, hlam, p47198_0]
                            · have p47198_0 := h47198c.1
                              have p47198_1 := h47198c.2.1
                              have p47198_2 := h47198c.2.2.1
                              have p47198_3 := h47198c.2.2.2
                              linarith only [h39227, hlam, p47198_0]
                            · have p47198_0 := h47198c.1
                              have p47198_1 := h47198c.2.1
                              have p47198_2 := h47198c.2.2.1
                              have p47198_3 := h47198c.2.2.2
                              linarith only [h47189, h47194, h47196, hc01, hc23, hlam, hphi, ht12, p47198_1]
                            · have p47198_0 := h47198c.1
                              have p47198_1 := h47198c.2.1
                              have p47198_2 := h47198c.2.2.1
                              have p47198_3 := h47198c.2.2.2
                              linarith only [hlam, p47198_0]
                            · have p47198_0 := h47198c.1
                              have p47198_1 := h47198c.2.1
                              have p47198_2 := h47198c.2.2.1
                              have p47198_3 := h47198c.2.2.2
                              linarith only [h46977, hlam, p47198_1]
                            · have p47198_0 := h47198c.1
                              have p47198_1 := h47198c.2.1
                              have p47198_2 := h47198c.2.2.1
                              have p47198_3 := h47198c.2.2.2
                              linarith only [h47187, hlam, p47198_1]
                            · have p47198_0 := h47198c.1
                              have p47198_1 := h47198c.2.1
                              have p47198_2 := h47198c.2.2.1
                              have p47198_3 := h47198c.2.2.2
                              linarith only [h47189, hlam, p47198_1]
                            · have p47198_0 := h47198c.1
                              have p47198_1 := h47198c.2.1
                              have p47198_2 := h47198c.2.2.1
                              have p47198_3 := h47198c.2.2.2
                              rcases p47198_3 (m.d 0 1) (by simp) with h47209 | h47209
                              · linarith only [h47209, hlam, p47198_0]
                              · rcases p47198_3 (m.d 1 2) (by simp) with h47211 | h47211
                                · linarith only [h46977, h47211, hlam]
                                · linarith only [h0, h47211, hlam]
                            · have p47198_0 := h47198c.1
                              have p47198_1 := h47198c.2.1
                              have p47198_2 := h47198c.2.2.1
                              have p47198_3 := h47198c.2.2.2
                              linarith only [h0, hc01, hc13, hlam, hphi, p47198_1]
                            · have p47198_0 := h47198c.1
                              have p47198_1 := h47198c.2.1
                              have p47198_2 := h47198c.2.2.1
                              have p47198_3 := h47198c.2.2.2
                              linarith only [hlam, p47198_0]
                            · have p47198_0 := h47198c.1
                              have p47198_1 := h47198c.2.1
                              have p47198_2 := h47198c.2.2.1
                              have p47198_3 := h47198c.2.2.2
                              linarith only [h0, h46977, h47189, h47193, hc01, hc23, hlam, hphi, ht12, p47198_1]
                            · have p47198_0 := h47198c.1
                              have p47198_1 := h47198c.2.1
                              have p47198_2 := h47198c.2.2.1
                              have p47198_3 := h47198c.2.2.2
                              linarith only [h0, h46977, h47189, hc01, hc23, hlam, hphi, ht12, p47198_1]
                            · have p47198_0 := h47198c.1
                              have p47198_1 := h47198c.2.1
                              have p47198_2 := h47198c.2.2.1
                              have p47198_3 := h47198c.2.2.2
                              rcases p47198_3 (m.d 0 1) (by simp) with h47218 | h47218
                              · linarith only [h47218, hlam, p47198_0]
                              · rcases p47198_3 (m.d 1 2) (by simp) with h47220 | h47220
                                · linarith only [h47187, h47220, hlam]
                                · linarith only [h0, h47220, hlam]
                            · have p47198_0 := h47198c.1
                              have p47198_1 := h47198c.2.1
                              have p47198_2 := h47198c.2.2.1
                              have p47198_3 := h47198c.2.2.2
                              linarith only [h0, hc01, hc14, hlam, hphi, p47198_1]
                            · have p47198_0 := h47198c.1
                              have p47198_1 := h47198c.2.1
                              have p47198_2 := h47198c.2.2.1
                              have p47198_3 := h47198c.2.2.2
                              linarith only [h47191, hlam, p47198_1]
                            · have p47198_0 := h47198c.1
                              have p47198_1 := h47198c.2.1
                              have p47198_2 := h47198c.2.2.1
                              have p47198_3 := h47198c.2.2.2
                              linarith only [hlam, p47198_0]
                            · have p47198_0 := h47198c.1
                              have p47198_1 := h47198c.2.1
                              have p47198_2 := h47198c.2.2.1
                              have p47198_3 := h47198c.2.2.2
                              linarith only [h0, h47187, h47189, h47194, hc01, hc23, hlam, hphi, ht12, p47198_1]
                            · have p47198_0 := h47198c.1
                              have p47198_1 := h47198c.2.1
                              have p47198_2 := h47198c.2.2.1
                              have p47198_3 := h47198c.2.2.2
                              rcases p47198_3 (m.d 0 1) (by simp) with h47227 | h47227
                              · linarith only [h47227, hlam, p47198_0]
                              · rcases p47198_3 (m.d 1 2) (by simp) with h47229 | h47229
                                · linarith only [h47189, h47229, hlam]
                                · linarith only [h0, h47229, hlam]
                            · have p47198_0 := h47198c.1
                              have p47198_1 := h47198c.2.1
                              have p47198_2 := h47198c.2.2.1
                              have p47198_3 := h47198c.2.2.2
                              linarith only [h0, hc01, hc15, hlam, hphi, p47198_1]
                            · have p47198_0 := h47198c.1
                              have p47198_1 := h47198c.2.1
                              have p47198_2 := h47198c.2.2.1
                              have p47198_3 := h47198c.2.2.2
                              linarith only [h47192, hlam, p47198_0]
                            · have p47198_0 := h47198c.1
                              have p47198_1 := h47198c.2.1
                              have p47198_2 := h47198c.2.2.1
                              have p47198_3 := h47198c.2.2.2
                              linarith only [h47193, hlam, p47198_0]
                            · have p47198_0 := h47198c.1
                              have p47198_1 := h47198c.2.1
                              have p47198_2 := h47198c.2.2.1
                              have p47198_3 := h47198c.2.2.2
                              linarith only [hlam, p47198_0]
                          · rcases h1bigk with h47236c | h47236c | h47236c | h47236c | h47236c | h47236c | h47236c | h47236c | h47236c | h47236c | h47236c | h47236c | h47236c | h47236c | h47236c | h47236c | h47236c | h47236c | h47236c | h47236c | h47236c | h47236c | h47236c | h47236c | h47236c
                            · have p47236_0 := h47236c.1
                              have p47236_1 := h47236c.2.1
                              have p47236_2 := h47236c.2.2.1
                              have p47236_3 := h47236c.2.2.2
                              linarith only [hlam, p47236_0]
                            · have p47236_0 := h47236c.1
                              have p47236_1 := h47236c.2.1
                              have p47236_2 := h47236c.2.2.1
                              have p47236_3 := h47236c.2.2.2
                              linarith only [h0, hlam, p47236_0]
                            · have p47236_0 := h47236c.1
                              have p47236_1 := h47236c.2.1
                              have p47236_2 := h47236c.2.2.1
                              have p47236_3 := h47236c.2.2.2
                              linarith only [h33187, hlam, p47236_0]
                            · have p47236_0 := h47236c.1
                              have p47236_1 := h47236c.2.1
                              have p47236_2 := h47236c.2.2.1
                              have p47236_3 := h47236c.2.2.2
                              linarith only [h36828, hlam, p47236_0]
                            · have p47236_0 := h47236c.1
                              have p47236_1 := h47236c.2.1
                              have p47236_2 := h47236c.2.2.1
                              have p47236_3 := h47236c.2.2.2
                              linarith only [h39227, hlam, p47236_0]
                            · have p47236_0 := h47236c.1
                              have p47236_1 := h47236c.2.1
                              have p47236_2 := h47236c.2.2.1
                              have p47236_3 := h47236c.2.2.2
                              linarith only [h46977, hc01, hc23, hlam, hphi, ht12, p47236_1]
                            · have p47236_0 := h47236c.1
                              have p47236_1 := h47236c.2.1
                              have p47236_2 := h47236c.2.2.1
                              have p47236_3 := h47236c.2.2.2
                              linarith only [hlam, p47236_0]
                            · have p47236_0 := h47236c.1
                              have p47236_1 := h47236c.2.1
                              have p47236_2 := h47236c.2.2.1
                              have p47236_3 := h47236c.2.2.2
                              linarith only [h46977, hlam, p47236_1]
                            · have p47236_0 := h47236c.1
                              have p47236_1 := h47236c.2.1
                              have p47236_2 := h47236c.2.2.1
                              have p47236_3 := h47236c.2.2.2
                              linarith only [h47187, hlam, p47236_1]
                            · have p47236_0 := h47236c.1
                              have p47236_1 := h47236c.2.1
                              have p47236_2 := h47236c.2.2.1
                              have p47236_3 := h47236c.2.2.2
                              linarith only [h47189, hlam, p47236_1]
                            · have p47236_0 := h47236c.1
                              have p47236_1 := h47236c.2.1
                              have p47236_2 := h47236c.2.2.1
                              have p47236_3 := h47236c.2.2.2
                              rcases p47236_3 (m.d 0 1) (by simp) with h47247 | h47247
                              · linarith only [h47247, hlam, p47236_0]
                              · rcases p47236_3 (m.d 1 2) (by simp) with h47249 | h47249
                                · linarith only [h46977, h47249, hlam]
                                · linarith only [h0, h47249, hlam]
                            · have p47236_0 := h47236c.1
                              have p47236_1 := h47236c.2.1
                              have p47236_2 := h47236c.2.2.1
                              have p47236_3 := h47236c.2.2.2
                              linarith only [h0, h46977, hc01, hc23, hlam, hphi, ht12, p47236_1]
                            · have p47236_0 := h47236c.1
                              have p47236_1 := h47236c.2.1
                              have p47236_2 := h47236c.2.2.1
                              have p47236_3 := h47236c.2.2.2
                              linarith only [hlam, p47236_0]
                            · have p47236_0 := h47236c.1
                              have p47236_1 := h47236c.2.1
                              have p47236_2 := h47236c.2.2.1
                              have p47236_3 := h47236c.2.2.2
                              linarith only [h36828, h46977, hc01, hc23, hlam, hphi, ht12, p47236_1]
                            · have p47236_0 := h47236c.1
                              have p47236_1 := h47236c.2.1
                              have p47236_2 := h47236c.2.2.1
                              have p47236_3 := h47236c.2.2.2
                              linarith only [h39227, h46977, hc01, hc23, hlam, hphi, ht12, p47236_1]
                            · have p47236_0 := h47236c.1
                              have p47236_1 := h47236c.2.1
                              have p47236_2 := h47236c.2.2.1
                              have p47236_3 := h47236c.2.2.2
                              rcases p47236_3 (m.d 0 1) (by simp) with h47256 | h47256
                              · linarith only [h47256, hlam, p47236_0]
                              · rcases p47236_3 (m.d 1 2) (by simp) with h47258 | h47258
                                · linarith only [h47187, h47258, hlam]
                                · linarith only [h0, h47258, hlam]
                            · have p47236_0 := h47236c.1
                              have p47236_1 := h47236c.2.1
                              have p47236_2 := h47236c.2.2.1
                              have p47236_3 := h47236c.2.2.2
                              linarith only [h0, hc01, hc14, hlam, hphi, p47236_1]
                            · have p47236_0 := h47236c.1
                              have p47236_1 := h47236c.2.1
                              have p47236_2 := h47236c.2.2.1
                              have p47236_3 := h47236c.2.2.2
                              linarith only [h47191, hlam, p47236_1]
                            · have p47236_0 := h47236c.1
                              have p47236_1 := h47236c.2.1
                              have p47236_2 := h47236c.2.2.1
                              have p47236_3 := h47236c.2.2.2
                              linarith only [hlam, p47236_0]
                            · have p47236_0 := h47236c.1
                              have p47236_1 := h47236c.2.1
                              have p47236_2 := h47236c.2.2.1
                              have p47236_3 := h47236c.2.2.2
                              linarith only [h39227, h47187, h47194, hc01, hc23, hlam, hphi, ht12, p47236_1]
                            · have p47236_0 := h47236c.1
                              have p47236_1 := h47236c.2.1
                              have p47236_2 := h47236c.2.2.1
                              have p47236_3 := h47236c.2.2.2
                              rcases p47236_3 (m.d 0 1) (by simp) with h47265 | h47265
                              · linarith only [h47265, hlam, p47236_0]
                              · rcases p47236_3 (m.d 1 2) (by simp) with h47267 | h47267
                                · linarith only [h47189, h47267, hlam]
                                · linarith only [h0, h47267, hlam]
                            · have p47236_0 := h47236c.1
                              have p47236_1 := h47236c.2.1
                              have p47236_2 := h47236c.2.2.1
                              have p47236_3 := h47236c.2.2.2
                              linarith only [h0, hc01, hc15, hlam, hphi, p47236_1]
                            · have p47236_0 := h47236c.1
                              have p47236_1 := h47236c.2.1
                              have p47236_2 := h47236c.2.2.1
                              have p47236_3 := h47236c.2.2.2
                              linarith only [h47192, hlam, p47236_0]
                            · have p47236_0 := h47236c.1
                              have p47236_1 := h47236c.2.1
                              have p47236_2 := h47236c.2.2.1
                              have p47236_3 := h47236c.2.2.2
                              linarith only [h47193, hlam, p47236_0]
                            · have p47236_0 := h47236c.1
                              have p47236_1 := h47236c.2.1
                              have p47236_2 := h47236c.2.2.1
                              have p47236_3 := h47236c.2.2.2
                              linarith only [hlam, p47236_0]
                        · linarith only [h33187, h36828, h46974, h46976, h46977, h47187, h47196, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h33187, h46975, h46977, h47195, hlam]
                    · linarith only [h33187, h46974, h46977, h47194, hlam]
                  · linarith only [h36828, h46976, h47193, hlam]
                · linarith only [h33187, h46975, h47192, hlam]
              · linarith only [h33187, h46974, h47191, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h47280 | h47280
        · rcases m.htr 1 2 4 (by decide) (by decide) with h47281 | h47281
          · rcases m.htr 1 2 5 (by decide) (by decide) with h47282 | h47282
            · rcases m.htr 1 3 4 (by decide) (by decide) with h47283 | h47283
              · rcases m.htr 1 3 5 (by decide) (by decide) with h47284 | h47284
                · rcases m.htr 1 4 5 (by decide) (by decide) with h47285 | h47285
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h47286 | h47286
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h47287 | h47287
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h47288 | h47288
                        · linarith only [h36828, h46976, h47280, h47286, h47288, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h45992, h47280, h47283, h47285, h47288, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h33187, h41027, h46975, h47280, h47287, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h33187, h41027, h46974, h47280, h47286, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h47293 | h47293
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h47294 | h47294
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h47295 | h47295
                        · linarith only [h36828, h47285, h47295, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h47297 | h47297
                          · linarith only [h41027, h45992, h46974, h47280, h47281, h47285, h47297, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                          · rcases h1bigk with h47299c | h47299c | h47299c | h47299c | h47299c | h47299c | h47299c | h47299c | h47299c | h47299c | h47299c | h47299c | h47299c | h47299c | h47299c | h47299c | h47299c | h47299c | h47299c | h47299c | h47299c | h47299c | h47299c | h47299c | h47299c
                            · have p47299_0 := h47299c.1
                              have p47299_1 := h47299c.2.1
                              have p47299_2 := h47299c.2.2.1
                              have p47299_3 := h47299c.2.2.2
                              linarith only [hlam, p47299_0]
                            · have p47299_0 := h47299c.1
                              have p47299_1 := h47299c.2.1
                              have p47299_2 := h47299c.2.2.1
                              have p47299_3 := h47299c.2.2.2
                              linarith only [h0, hlam, p47299_0]
                            · have p47299_0 := h47299c.1
                              have p47299_1 := h47299c.2.1
                              have p47299_2 := h47299c.2.2.1
                              have p47299_3 := h47299c.2.2.2
                              linarith only [h33187, hlam, p47299_0]
                            · have p47299_0 := h47299c.1
                              have p47299_1 := h47299c.2.1
                              have p47299_2 := h47299c.2.2.1
                              have p47299_3 := h47299c.2.2.2
                              linarith only [h36828, hlam, p47299_0]
                            · have p47299_0 := h47299c.1
                              have p47299_1 := h47299c.2.1
                              have p47299_2 := h47299c.2.2.1
                              have p47299_3 := h47299c.2.2.2
                              linarith only [h39227, hlam, p47299_0]
                            · have p47299_0 := h47299c.1
                              have p47299_1 := h47299c.2.1
                              have p47299_2 := h47299c.2.2.1
                              have p47299_3 := h47299c.2.2.2
                              rcases p47299_3 (m.d 0 1) (by simp) with h47305 | h47305
                              · linarith only [h47305, hlam, p47299_0]
                              · rcases p47299_3 (m.d 1 2) (by simp) with h47307 | h47307
                                · rcases p47299_3 (m.d 1 3) (by simp) with h47308 | h47308
                                  · linarith only [h47280, h47308, hlam]
                                  · linarith only [h33187, h47308, hlam]
                                · linarith only [h47307, hlam, p47299_0]
                            · have p47299_0 := h47299c.1
                              have p47299_1 := h47299c.2.1
                              have p47299_2 := h47299c.2.2.1
                              have p47299_3 := h47299c.2.2.2
                              linarith only [hlam, p47299_0]
                            · have p47299_0 := h47299c.1
                              have p47299_1 := h47299c.2.1
                              have p47299_2 := h47299c.2.2.1
                              have p47299_3 := h47299c.2.2.2
                              linarith only [h33187, hc01, hc12, hlam, hphi, p47299_1]
                            · have p47299_0 := h47299c.1
                              have p47299_1 := h47299c.2.1
                              have p47299_2 := h47299c.2.2.1
                              have p47299_3 := h47299c.2.2.2
                              linarith only [h0, h45992, h47281, hc01, hc12, hlam, hphi, p47299_1]
                            · have p47299_0 := h47299c.1
                              have p47299_1 := h47299c.2.1
                              have p47299_2 := h47299c.2.2.1
                              have p47299_3 := h47299c.2.2.2
                              linarith only [h39227, hc01, hc12, hlam, hphi, p47299_1]
                            · have p47299_0 := h47299c.1
                              have p47299_1 := h47299c.2.1
                              have p47299_2 := h47299c.2.2.1
                              have p47299_3 := h47299c.2.2.2
                              rcases p47299_3 (m.d 0 1) (by simp) with h47316 | h47316
                              · linarith only [h47316, hlam, p47299_0]
                              · rcases p47299_3 (m.d 1 2) (by simp) with h47318 | h47318
                                · rcases p47299_3 (m.d 1 3) (by simp) with h47319 | h47319
                                  · rcases p47299_3 (m.d 1 4) (by simp) with h47320 | h47320
                                    · linarith only [h47283, h47320, hlam]
                                    · linarith only [h36828, h47320, hlam]
                                  · linarith only [h47319, hlam, p47299_0]
                                · linarith only [h0, h47318, hlam]
                            · have p47299_0 := h47299c.1
                              have p47299_1 := h47299c.2.1
                              have p47299_2 := h47299c.2.2.1
                              have p47299_3 := h47299c.2.2.2
                              linarith only [h47280, hlam, p47299_0]
                            · have p47299_0 := h47299c.1
                              have p47299_1 := h47299c.2.1
                              have p47299_2 := h47299c.2.2.1
                              have p47299_3 := h47299c.2.2.2
                              linarith only [hlam, p47299_0]
                            · have p47299_0 := h47299c.1
                              have p47299_1 := h47299c.2.1
                              have p47299_2 := h47299c.2.2.1
                              have p47299_3 := h47299c.2.2.2
                              linarith only [h0, h45992, h47281, hc01, hc13, hlam, hphi, p47299_1]
                            · have p47299_0 := h47299c.1
                              have p47299_1 := h47299c.2.1
                              have p47299_2 := h47299c.2.2.1
                              have p47299_3 := h47299c.2.2.2
                              linarith only [h39227, h47280, hc01, hc12, hlam, hphi, p47299_1]
                            · have p47299_0 := h47299c.1
                              have p47299_1 := h47299c.2.1
                              have p47299_2 := h47299c.2.2.1
                              have p47299_3 := h47299c.2.2.2
                              linarith only [h47285, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p47299_1]
                            · have p47299_0 := h47299c.1
                              have p47299_1 := h47299c.2.1
                              have p47299_2 := h47299c.2.2.1
                              have p47299_3 := h47299c.2.2.2
                              linarith only [h47281, hlam, p47299_0]
                            · have p47299_0 := h47299c.1
                              have p47299_1 := h47299c.2.1
                              have p47299_2 := h47299c.2.2.1
                              have p47299_3 := h47299c.2.2.2
                              linarith only [h47283, hlam, p47299_1]
                            · have p47299_0 := h47299c.1
                              have p47299_1 := h47299c.2.1
                              have p47299_2 := h47299c.2.2.1
                              have p47299_3 := h47299c.2.2.2
                              linarith only [hlam, p47299_0]
                            · have p47299_0 := h47299c.1
                              have p47299_1 := h47299c.2.1
                              have p47299_2 := h47299c.2.2.1
                              have p47299_3 := h47299c.2.2.2
                              linarith only [h47285, hlam, p47299_1]
                            · have p47299_0 := h47299c.1
                              have p47299_1 := h47299c.2.1
                              have p47299_2 := h47299c.2.2.1
                              have p47299_3 := h47299c.2.2.2
                              rcases p47299_3 (m.d 0 1) (by simp) with h47334 | h47334
                              · linarith only [h47334, hlam, p47299_0]
                              · rcases p47299_3 (m.d 1 2) (by simp) with h47336 | h47336
                                · rcases p47299_3 (m.d 1 3) (by simp) with h47337 | h47337
                                  · rcases p47299_3 (m.d 1 4) (by simp) with h47338 | h47338
                                    · linarith only [h47285, h47338, hlam]
                                    · linarith only [h36828, h47338, hlam]
                                  · linarith only [h33187, h47337, hlam]
                                · linarith only [h0, h47336, hlam]
                            · have p47299_0 := h47299c.1
                              have p47299_1 := h47299c.2.1
                              have p47299_2 := h47299c.2.2.1
                              have p47299_3 := h47299c.2.2.2
                              linarith only [h47282, hlam, p47299_0]
                            · have p47299_0 := h47299c.1
                              have p47299_1 := h47299c.2.1
                              have p47299_2 := h47299c.2.2.1
                              have p47299_3 := h47299c.2.2.2
                              linarith only [h47284, hlam, p47299_0]
                            · have p47299_0 := h47299c.1
                              have p47299_1 := h47299c.2.1
                              have p47299_2 := h47299c.2.2.1
                              have p47299_3 := h47299c.2.2.2
                              linarith only [h36828, hc01, hc15, hlam, hphi, p47299_1]
                            · have p47299_0 := h47299c.1
                              have p47299_1 := h47299c.2.1
                              have p47299_2 := h47299c.2.2.1
                              have p47299_3 := h47299c.2.2.2
                              linarith only [hlam, p47299_0]
                      · linarith only [h41027, h46975, h47294, hlam]
                    · linarith only [h41027, h46974, h47293, hlam]
                · linarith only [h33187, h41027, h46975, h47280, h47284, hc01, hc12, hlam, hphi]
              · linarith only [h41027, h46974, h47280, h47283, hlam]
            · linarith only [h0, h41027, h47280, h47282, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h41027, h47280, h47281, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h47353 | h47353
          · linarith only [h0, h45992, h47280, h47353, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h47355 | h47355
            · linarith only [h0, h46639, h47280, h47355, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h47357 | h47357
              · rcases m.htr 1 3 5 (by decide) (by decide) with h47358 | h47358
                · rcases m.htr 1 4 5 (by decide) (by decide) with h47359 | h47359
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h47360 | h47360
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h47361 | h47361
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h47362 | h47362
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h47363 | h47363
                          · linarith only [h46974, h46976, h47363, hlam]
                          · rcases h1bigk with h47365c | h47365c | h47365c | h47365c | h47365c | h47365c | h47365c | h47365c | h47365c | h47365c | h47365c | h47365c | h47365c | h47365c | h47365c | h47365c | h47365c | h47365c | h47365c | h47365c | h47365c | h47365c | h47365c | h47365c | h47365c
                            · have p47365_0 := h47365c.1
                              have p47365_1 := h47365c.2.1
                              have p47365_2 := h47365c.2.2.1
                              have p47365_3 := h47365c.2.2.2
                              linarith only [hlam, p47365_0]
                            · have p47365_0 := h47365c.1
                              have p47365_1 := h47365c.2.1
                              have p47365_2 := h47365c.2.2.1
                              have p47365_3 := h47365c.2.2.2
                              linarith only [h0, hlam, p47365_0]
                            · have p47365_0 := h47365c.1
                              have p47365_1 := h47365c.2.1
                              have p47365_2 := h47365c.2.2.1
                              have p47365_3 := h47365c.2.2.2
                              linarith only [h33187, hlam, p47365_0]
                            · have p47365_0 := h47365c.1
                              have p47365_1 := h47365c.2.1
                              have p47365_2 := h47365c.2.2.1
                              have p47365_3 := h47365c.2.2.2
                              linarith only [h36828, hlam, p47365_0]
                            · have p47365_0 := h47365c.1
                              have p47365_1 := h47365c.2.1
                              have p47365_2 := h47365c.2.2.1
                              have p47365_3 := h47365c.2.2.2
                              linarith only [h39227, hlam, p47365_0]
                            · have p47365_0 := h47365c.1
                              have p47365_1 := h47365c.2.1
                              have p47365_2 := h47365c.2.2.1
                              have p47365_3 := h47365c.2.2.2
                              linarith only [h47355, h47360, h47362, hc01, hc23, hlam, hphi, ht12, p47365_1]
                            · have p47365_0 := h47365c.1
                              have p47365_1 := h47365c.2.1
                              have p47365_2 := h47365c.2.2.1
                              have p47365_3 := h47365c.2.2.2
                              linarith only [hlam, p47365_0]
                            · have p47365_0 := h47365c.1
                              have p47365_1 := h47365c.2.1
                              have p47365_2 := h47365c.2.2.1
                              have p47365_3 := h47365c.2.2.2
                              linarith only [h47280, hlam, p47365_1]
                            · have p47365_0 := h47365c.1
                              have p47365_1 := h47365c.2.1
                              have p47365_2 := h47365c.2.2.1
                              have p47365_3 := h47365c.2.2.2
                              linarith only [h47353, hlam, p47365_1]
                            · have p47365_0 := h47365c.1
                              have p47365_1 := h47365c.2.1
                              have p47365_2 := h47365c.2.2.1
                              have p47365_3 := h47365c.2.2.2
                              linarith only [h47355, hlam, p47365_1]
                            · have p47365_0 := h47365c.1
                              have p47365_1 := h47365c.2.1
                              have p47365_2 := h47365c.2.2.1
                              have p47365_3 := h47365c.2.2.2
                              rcases p47365_3 (m.d 0 1) (by simp) with h47376 | h47376
                              · linarith only [h47376, hlam, p47365_0]
                              · rcases p47365_3 (m.d 1 2) (by simp) with h47378 | h47378
                                · linarith only [h47280, h47378, hlam]
                                · linarith only [h0, h47378, hlam]
                            · have p47365_0 := h47365c.1
                              have p47365_1 := h47365c.2.1
                              have p47365_2 := h47365c.2.2.1
                              have p47365_3 := h47365c.2.2.2
                              linarith only [h0, h47280, hc01, hc23, hlam, hphi, ht12, p47365_1]
                            · have p47365_0 := h47365c.1
                              have p47365_1 := h47365c.2.1
                              have p47365_2 := h47365c.2.2.1
                              have p47365_3 := h47365c.2.2.2
                              linarith only [hlam, p47365_0]
                            · have p47365_0 := h47365c.1
                              have p47365_1 := h47365c.2.1
                              have p47365_2 := h47365c.2.2.1
                              have p47365_3 := h47365c.2.2.2
                              linarith only [h46976, h47280, h47359, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p47365_1]
                            · have p47365_0 := h47365c.1
                              have p47365_1 := h47365c.2.1
                              have p47365_2 := h47365c.2.2.1
                              have p47365_3 := h47365c.2.2.2
                              linarith only [h39227, h47280, hc01, hc23, hlam, hphi, ht12, p47365_1]
                            · have p47365_0 := h47365c.1
                              have p47365_1 := h47365c.2.1
                              have p47365_2 := h47365c.2.2.1
                              have p47365_3 := h47365c.2.2.2
                              rcases p47365_3 (m.d 0 1) (by simp) with h47385 | h47385
                              · linarith only [h47385, hlam, p47365_0]
                              · rcases p47365_3 (m.d 1 2) (by simp) with h47387 | h47387
                                · linarith only [h47353, h47387, hlam]
                                · linarith only [h0, h47387, hlam]
                            · have p47365_0 := h47365c.1
                              have p47365_1 := h47365c.2.1
                              have p47365_2 := h47365c.2.2.1
                              have p47365_3 := h47365c.2.2.2
                              linarith only [h0, hc01, hc14, hlam, hphi, p47365_1]
                            · have p47365_0 := h47365c.1
                              have p47365_1 := h47365c.2.1
                              have p47365_2 := h47365c.2.2.1
                              have p47365_3 := h47365c.2.2.2
                              linarith only [h47357, hlam, p47365_1]
                            · have p47365_0 := h47365c.1
                              have p47365_1 := h47365c.2.1
                              have p47365_2 := h47365c.2.2.1
                              have p47365_3 := h47365c.2.2.2
                              linarith only [hlam, p47365_0]
                            · have p47365_0 := h47365c.1
                              have p47365_1 := h47365c.2.1
                              have p47365_2 := h47365c.2.2.1
                              have p47365_3 := h47365c.2.2.2
                              linarith only [h0, h45992, h46976, h47353, h47359, h47360, hc01, hc23, hlam, hphi, ht12, p47365_1]
                            · have p47365_0 := h47365c.1
                              have p47365_1 := h47365c.2.1
                              have p47365_2 := h47365c.2.2.1
                              have p47365_3 := h47365c.2.2.2
                              rcases p47365_3 (m.d 0 1) (by simp) with h47394 | h47394
                              · linarith only [h47394, hlam, p47365_0]
                              · rcases p47365_3 (m.d 1 2) (by simp) with h47396 | h47396
                                · linarith only [h47355, h47396, hlam]
                                · linarith only [h0, h47396, hlam]
                            · have p47365_0 := h47365c.1
                              have p47365_1 := h47365c.2.1
                              have p47365_2 := h47365c.2.2.1
                              have p47365_3 := h47365c.2.2.2
                              linarith only [h0, hc01, hc15, hlam, hphi, p47365_1]
                            · have p47365_0 := h47365c.1
                              have p47365_1 := h47365c.2.1
                              have p47365_2 := h47365c.2.2.1
                              have p47365_3 := h47365c.2.2.2
                              linarith only [h47358, hlam, p47365_0]
                            · have p47365_0 := h47365c.1
                              have p47365_1 := h47365c.2.1
                              have p47365_2 := h47365c.2.2.1
                              have p47365_3 := h47365c.2.2.2
                              linarith only [h47359, hlam, p47365_0]
                            · have p47365_0 := h47365c.1
                              have p47365_1 := h47365c.2.1
                              have p47365_2 := h47365c.2.2.1
                              have p47365_3 := h47365c.2.2.2
                              linarith only [hlam, p47365_0]
                        · linarith only [h0, h47353, h47362, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h33187, h46975, h46976, h47280, h47359, h47361, hc01, hc14, hlam, hphi]
                    · linarith only [h46974, h46976, h47280, h47357, h47359, h47360, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h47406 | h47406
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h47407 | h47407
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h47408 | h47408
                        · linarith only [h0, h47353, h47359, h47406, h47408, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h47353, h47408, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h33187, h46975, h47280, h47407, hlam]
                    · linarith only [h33187, h46974, h47280, h47406, hlam]
                · linarith only [h33187, h46975, h47358, hlam]
              · linarith only [h33187, h46974, h46976, h47357, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h47415 | h47415
      · linarith only [h46974, h46975, h47415, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h47417 | h47417
        · rcases m.htr 1 2 4 (by decide) (by decide) with h47418 | h47418
          · rcases m.htr 1 2 5 (by decide) (by decide) with h47419 | h47419
            · rcases m.htr 1 3 4 (by decide) (by decide) with h47420 | h47420
              · rcases m.htr 1 3 5 (by decide) (by decide) with h47421 | h47421
                · rcases m.htr 1 4 5 (by decide) (by decide) with h47422 | h47422
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h47423 | h47423
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h47424 | h47424
                      · linarith only [h46974, h46975, h47417, h47424, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h41027, h47417, h47421, h47424, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h33187, h41027, h46974, h47417, h47423, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h47428 | h47428
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h47429 | h47429
                      · linarith only [h46974, h46975, h47417, h47429, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h41027, h47421, h47429, hc01, hc13, hlam, hphi]
                    · linarith only [h0, h33187, h41027, h46974, h47417, h47428, hc01, hc12, hlam, hphi]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h47433 | h47433
                  · linarith only [h36828, h47415, h47420, h47421, h47433, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h47435 | h47435
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h47436 | h47436
                      · linarith only [h47417, h47421, h47436, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h47438 | h47438
                        · linarith only [h36828, h47433, h47438, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h47440 | h47440
                          · linarith only [h0, h45992, h47418, h47433, h47440, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases h1bigk with h47442c | h47442c | h47442c | h47442c | h47442c | h47442c | h47442c | h47442c | h47442c | h47442c | h47442c | h47442c | h47442c | h47442c | h47442c | h47442c | h47442c | h47442c | h47442c | h47442c | h47442c | h47442c | h47442c | h47442c | h47442c
                            · have p47442_0 := h47442c.1
                              have p47442_1 := h47442c.2.1
                              have p47442_2 := h47442c.2.2.1
                              have p47442_3 := h47442c.2.2.2
                              linarith only [hlam, p47442_0]
                            · have p47442_0 := h47442c.1
                              have p47442_1 := h47442c.2.1
                              have p47442_2 := h47442c.2.2.1
                              have p47442_3 := h47442c.2.2.2
                              linarith only [h0, hlam, p47442_0]
                            · have p47442_0 := h47442c.1
                              have p47442_1 := h47442c.2.1
                              have p47442_2 := h47442c.2.2.1
                              have p47442_3 := h47442c.2.2.2
                              linarith only [h33187, hlam, p47442_0]
                            · have p47442_0 := h47442c.1
                              have p47442_1 := h47442c.2.1
                              have p47442_2 := h47442c.2.2.1
                              have p47442_3 := h47442c.2.2.2
                              linarith only [h36828, hlam, p47442_0]
                            · have p47442_0 := h47442c.1
                              have p47442_1 := h47442c.2.1
                              have p47442_2 := h47442c.2.2.1
                              have p47442_3 := h47442c.2.2.2
                              linarith only [h39227, hlam, p47442_0]
                            · have p47442_0 := h47442c.1
                              have p47442_1 := h47442c.2.1
                              have p47442_2 := h47442c.2.2.1
                              have p47442_3 := h47442c.2.2.2
                              rcases p47442_3 (m.d 0 1) (by simp) with h47448 | h47448
                              · linarith only [h47448, hlam, p47442_0]
                              · rcases p47442_3 (m.d 1 2) (by simp) with h47450 | h47450
                                · rcases p47442_3 (m.d 1 3) (by simp) with h47451 | h47451
                                  · linarith only [h47417, h47451, hlam]
                                  · linarith only [h33187, h47451, hlam]
                                · linarith only [h47450, hlam, p47442_0]
                            · have p47442_0 := h47442c.1
                              have p47442_1 := h47442c.2.1
                              have p47442_2 := h47442c.2.2.1
                              have p47442_3 := h47442c.2.2.2
                              linarith only [hlam, p47442_0]
                            · have p47442_0 := h47442c.1
                              have p47442_1 := h47442c.2.1
                              have p47442_2 := h47442c.2.2.1
                              have p47442_3 := h47442c.2.2.2
                              linarith only [h33187, hc01, hc12, hlam, hphi, p47442_1]
                            · have p47442_0 := h47442c.1
                              have p47442_1 := h47442c.2.1
                              have p47442_2 := h47442c.2.2.1
                              have p47442_3 := h47442c.2.2.2
                              linarith only [h36828, hc01, hc12, hlam, hphi, p47442_1]
                            · have p47442_0 := h47442c.1
                              have p47442_1 := h47442c.2.1
                              have p47442_2 := h47442c.2.2.1
                              have p47442_3 := h47442c.2.2.2
                              linarith only [h39227, hc01, hc12, hlam, hphi, p47442_1]
                            · have p47442_0 := h47442c.1
                              have p47442_1 := h47442c.2.1
                              have p47442_2 := h47442c.2.2.1
                              have p47442_3 := h47442c.2.2.2
                              linarith only [h47421, h47440, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p47442_1]
                            · have p47442_0 := h47442c.1
                              have p47442_1 := h47442c.2.1
                              have p47442_2 := h47442c.2.2.1
                              have p47442_3 := h47442c.2.2.2
                              linarith only [h47417, hlam, p47442_0]
                            · have p47442_0 := h47442c.1
                              have p47442_1 := h47442c.2.1
                              have p47442_2 := h47442c.2.2.1
                              have p47442_3 := h47442c.2.2.2
                              linarith only [hlam, p47442_0]
                            · have p47442_0 := h47442c.1
                              have p47442_1 := h47442c.2.1
                              have p47442_2 := h47442c.2.2.1
                              have p47442_3 := h47442c.2.2.2
                              linarith only [h0, h45992, h47418, h47421, h47440, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p47442_1]
                            · have p47442_0 := h47442c.1
                              have p47442_1 := h47442c.2.1
                              have p47442_2 := h47442c.2.2.1
                              have p47442_3 := h47442c.2.2.2
                              linarith only [h47421, hlam, p47442_1]
                            · have p47442_0 := h47442c.1
                              have p47442_1 := h47442c.2.1
                              have p47442_2 := h47442c.2.2.1
                              have p47442_3 := h47442c.2.2.2
                              linarith only [h47420, h47421, h47440, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p47442_1]
                            · have p47442_0 := h47442c.1
                              have p47442_1 := h47442c.2.1
                              have p47442_2 := h47442c.2.2.1
                              have p47442_3 := h47442c.2.2.2
                              linarith only [h47418, hlam, p47442_0]
                            · have p47442_0 := h47442c.1
                              have p47442_1 := h47442c.2.1
                              have p47442_2 := h47442c.2.2.1
                              have p47442_3 := h47442c.2.2.2
                              linarith only [h47420, hlam, p47442_1]
                            · have p47442_0 := h47442c.1
                              have p47442_1 := h47442c.2.1
                              have p47442_2 := h47442c.2.2.1
                              have p47442_3 := h47442c.2.2.2
                              linarith only [hlam, p47442_0]
                            · have p47442_0 := h47442c.1
                              have p47442_1 := h47442c.2.1
                              have p47442_2 := h47442c.2.2.1
                              have p47442_3 := h47442c.2.2.2
                              linarith only [h47433, hlam, p47442_1]
                            · have p47442_0 := h47442c.1
                              have p47442_1 := h47442c.2.1
                              have p47442_2 := h47442c.2.2.1
                              have p47442_3 := h47442c.2.2.2
                              rcases p47442_3 (m.d 0 1) (by simp) with h47469 | h47469
                              · linarith only [h47469, hlam, p47442_0]
                              · rcases p47442_3 (m.d 1 2) (by simp) with h47471 | h47471
                                · rcases p47442_3 (m.d 1 3) (by simp) with h47472 | h47472
                                  · linarith only [h47421, h47472, hlam]
                                  · linarith only [h33187, h47472, hlam]
                                · linarith only [h0, h47471, hlam]
                            · have p47442_0 := h47442c.1
                              have p47442_1 := h47442c.2.1
                              have p47442_2 := h47442c.2.2.1
                              have p47442_3 := h47442c.2.2.2
                              linarith only [h47419, hlam, p47442_0]
                            · have p47442_0 := h47442c.1
                              have p47442_1 := h47442c.2.1
                              have p47442_2 := h47442c.2.2.1
                              have p47442_3 := h47442c.2.2.2
                              linarith only [h33187, hc01, hc15, hlam, hphi, p47442_1]
                            · have p47442_0 := h47442c.1
                              have p47442_1 := h47442c.2.1
                              have p47442_2 := h47442c.2.2.1
                              have p47442_3 := h47442c.2.2.2
                              linarith only [h36828, h47421, h47440, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p47442_1]
                            · have p47442_0 := h47442c.1
                              have p47442_1 := h47442c.2.1
                              have p47442_2 := h47442c.2.2.1
                              have p47442_3 := h47442c.2.2.2
                              linarith only [hlam, p47442_0]
                    · linarith only [h41027, h46639, h46974, h46975, h47435, hc02, hc25, hlam, hphi]
              · linarith only [h41027, h46974, h47417, h47420, hlam]
            · linarith only [h0, h41027, h47417, h47419, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h41027, h47417, h47418, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h47484 | h47484
          · linarith only [h0, h45992, h47417, h47484, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h47486 | h47486
            · linarith only [h0, h46639, h47417, h47486, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h47488 | h47488
              · rcases m.htr 1 3 5 (by decide) (by decide) with h47489 | h47489
                · rcases m.htr 1 4 5 (by decide) (by decide) with h47490 | h47490
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h47491 | h47491
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h47492 | h47492
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h47493 | h47493
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h47494 | h47494
                          · linarith only [h0, h45992, h46974, h46975, h47415, h47417, h47489, h47494, hc01, hc23, hlam, hphi, ht12]
                          · rcases h1bigk with h47496c | h47496c | h47496c | h47496c | h47496c | h47496c | h47496c | h47496c | h47496c | h47496c | h47496c | h47496c | h47496c | h47496c | h47496c | h47496c | h47496c | h47496c | h47496c | h47496c | h47496c | h47496c | h47496c | h47496c | h47496c
                            · have p47496_0 := h47496c.1
                              have p47496_1 := h47496c.2.1
                              have p47496_2 := h47496c.2.2.1
                              have p47496_3 := h47496c.2.2.2
                              linarith only [hlam, p47496_0]
                            · have p47496_0 := h47496c.1
                              have p47496_1 := h47496c.2.1
                              have p47496_2 := h47496c.2.2.1
                              have p47496_3 := h47496c.2.2.2
                              linarith only [h0, hlam, p47496_0]
                            · have p47496_0 := h47496c.1
                              have p47496_1 := h47496c.2.1
                              have p47496_2 := h47496c.2.2.1
                              have p47496_3 := h47496c.2.2.2
                              linarith only [h33187, hlam, p47496_0]
                            · have p47496_0 := h47496c.1
                              have p47496_1 := h47496c.2.1
                              have p47496_2 := h47496c.2.2.1
                              have p47496_3 := h47496c.2.2.2
                              linarith only [h36828, hlam, p47496_0]
                            · have p47496_0 := h47496c.1
                              have p47496_1 := h47496c.2.1
                              have p47496_2 := h47496c.2.2.1
                              have p47496_3 := h47496c.2.2.2
                              linarith only [h39227, hlam, p47496_0]
                            · have p47496_0 := h47496c.1
                              have p47496_1 := h47496c.2.1
                              have p47496_2 := h47496c.2.2.1
                              have p47496_3 := h47496c.2.2.2
                              linarith only [h47486, h47491, h47493, hc01, hc23, hlam, hphi, ht12, p47496_1]
                            · have p47496_0 := h47496c.1
                              have p47496_1 := h47496c.2.1
                              have p47496_2 := h47496c.2.2.1
                              have p47496_3 := h47496c.2.2.2
                              linarith only [hlam, p47496_0]
                            · have p47496_0 := h47496c.1
                              have p47496_1 := h47496c.2.1
                              have p47496_2 := h47496c.2.2.1
                              have p47496_3 := h47496c.2.2.2
                              linarith only [h47417, hlam, p47496_1]
                            · have p47496_0 := h47496c.1
                              have p47496_1 := h47496c.2.1
                              have p47496_2 := h47496c.2.2.1
                              have p47496_3 := h47496c.2.2.2
                              linarith only [h47484, hlam, p47496_1]
                            · have p47496_0 := h47496c.1
                              have p47496_1 := h47496c.2.1
                              have p47496_2 := h47496c.2.2.1
                              have p47496_3 := h47496c.2.2.2
                              linarith only [h47486, hlam, p47496_1]
                            · have p47496_0 := h47496c.1
                              have p47496_1 := h47496c.2.1
                              have p47496_2 := h47496c.2.2.1
                              have p47496_3 := h47496c.2.2.2
                              rcases p47496_3 (m.d 0 1) (by simp) with h47507 | h47507
                              · linarith only [h47507, hlam, p47496_0]
                              · rcases p47496_3 (m.d 1 2) (by simp) with h47509 | h47509
                                · linarith only [h47417, h47509, hlam]
                                · linarith only [h0, h47509, hlam]
                            · have p47496_0 := h47496c.1
                              have p47496_1 := h47496c.2.1
                              have p47496_2 := h47496c.2.2.1
                              have p47496_3 := h47496c.2.2.2
                              linarith only [h0, h47417, hc01, hc23, hlam, hphi, ht12, p47496_1]
                            · have p47496_0 := h47496c.1
                              have p47496_1 := h47496c.2.1
                              have p47496_2 := h47496c.2.2.1
                              have p47496_3 := h47496c.2.2.2
                              linarith only [hlam, p47496_0]
                            · have p47496_0 := h47496c.1
                              have p47496_1 := h47496c.2.1
                              have p47496_2 := h47496c.2.2.1
                              have p47496_3 := h47496c.2.2.2
                              linarith only [h46974, h46975, h47417, h47490, h47494, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p47496_1]
                            · have p47496_0 := h47496c.1
                              have p47496_1 := h47496c.2.1
                              have p47496_2 := h47496c.2.2.1
                              have p47496_3 := h47496c.2.2.2
                              linarith only [h39227, h47417, hc01, hc23, hlam, hphi, ht12, p47496_1]
                            · have p47496_0 := h47496c.1
                              have p47496_1 := h47496c.2.1
                              have p47496_2 := h47496c.2.2.1
                              have p47496_3 := h47496c.2.2.2
                              rcases p47496_3 (m.d 0 1) (by simp) with h47516 | h47516
                              · linarith only [h47516, hlam, p47496_0]
                              · rcases p47496_3 (m.d 1 2) (by simp) with h47518 | h47518
                                · linarith only [h47484, h47518, hlam]
                                · linarith only [h0, h47518, hlam]
                            · have p47496_0 := h47496c.1
                              have p47496_1 := h47496c.2.1
                              have p47496_2 := h47496c.2.2.1
                              have p47496_3 := h47496c.2.2.2
                              linarith only [h0, hc01, hc14, hlam, hphi, p47496_1]
                            · have p47496_0 := h47496c.1
                              have p47496_1 := h47496c.2.1
                              have p47496_2 := h47496c.2.2.1
                              have p47496_3 := h47496c.2.2.2
                              linarith only [h47488, hlam, p47496_1]
                            · have p47496_0 := h47496c.1
                              have p47496_1 := h47496c.2.1
                              have p47496_2 := h47496c.2.2.1
                              have p47496_3 := h47496c.2.2.2
                              linarith only [hlam, p47496_0]
                            · have p47496_0 := h47496c.1
                              have p47496_1 := h47496c.2.1
                              have p47496_2 := h47496c.2.2.1
                              have p47496_3 := h47496c.2.2.2
                              linarith only [h46974, h46975, h47484, h47490, h47491, h47494, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p47496_1]
                            · have p47496_0 := h47496c.1
                              have p47496_1 := h47496c.2.1
                              have p47496_2 := h47496c.2.2.1
                              have p47496_3 := h47496c.2.2.2
                              rcases p47496_3 (m.d 0 1) (by simp) with h47525 | h47525
                              · linarith only [h47525, hlam, p47496_0]
                              · rcases p47496_3 (m.d 1 2) (by simp) with h47527 | h47527
                                · linarith only [h47486, h47527, hlam]
                                · linarith only [h0, h47527, hlam]
                            · have p47496_0 := h47496c.1
                              have p47496_1 := h47496c.2.1
                              have p47496_2 := h47496c.2.2.1
                              have p47496_3 := h47496c.2.2.2
                              linarith only [h0, hc01, hc15, hlam, hphi, p47496_1]
                            · have p47496_0 := h47496c.1
                              have p47496_1 := h47496c.2.1
                              have p47496_2 := h47496c.2.2.1
                              have p47496_3 := h47496c.2.2.2
                              linarith only [h47489, hlam, p47496_0]
                            · have p47496_0 := h47496c.1
                              have p47496_1 := h47496c.2.1
                              have p47496_2 := h47496c.2.2.1
                              have p47496_3 := h47496c.2.2.2
                              linarith only [h47490, hlam, p47496_0]
                            · have p47496_0 := h47496c.1
                              have p47496_1 := h47496c.2.1
                              have p47496_2 := h47496c.2.2.1
                              have p47496_3 := h47496c.2.2.2
                              linarith only [hlam, p47496_0]
                        · linarith only [h0, h47484, h47493, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h47417, h47489, h47492, hlam]
                    · linarith only [h33187, h46974, h47417, h47491, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h47537 | h47537
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h47538 | h47538
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h47539 | h47539
                        · linarith only [h0, h47484, h47490, h47539, hc01, hc24, hlam, hphi, ht12]
                        · linarith only [h0, h47484, h47539, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h47417, h47489, h47538, hc01, hc15, hlam, hphi]
                    · linarith only [h46974, h46975, h47417, h47489, h47537, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h47544 | h47544
                  · linarith only [h45992, h47415, h47488, h47489, h47544, hc02, hc35, hlam, hphi, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h47546 | h47546
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h47547 | h47547
                      · linarith only [h0, h47484, h47488, h47489, h47547, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h47417, h47547, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h46974, h47417, h47546, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
              · linarith only [h33187, h46974, h47488, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h47552 | h47552
    · rcases m.htr 0 4 5 (by decide) (by decide) with h47553 | h47553
      · rcases m.htr 1 2 3 (by decide) (by decide) with h47554 | h47554
        · rcases m.htr 1 2 4 (by decide) (by decide) with h47555 | h47555
          · rcases m.htr 1 2 5 (by decide) (by decide) with h47556 | h47556
            · rcases m.htr 1 3 4 (by decide) (by decide) with h47557 | h47557
              · rcases m.htr 1 3 5 (by decide) (by decide) with h47558 | h47558
                · rcases m.htr 1 4 5 (by decide) (by decide) with h47559 | h47559
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h47560 | h47560
                    · linarith only [h46974, h47552, h47554, h47560, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h0, h41027, h47554, h47557, h47560, hc01, hc12, hlam, hphi]
                  · linarith only [h36828, h46639, h47553, h47556, h47559, hc01, hc12, hlam, hphi]
                · linarith only [h46974, h47557, h47558, hc03, hc35, hlam, hphi]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h47565 | h47565
                · rcases m.htr 1 4 5 (by decide) (by decide) with h47566 | h47566
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h47567 | h47567
                    · linarith only [h47554, h47557, h47567, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h47569 | h47569
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h47570 | h47570
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h47571 | h47571
                          · rcases h1bigk with h47572c | h47572c | h47572c | h47572c | h47572c | h47572c | h47572c | h47572c | h47572c | h47572c | h47572c | h47572c | h47572c | h47572c | h47572c | h47572c | h47572c | h47572c | h47572c | h47572c | h47572c | h47572c | h47572c | h47572c | h47572c
                            · have p47572_0 := h47572c.1
                              have p47572_1 := h47572c.2.1
                              have p47572_2 := h47572c.2.2.1
                              have p47572_3 := h47572c.2.2.2
                              linarith only [hlam, p47572_0]
                            · have p47572_0 := h47572c.1
                              have p47572_1 := h47572c.2.1
                              have p47572_2 := h47572c.2.2.1
                              have p47572_3 := h47572c.2.2.2
                              linarith only [h0, hlam, p47572_0]
                            · have p47572_0 := h47572c.1
                              have p47572_1 := h47572c.2.1
                              have p47572_2 := h47572c.2.2.1
                              have p47572_3 := h47572c.2.2.2
                              linarith only [h33187, hlam, p47572_0]
                            · have p47572_0 := h47572c.1
                              have p47572_1 := h47572c.2.1
                              have p47572_2 := h47572c.2.2.1
                              have p47572_3 := h47572c.2.2.2
                              linarith only [h36828, hlam, p47572_0]
                            · have p47572_0 := h47572c.1
                              have p47572_1 := h47572c.2.1
                              have p47572_2 := h47572c.2.2.1
                              have p47572_3 := h47572c.2.2.2
                              linarith only [h39227, hlam, p47572_0]
                            · have p47572_0 := h47572c.1
                              have p47572_1 := h47572c.2.1
                              have p47572_2 := h47572c.2.2.1
                              have p47572_3 := h47572c.2.2.2
                              rcases p47572_3 (m.d 0 1) (by simp) with h47578 | h47578
                              · linarith only [h47578, hlam, p47572_0]
                              · rcases p47572_3 (m.d 1 2) (by simp) with h47580 | h47580
                                · rcases p47572_3 (m.d 1 3) (by simp) with h47581 | h47581
                                  · linarith only [h47554, h47581, hlam]
                                  · linarith only [h33187, h47581, hlam]
                                · linarith only [h47580, hlam, p47572_0]
                            · have p47572_0 := h47572c.1
                              have p47572_1 := h47572c.2.1
                              have p47572_2 := h47572c.2.2.1
                              have p47572_3 := h47572c.2.2.2
                              linarith only [hlam, p47572_0]
                            · have p47572_0 := h47572c.1
                              have p47572_1 := h47572c.2.1
                              have p47572_2 := h47572c.2.2.1
                              have p47572_3 := h47572c.2.2.2
                              linarith only [h33187, hc01, hc12, hlam, hphi, p47572_1]
                            · have p47572_0 := h47572c.1
                              have p47572_1 := h47572c.2.1
                              have p47572_2 := h47572c.2.2.1
                              have p47572_3 := h47572c.2.2.2
                              linarith only [h0, h46639, h47554, h47557, h47569, hc01, hc12, hlam, hphi, p47572_1]
                            · have p47572_0 := h47572c.1
                              have p47572_1 := h47572c.2.1
                              have p47572_2 := h47572c.2.2.1
                              have p47572_3 := h47572c.2.2.2
                              linarith only [h0, h46639, h47556, hc01, hc12, hlam, hphi, p47572_1]
                            · have p47572_0 := h47572c.1
                              have p47572_1 := h47572c.2.1
                              have p47572_2 := h47572c.2.2.1
                              have p47572_3 := h47572c.2.2.2
                              linarith only [h47557, hc01, hc34, hlam, hphi, ht12, ht23, p47572_1]
                            · have p47572_0 := h47572c.1
                              have p47572_1 := h47572c.2.1
                              have p47572_2 := h47572c.2.2.1
                              have p47572_3 := h47572c.2.2.2
                              linarith only [h47554, hlam, p47572_0]
                            · have p47572_0 := h47572c.1
                              have p47572_1 := h47572c.2.1
                              have p47572_2 := h47572c.2.2.1
                              have p47572_3 := h47572c.2.2.2
                              linarith only [hlam, p47572_0]
                            · have p47572_0 := h47572c.1
                              have p47572_1 := h47572c.2.1
                              have p47572_2 := h47572c.2.2.1
                              have p47572_3 := h47572c.2.2.2
                              linarith only [h47557, hlam, p47572_0]
                            · have p47572_0 := h47572c.1
                              have p47572_1 := h47572c.2.1
                              have p47572_2 := h47572c.2.2.1
                              have p47572_3 := h47572c.2.2.2
                              linarith only [h0, h46639, h47556, h47557, hc01, hc34, hlam, hphi, ht12, ht23, p47572_1]
                            · have p47572_0 := h47572c.1
                              have p47572_1 := h47572c.2.1
                              have p47572_2 := h47572c.2.2.1
                              have p47572_3 := h47572c.2.2.2
                              rcases p47572_3 (m.d 0 1) (by simp) with h47594 | h47594
                              · linarith only [h47594, hlam, p47572_0]
                              · rcases p47572_3 (m.d 1 2) (by simp) with h47596 | h47596
                                · rcases p47572_3 (m.d 1 3) (by simp) with h47597 | h47597
                                  · linarith only [h47557, h47597, hlam]
                                  · linarith only [h33187, h47597, hlam]
                                · linarith only [h0, h47596, hlam]
                            · have p47572_0 := h47572c.1
                              have p47572_1 := h47572c.2.1
                              have p47572_2 := h47572c.2.2.1
                              have p47572_3 := h47572c.2.2.2
                              linarith only [h47555, hlam, p47572_0]
                            · have p47572_0 := h47572c.1
                              have p47572_1 := h47572c.2.1
                              have p47572_2 := h47572c.2.2.1
                              have p47572_3 := h47572c.2.2.2
                              linarith only [h33187, hc01, hc14, hlam, hphi, p47572_1]
                            · have p47572_0 := h47572c.1
                              have p47572_1 := h47572c.2.1
                              have p47572_2 := h47572c.2.2.1
                              have p47572_3 := h47572c.2.2.2
                              linarith only [hlam, p47572_0]
                            · have p47572_0 := h47572c.1
                              have p47572_1 := h47572c.2.1
                              have p47572_2 := h47572c.2.2.1
                              have p47572_3 := h47572c.2.2.2
                              linarith only [h0, h46639, h47556, h47557, hc01, hc34, hlam, hphi, ht12, ht23, p47572_1]
                            · have p47572_0 := h47572c.1
                              have p47572_1 := h47572c.2.1
                              have p47572_2 := h47572c.2.2.1
                              have p47572_3 := h47572c.2.2.2
                              linarith only [h47557, h47565, hc01, hc34, hlam, hphi, ht12, ht23, p47572_1]
                            · have p47572_0 := h47572c.1
                              have p47572_1 := h47572c.2.1
                              have p47572_2 := h47572c.2.2.1
                              have p47572_3 := h47572c.2.2.2
                              linarith only [h47556, hlam, p47572_0]
                            · have p47572_0 := h47572c.1
                              have p47572_1 := h47572c.2.1
                              have p47572_2 := h47572c.2.2.1
                              have p47572_3 := h47572c.2.2.2
                              linarith only [h47565, hlam, p47572_0]
                            · have p47572_0 := h47572c.1
                              have p47572_1 := h47572c.2.1
                              have p47572_2 := h47572c.2.2.1
                              have p47572_3 := h47572c.2.2.2
                              linarith only [h47566, hlam, p47572_0]
                            · have p47572_0 := h47572c.1
                              have p47572_1 := h47572c.2.1
                              have p47572_2 := h47572c.2.2.1
                              have p47572_3 := h47572c.2.2.2
                              linarith only [hlam, p47572_0]
                          · linarith only [h33187, h47557, h47571, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h0, h33187, h45992, h47552, h47553, h47557, h47570, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h41027, h47552, h47569, hlam]
                  · linarith only [h36828, h45992, h47553, h47566, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h41027, h47552, h47554, h47565, hlam]
            · linarith only [h0, h45992, h47555, h47556, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h41027, h47554, h47555, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h47617 | h47617
          · linarith only [h0, h45992, h47554, h47617, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h47619 | h47619
            · linarith only [h0, h46639, h47554, h47619, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h47621 | h47621
              · rcases m.htr 1 3 5 (by decide) (by decide) with h47622 | h47622
                · rcases m.htr 1 4 5 (by decide) (by decide) with h47623 | h47623
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h47624 | h47624
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h47625 | h47625
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h47626 | h47626
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h47627 | h47627
                          · rcases h1bigk with h47628c | h47628c | h47628c | h47628c | h47628c | h47628c | h47628c | h47628c | h47628c | h47628c | h47628c | h47628c | h47628c | h47628c | h47628c | h47628c | h47628c | h47628c | h47628c | h47628c | h47628c | h47628c | h47628c | h47628c | h47628c
                            · have p47628_0 := h47628c.1
                              have p47628_1 := h47628c.2.1
                              have p47628_2 := h47628c.2.2.1
                              have p47628_3 := h47628c.2.2.2
                              linarith only [hlam, p47628_0]
                            · have p47628_0 := h47628c.1
                              have p47628_1 := h47628c.2.1
                              have p47628_2 := h47628c.2.2.1
                              have p47628_3 := h47628c.2.2.2
                              linarith only [h0, hlam, p47628_0]
                            · have p47628_0 := h47628c.1
                              have p47628_1 := h47628c.2.1
                              have p47628_2 := h47628c.2.2.1
                              have p47628_3 := h47628c.2.2.2
                              linarith only [h33187, hlam, p47628_0]
                            · have p47628_0 := h47628c.1
                              have p47628_1 := h47628c.2.1
                              have p47628_2 := h47628c.2.2.1
                              have p47628_3 := h47628c.2.2.2
                              linarith only [h36828, hlam, p47628_0]
                            · have p47628_0 := h47628c.1
                              have p47628_1 := h47628c.2.1
                              have p47628_2 := h47628c.2.2.1
                              have p47628_3 := h47628c.2.2.2
                              linarith only [h39227, hlam, p47628_0]
                            · have p47628_0 := h47628c.1
                              have p47628_1 := h47628c.2.1
                              have p47628_2 := h47628c.2.2.1
                              have p47628_3 := h47628c.2.2.2
                              linarith only [h47619, h47624, h47626, hc01, hc23, hlam, hphi, ht12, p47628_1]
                            · have p47628_0 := h47628c.1
                              have p47628_1 := h47628c.2.1
                              have p47628_2 := h47628c.2.2.1
                              have p47628_3 := h47628c.2.2.2
                              linarith only [hlam, p47628_0]
                            · have p47628_0 := h47628c.1
                              have p47628_1 := h47628c.2.1
                              have p47628_2 := h47628c.2.2.1
                              have p47628_3 := h47628c.2.2.2
                              linarith only [h47554, hlam, p47628_1]
                            · have p47628_0 := h47628c.1
                              have p47628_1 := h47628c.2.1
                              have p47628_2 := h47628c.2.2.1
                              have p47628_3 := h47628c.2.2.2
                              linarith only [h47617, hlam, p47628_1]
                            · have p47628_0 := h47628c.1
                              have p47628_1 := h47628c.2.1
                              have p47628_2 := h47628c.2.2.1
                              have p47628_3 := h47628c.2.2.2
                              linarith only [h47619, hlam, p47628_1]
                            · have p47628_0 := h47628c.1
                              have p47628_1 := h47628c.2.1
                              have p47628_2 := h47628c.2.2.1
                              have p47628_3 := h47628c.2.2.2
                              rcases p47628_3 (m.d 0 1) (by simp) with h47639 | h47639
                              · linarith only [h47639, hlam, p47628_0]
                              · rcases p47628_3 (m.d 1 2) (by simp) with h47641 | h47641
                                · linarith only [h47554, h47641, hlam]
                                · linarith only [h0, h47641, hlam]
                            · have p47628_0 := h47628c.1
                              have p47628_1 := h47628c.2.1
                              have p47628_2 := h47628c.2.2.1
                              have p47628_3 := h47628c.2.2.2
                              linarith only [h0, h47554, hc01, hc23, hlam, hphi, ht12, p47628_1]
                            · have p47628_0 := h47628c.1
                              have p47628_1 := h47628c.2.1
                              have p47628_2 := h47628c.2.2.1
                              have p47628_3 := h47628c.2.2.2
                              linarith only [hlam, p47628_0]
                            · have p47628_0 := h47628c.1
                              have p47628_1 := h47628c.2.1
                              have p47628_2 := h47628c.2.2.1
                              have p47628_3 := h47628c.2.2.2
                              linarith only [h0, h47554, h47619, h47623, hc01, hc23, hlam, hphi, ht12, p47628_1]
                            · have p47628_0 := h47628c.1
                              have p47628_1 := h47628c.2.1
                              have p47628_2 := h47628c.2.2.1
                              have p47628_3 := h47628c.2.2.2
                              linarith only [h0, h47554, h47619, hc01, hc23, hlam, hphi, ht12, p47628_1]
                            · have p47628_0 := h47628c.1
                              have p47628_1 := h47628c.2.1
                              have p47628_2 := h47628c.2.2.1
                              have p47628_3 := h47628c.2.2.2
                              rcases p47628_3 (m.d 0 1) (by simp) with h47648 | h47648
                              · linarith only [h47648, hlam, p47628_0]
                              · rcases p47628_3 (m.d 1 2) (by simp) with h47650 | h47650
                                · linarith only [h47617, h47650, hlam]
                                · linarith only [h0, h47650, hlam]
                            · have p47628_0 := h47628c.1
                              have p47628_1 := h47628c.2.1
                              have p47628_2 := h47628c.2.2.1
                              have p47628_3 := h47628c.2.2.2
                              linarith only [h0, hc01, hc14, hlam, hphi, p47628_1]
                            · have p47628_0 := h47628c.1
                              have p47628_1 := h47628c.2.1
                              have p47628_2 := h47628c.2.2.1
                              have p47628_3 := h47628c.2.2.2
                              linarith only [h47621, hlam, p47628_1]
                            · have p47628_0 := h47628c.1
                              have p47628_1 := h47628c.2.1
                              have p47628_2 := h47628c.2.2.1
                              have p47628_3 := h47628c.2.2.2
                              linarith only [hlam, p47628_0]
                            · have p47628_0 := h47628c.1
                              have p47628_1 := h47628c.2.1
                              have p47628_2 := h47628c.2.2.1
                              have p47628_3 := h47628c.2.2.2
                              linarith only [h0, h47617, h47619, h47624, hc01, hc23, hlam, hphi, ht12, p47628_1]
                            · have p47628_0 := h47628c.1
                              have p47628_1 := h47628c.2.1
                              have p47628_2 := h47628c.2.2.1
                              have p47628_3 := h47628c.2.2.2
                              rcases p47628_3 (m.d 0 1) (by simp) with h47657 | h47657
                              · linarith only [h47657, hlam, p47628_0]
                              · rcases p47628_3 (m.d 1 2) (by simp) with h47659 | h47659
                                · linarith only [h47619, h47659, hlam]
                                · linarith only [h0, h47659, hlam]
                            · have p47628_0 := h47628c.1
                              have p47628_1 := h47628c.2.1
                              have p47628_2 := h47628c.2.2.1
                              have p47628_3 := h47628c.2.2.2
                              linarith only [h0, hc01, hc15, hlam, hphi, p47628_1]
                            · have p47628_0 := h47628c.1
                              have p47628_1 := h47628c.2.1
                              have p47628_2 := h47628c.2.2.1
                              have p47628_3 := h47628c.2.2.2
                              linarith only [h47622, hlam, p47628_0]
                            · have p47628_0 := h47628c.1
                              have p47628_1 := h47628c.2.1
                              have p47628_2 := h47628c.2.2.1
                              have p47628_3 := h47628c.2.2.2
                              linarith only [h47623, hlam, p47628_0]
                            · have p47628_0 := h47628c.1
                              have p47628_1 := h47628c.2.1
                              have p47628_2 := h47628c.2.2.1
                              have p47628_3 := h47628c.2.2.2
                              linarith only [hlam, p47628_0]
                          · linarith only [h46974, h47552, h47553, h47627, hc04, hc35, hlam, hphi, ht0b, ht5b]
                        · linarith only [h36828, h47553, h47617, h47626, hlam]
                      · linarith only [h33187, h47552, h47554, h47625, hlam]
                    · linarith only [h0, h47554, h47621, h47624, hc01, hc14, hlam, hphi]
                  · linarith only [h36828, h46974, h47552, h47553, h47623, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h46974, h47552, h47621, h47622, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h47672 | h47672
                · rcases m.htr 1 4 5 (by decide) (by decide) with h47673 | h47673
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h47674 | h47674
                    · linarith only [h0, h47619, h47621, h47672, h47674, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h47554, h47674, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h36828, h47553, h47673, hlam]
                · linarith only [h33187, h47552, h47672, hlam]
      · linarith only [h46974, h47552, h47553, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h47680 | h47680
      · rcases m.htr 1 2 3 (by decide) (by decide) with h47681 | h47681
        · rcases m.htr 1 2 4 (by decide) (by decide) with h47682 | h47682
          · rcases m.htr 1 2 5 (by decide) (by decide) with h47683 | h47683
            · rcases m.htr 1 3 4 (by decide) (by decide) with h47684 | h47684
              · rcases m.htr 1 3 5 (by decide) (by decide) with h47685 | h47685
                · rcases m.htr 1 4 5 (by decide) (by decide) with h47686 | h47686
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h47687 | h47687
                    · linarith only [h0, h41027, h46974, h47681, h47687, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h41027, h47684, h47687, hc01, hc13, hlam, hphi]
                  · linarith only [h36828, h47680, h47686, hlam]
                · linarith only [h0, h41027, h46974, h47684, h47685, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h47692 | h47692
                · linarith only [h0, h41027, h47552, h47684, h47692, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h47694 | h47694
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h47695 | h47695
                    · linarith only [h33187, h47684, h47695, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h47697 | h47697
                      · linarith only [h47681, h47692, h47697, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h47699 | h47699
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h47700 | h47700
                          · rcases h1bigk with h47701c | h47701c | h47701c | h47701c | h47701c | h47701c | h47701c | h47701c | h47701c | h47701c | h47701c | h47701c | h47701c | h47701c | h47701c | h47701c | h47701c | h47701c | h47701c | h47701c | h47701c | h47701c | h47701c | h47701c | h47701c
                            · have p47701_0 := h47701c.1
                              have p47701_1 := h47701c.2.1
                              have p47701_2 := h47701c.2.2.1
                              have p47701_3 := h47701c.2.2.2
                              linarith only [hlam, p47701_0]
                            · have p47701_0 := h47701c.1
                              have p47701_1 := h47701c.2.1
                              have p47701_2 := h47701c.2.2.1
                              have p47701_3 := h47701c.2.2.2
                              linarith only [h0, hlam, p47701_0]
                            · have p47701_0 := h47701c.1
                              have p47701_1 := h47701c.2.1
                              have p47701_2 := h47701c.2.2.1
                              have p47701_3 := h47701c.2.2.2
                              linarith only [h33187, hlam, p47701_0]
                            · have p47701_0 := h47701c.1
                              have p47701_1 := h47701c.2.1
                              have p47701_2 := h47701c.2.2.1
                              have p47701_3 := h47701c.2.2.2
                              linarith only [h36828, hlam, p47701_0]
                            · have p47701_0 := h47701c.1
                              have p47701_1 := h47701c.2.1
                              have p47701_2 := h47701c.2.2.1
                              have p47701_3 := h47701c.2.2.2
                              linarith only [h39227, hlam, p47701_0]
                            · have p47701_0 := h47701c.1
                              have p47701_1 := h47701c.2.1
                              have p47701_2 := h47701c.2.2.1
                              have p47701_3 := h47701c.2.2.2
                              rcases p47701_3 (m.d 0 1) (by simp) with h47707 | h47707
                              · linarith only [h47707, hlam, p47701_0]
                              · rcases p47701_3 (m.d 1 2) (by simp) with h47709 | h47709
                                · rcases p47701_3 (m.d 1 3) (by simp) with h47710 | h47710
                                  · linarith only [h47681, h47710, hlam]
                                  · linarith only [h33187, h47710, hlam]
                                · linarith only [h47709, hlam, p47701_0]
                            · have p47701_0 := h47701c.1
                              have p47701_1 := h47701c.2.1
                              have p47701_2 := h47701c.2.2.1
                              have p47701_3 := h47701c.2.2.2
                              linarith only [hlam, p47701_0]
                            · have p47701_0 := h47701c.1
                              have p47701_1 := h47701c.2.1
                              have p47701_2 := h47701c.2.2.1
                              have p47701_3 := h47701c.2.2.2
                              linarith only [h0, h41027, h47681, hc01, hc12, hlam, hphi, p47701_1]
                            · have p47701_0 := h47701c.1
                              have p47701_1 := h47701c.2.1
                              have p47701_2 := h47701c.2.2.1
                              have p47701_3 := h47701c.2.2.2
                              linarith only [h36828, hc01, hc12, hlam, hphi, p47701_1]
                            · have p47701_0 := h47701c.1
                              have p47701_1 := h47701c.2.1
                              have p47701_2 := h47701c.2.2.1
                              have p47701_3 := h47701c.2.2.2
                              linarith only [h0, h46639, h47683, hc01, hc12, hlam, hphi, p47701_1]
                            · have p47701_0 := h47701c.1
                              have p47701_1 := h47701c.2.1
                              have p47701_2 := h47701c.2.2.1
                              have p47701_3 := h47701c.2.2.2
                              linarith only [h47692, h47700, hc01, hc34, hlam, hphi, ht12, ht23, p47701_1]
                            · have p47701_0 := h47701c.1
                              have p47701_1 := h47701c.2.1
                              have p47701_2 := h47701c.2.2.1
                              have p47701_3 := h47701c.2.2.2
                              linarith only [h47681, hlam, p47701_0]
                            · have p47701_0 := h47701c.1
                              have p47701_1 := h47701c.2.1
                              have p47701_2 := h47701c.2.2.1
                              have p47701_3 := h47701c.2.2.2
                              linarith only [hlam, p47701_0]
                            · have p47701_0 := h47701c.1
                              have p47701_1 := h47701c.2.1
                              have p47701_2 := h47701c.2.2.1
                              have p47701_3 := h47701c.2.2.2
                              linarith only [h47684, hlam, p47701_0]
                            · have p47701_0 := h47701c.1
                              have p47701_1 := h47701c.2.1
                              have p47701_2 := h47701c.2.2.1
                              have p47701_3 := h47701c.2.2.2
                              linarith only [h47692, hlam, p47701_1]
                            · have p47701_0 := h47701c.1
                              have p47701_1 := h47701c.2.1
                              have p47701_2 := h47701c.2.2.1
                              have p47701_3 := h47701c.2.2.2
                              rcases p47701_3 (m.d 0 1) (by simp) with h47723 | h47723
                              · linarith only [h47723, hlam, p47701_0]
                              · rcases p47701_3 (m.d 1 2) (by simp) with h47725 | h47725
                                · rcases p47701_3 (m.d 1 3) (by simp) with h47726 | h47726
                                  · linarith only [h47684, h47726, hlam]
                                  · linarith only [h33187, h47726, hlam]
                                · linarith only [h0, h47725, hlam]
                            · have p47701_0 := h47701c.1
                              have p47701_1 := h47701c.2.1
                              have p47701_2 := h47701c.2.2.1
                              have p47701_3 := h47701c.2.2.2
                              linarith only [h47682, hlam, p47701_0]
                            · have p47701_0 := h47701c.1
                              have p47701_1 := h47701c.2.1
                              have p47701_2 := h47701c.2.2.1
                              have p47701_3 := h47701c.2.2.2
                              linarith only [h0, h41027, h47681, hc01, hc14, hlam, hphi, p47701_1]
                            · have p47701_0 := h47701c.1
                              have p47701_1 := h47701c.2.1
                              have p47701_2 := h47701c.2.2.1
                              have p47701_3 := h47701c.2.2.2
                              linarith only [hlam, p47701_0]
                            · have p47701_0 := h47701c.1
                              have p47701_1 := h47701c.2.1
                              have p47701_2 := h47701c.2.2.1
                              have p47701_3 := h47701c.2.2.2
                              linarith only [h0, h41027, h47681, h47684, h47692, hc01, hc34, hlam, hphi, ht12, ht23, p47701_1]
                            · have p47701_0 := h47701c.1
                              have p47701_1 := h47701c.2.1
                              have p47701_2 := h47701c.2.2.1
                              have p47701_3 := h47701c.2.2.2
                              rcases p47701_3 (m.d 0 1) (by simp) with h47734 | h47734
                              · linarith only [h47734, hlam, p47701_0]
                              · rcases p47701_3 (m.d 1 2) (by simp) with h47736 | h47736
                                · rcases p47701_3 (m.d 1 3) (by simp) with h47737 | h47737
                                  · linarith only [h47692, h47737, hlam]
                                  · linarith only [h33187, h47737, hlam]
                                · linarith only [h0, h47736, hlam]
                            · have p47701_0 := h47701c.1
                              have p47701_1 := h47701c.2.1
                              have p47701_2 := h47701c.2.2.1
                              have p47701_3 := h47701c.2.2.2
                              linarith only [h47683, hlam, p47701_0]
                            · have p47701_0 := h47701c.1
                              have p47701_1 := h47701c.2.1
                              have p47701_2 := h47701c.2.2.1
                              have p47701_3 := h47701c.2.2.2
                              linarith only [h0, h41027, h47681, hc01, hc15, hlam, hphi, p47701_1]
                            · have p47701_0 := h47701c.1
                              have p47701_1 := h47701c.2.1
                              have p47701_2 := h47701c.2.2.1
                              have p47701_3 := h47701c.2.2.2
                              linarith only [h47694, hlam, p47701_0]
                            · have p47701_0 := h47701c.1
                              have p47701_1 := h47701c.2.1
                              have p47701_2 := h47701c.2.2.1
                              have p47701_3 := h47701c.2.2.2
                              linarith only [hlam, p47701_0]
                          · linarith only [h36828, h47680, h47684, h47700, hlam]
                        · linarith only [h45992, h47680, h47699, hlam]
                  · linarith only [h36828, h45992, h47680, h47694, hc01, hc24, hlam, hphi, ht12]
            · linarith only [h41027, h47681, h47683, hc02, hc25, hlam, hphi]
          · linarith only [h0, h41027, h47681, h47682, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h47750 | h47750
          · linarith only [h0, h45992, h47681, h47750, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h47752 | h47752
            · linarith only [h0, h46639, h47681, h47752, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h47754 | h47754
              · rcases m.htr 1 3 5 (by decide) (by decide) with h47755 | h47755
                · rcases m.htr 1 4 5 (by decide) (by decide) with h47756 | h47756
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h47757 | h47757
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h47758 | h47758
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h47759 | h47759
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h47760 | h47760
                          · rcases h1bigk with h47761c | h47761c | h47761c | h47761c | h47761c | h47761c | h47761c | h47761c | h47761c | h47761c | h47761c | h47761c | h47761c | h47761c | h47761c | h47761c | h47761c | h47761c | h47761c | h47761c | h47761c | h47761c | h47761c | h47761c | h47761c
                            · have p47761_0 := h47761c.1
                              have p47761_1 := h47761c.2.1
                              have p47761_2 := h47761c.2.2.1
                              have p47761_3 := h47761c.2.2.2
                              linarith only [hlam, p47761_0]
                            · have p47761_0 := h47761c.1
                              have p47761_1 := h47761c.2.1
                              have p47761_2 := h47761c.2.2.1
                              have p47761_3 := h47761c.2.2.2
                              linarith only [h0, hlam, p47761_0]
                            · have p47761_0 := h47761c.1
                              have p47761_1 := h47761c.2.1
                              have p47761_2 := h47761c.2.2.1
                              have p47761_3 := h47761c.2.2.2
                              linarith only [h33187, hlam, p47761_0]
                            · have p47761_0 := h47761c.1
                              have p47761_1 := h47761c.2.1
                              have p47761_2 := h47761c.2.2.1
                              have p47761_3 := h47761c.2.2.2
                              linarith only [h36828, hlam, p47761_0]
                            · have p47761_0 := h47761c.1
                              have p47761_1 := h47761c.2.1
                              have p47761_2 := h47761c.2.2.1
                              have p47761_3 := h47761c.2.2.2
                              linarith only [h39227, hlam, p47761_0]
                            · have p47761_0 := h47761c.1
                              have p47761_1 := h47761c.2.1
                              have p47761_2 := h47761c.2.2.1
                              have p47761_3 := h47761c.2.2.2
                              linarith only [h47752, h47757, h47759, hc01, hc23, hlam, hphi, ht12, p47761_1]
                            · have p47761_0 := h47761c.1
                              have p47761_1 := h47761c.2.1
                              have p47761_2 := h47761c.2.2.1
                              have p47761_3 := h47761c.2.2.2
                              linarith only [hlam, p47761_0]
                            · have p47761_0 := h47761c.1
                              have p47761_1 := h47761c.2.1
                              have p47761_2 := h47761c.2.2.1
                              have p47761_3 := h47761c.2.2.2
                              linarith only [h47681, hlam, p47761_1]
                            · have p47761_0 := h47761c.1
                              have p47761_1 := h47761c.2.1
                              have p47761_2 := h47761c.2.2.1
                              have p47761_3 := h47761c.2.2.2
                              linarith only [h47750, hlam, p47761_1]
                            · have p47761_0 := h47761c.1
                              have p47761_1 := h47761c.2.1
                              have p47761_2 := h47761c.2.2.1
                              have p47761_3 := h47761c.2.2.2
                              linarith only [h47752, hlam, p47761_1]
                            · have p47761_0 := h47761c.1
                              have p47761_1 := h47761c.2.1
                              have p47761_2 := h47761c.2.2.1
                              have p47761_3 := h47761c.2.2.2
                              rcases p47761_3 (m.d 0 1) (by simp) with h47772 | h47772
                              · linarith only [h47772, hlam, p47761_0]
                              · rcases p47761_3 (m.d 1 2) (by simp) with h47774 | h47774
                                · linarith only [h47681, h47774, hlam]
                                · linarith only [h0, h47774, hlam]
                            · have p47761_0 := h47761c.1
                              have p47761_1 := h47761c.2.1
                              have p47761_2 := h47761c.2.2.1
                              have p47761_3 := h47761c.2.2.2
                              linarith only [h0, hc01, hc13, hlam, hphi, p47761_1]
                            · have p47761_0 := h47761c.1
                              have p47761_1 := h47761c.2.1
                              have p47761_2 := h47761c.2.2.1
                              have p47761_3 := h47761c.2.2.2
                              linarith only [hlam, p47761_0]
                            · have p47761_0 := h47761c.1
                              have p47761_1 := h47761c.2.1
                              have p47761_2 := h47761c.2.2.1
                              have p47761_3 := h47761c.2.2.2
                              linarith only [h0, h47681, h47752, h47756, hc01, hc23, hlam, hphi, ht12, p47761_1]
                            · have p47761_0 := h47761c.1
                              have p47761_1 := h47761c.2.1
                              have p47761_2 := h47761c.2.2.1
                              have p47761_3 := h47761c.2.2.2
                              linarith only [h0, h47681, h47752, hc01, hc23, hlam, hphi, ht12, p47761_1]
                            · have p47761_0 := h47761c.1
                              have p47761_1 := h47761c.2.1
                              have p47761_2 := h47761c.2.2.1
                              have p47761_3 := h47761c.2.2.2
                              rcases p47761_3 (m.d 0 1) (by simp) with h47781 | h47781
                              · linarith only [h47781, hlam, p47761_0]
                              · rcases p47761_3 (m.d 1 2) (by simp) with h47783 | h47783
                                · linarith only [h47750, h47783, hlam]
                                · linarith only [h0, h47783, hlam]
                            · have p47761_0 := h47761c.1
                              have p47761_1 := h47761c.2.1
                              have p47761_2 := h47761c.2.2.1
                              have p47761_3 := h47761c.2.2.2
                              linarith only [h0, hc01, hc14, hlam, hphi, p47761_1]
                            · have p47761_0 := h47761c.1
                              have p47761_1 := h47761c.2.1
                              have p47761_2 := h47761c.2.2.1
                              have p47761_3 := h47761c.2.2.2
                              linarith only [h47754, hlam, p47761_1]
                            · have p47761_0 := h47761c.1
                              have p47761_1 := h47761c.2.1
                              have p47761_2 := h47761c.2.2.1
                              have p47761_3 := h47761c.2.2.2
                              linarith only [hlam, p47761_0]
                            · have p47761_0 := h47761c.1
                              have p47761_1 := h47761c.2.1
                              have p47761_2 := h47761c.2.2.1
                              have p47761_3 := h47761c.2.2.2
                              linarith only [h0, h41027, h47552, h47750, h47755, h47757, hc01, hc23, hlam, hphi, ht12, p47761_1]
                            · have p47761_0 := h47761c.1
                              have p47761_1 := h47761c.2.1
                              have p47761_2 := h47761c.2.2.1
                              have p47761_3 := h47761c.2.2.2
                              rcases p47761_3 (m.d 0 1) (by simp) with h47790 | h47790
                              · linarith only [h47790, hlam, p47761_0]
                              · rcases p47761_3 (m.d 1 2) (by simp) with h47792 | h47792
                                · linarith only [h47752, h47792, hlam]
                                · linarith only [h0, h47792, hlam]
                            · have p47761_0 := h47761c.1
                              have p47761_1 := h47761c.2.1
                              have p47761_2 := h47761c.2.2.1
                              have p47761_3 := h47761c.2.2.2
                              linarith only [h0, hc01, hc15, hlam, hphi, p47761_1]
                            · have p47761_0 := h47761c.1
                              have p47761_1 := h47761c.2.1
                              have p47761_2 := h47761c.2.2.1
                              have p47761_3 := h47761c.2.2.2
                              linarith only [h47755, hlam, p47761_0]
                            · have p47761_0 := h47761c.1
                              have p47761_1 := h47761c.2.1
                              have p47761_2 := h47761c.2.2.1
                              have p47761_3 := h47761c.2.2.2
                              linarith only [h47756, hlam, p47761_0]
                            · have p47761_0 := h47761c.1
                              have p47761_1 := h47761c.2.1
                              have p47761_2 := h47761c.2.2.1
                              have p47761_3 := h47761c.2.2.2
                              linarith only [hlam, p47761_0]
                          · linarith only [h0, h36828, h41027, h46974, h47680, h47750, h47757, h47760, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h36828, h46974, h47680, h47750, h47759, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h47681, h47755, h47756, h47758, hc01, hc14, hlam, hphi]
                    · linarith only [h0, h41027, h47552, h47681, h47755, h47757, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h36828, h46974, h47680, h47754, h47756, hc01, hc13, hlam, hphi]
                · linarith only [h41027, h46974, h47754, h47755, hc02, hc35, hlam, hphi, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h47805 | h47805
                · linarith only [h0, h41027, h47552, h47754, h47805, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h47807 | h47807
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h47808 | h47808
                    · linarith only [h33187, h47754, h47808, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h47681, h47808, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h36828, h47680, h47807, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h47812 | h47812
        · rcases m.htr 1 2 4 (by decide) (by decide) with h47813 | h47813
          · rcases m.htr 1 2 5 (by decide) (by decide) with h47814 | h47814
            · rcases m.htr 1 3 4 (by decide) (by decide) with h47815 | h47815
              · rcases m.htr 1 3 5 (by decide) (by decide) with h47816 | h47816
                · rcases m.htr 1 4 5 (by decide) (by decide) with h47817 | h47817
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h47818 | h47818
                    · linarith only [h0, h41027, h46974, h47812, h47818, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h41027, h47815, h47818, hc01, hc13, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h47821 | h47821
                    · linarith only [h0, h41027, h46974, h47812, h47821, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h41027, h47815, h47817, h47821, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · linarith only [h0, h41027, h46974, h47815, h47816, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h47825 | h47825
                · linarith only [h0, h41027, h47552, h47815, h47825, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h47827 | h47827
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h47828 | h47828
                    · linarith only [h33187, h47815, h47828, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h47830 | h47830
                      · linarith only [h47812, h47825, h47830, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h47832 | h47832
                        · linarith only [h0, h41027, h46974, h47680, h47813, h47832, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h45992, h47827, h47832, hc01, hc14, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h47835 | h47835
                    · linarith only [h0, h41027, h46974, h47812, h47825, h47835, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h47837 | h47837
                      · linarith only [h0, h41027, h47552, h47812, h47837, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h47839 | h47839
                        · linarith only [h33187, h47815, h47827, h47839, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h47841 | h47841
                          · linarith only [h0, h41027, h47812, h47815, h47827, h47841, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h0, h41027, h47812, h47815, h47841, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · linarith only [h0, h41027, h47812, h47814, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h41027, h47812, h47813, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h47846 | h47846
          · linarith only [h0, h45992, h47812, h47846, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h47848 | h47848
            · linarith only [h0, h46639, h47812, h47848, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h47850 | h47850
              · rcases m.htr 1 3 5 (by decide) (by decide) with h47851 | h47851
                · rcases m.htr 1 4 5 (by decide) (by decide) with h47852 | h47852
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h47853 | h47853
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h47854 | h47854
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h47855 | h47855
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h47856 | h47856
                          · linarith only [h0, h41027, h46974, h47680, h47850, h47856, hc01, hc13, hlam, hphi]
                          · linarith only [h0, h41027, h46974, h47852, h47856, hc01, hc14, hlam, hphi]
                        · linarith only [h47846, h47852, h47855, hlam]
                      · linarith only [h47812, h47851, h47854, hlam]
                    · linarith only [h0, h41027, h47552, h47812, h47851, h47853, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h47862 | h47862
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h47863 | h47863
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h47864 | h47864
                        · linarith only [h0, h47846, h47852, h47862, h47864, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h47846, h47864, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h41027, h47851, h47863, hc01, hc13, hlam, hphi]
                    · linarith only [h0, h41027, h47552, h47812, h47851, h47862, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h0, h41027, h46974, h47850, h47851, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h47870 | h47870
                · linarith only [h0, h41027, h47552, h47850, h47870, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h47872 | h47872
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h47873 | h47873
                    · linarith only [h33187, h47850, h47873, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h47812, h47873, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h47876 | h47876
                    · linarith only [h0, h47812, h47850, h47876, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h47812, h47876, hc01, hc34, hlam, hphi, ht12, ht23]

end R2N4
