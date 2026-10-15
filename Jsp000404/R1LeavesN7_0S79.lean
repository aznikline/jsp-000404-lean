import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 13704000 in
set_option maxHeartbeats 13704000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s39_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg39227 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h41027 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h45992 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h45993 | h45993
  · rcases m.htr 0 3 4 (by decide) (by decide) with h45994 | h45994
    · rcases m.htr 0 3 5 (by decide) (by decide) with h45995 | h45995
      · rcases m.htr 0 4 5 (by decide) (by decide) with h45996 | h45996
        · rcases m.htr 1 2 3 (by decide) (by decide) with h45997 | h45997
          · rcases m.htr 1 2 4 (by decide) (by decide) with h45998 | h45998
            · rcases m.htr 1 2 5 (by decide) (by decide) with h45999 | h45999
              · rcases m.htr 1 3 4 (by decide) (by decide) with h46000 | h46000
                · rcases m.htr 1 3 5 (by decide) (by decide) with h46001 | h46001
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h46002 | h46002
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h46003 | h46003
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h46004 | h46004
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h46005 | h46005
                          · linarith only [h41027, h45992, h45997, h46005, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h41027, h45992, h45996, h45997, h46005, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h41027, h45995, h46004, hlam]
                      · linarith only [h41027, h45994, h46003, hlam]
                    · linarith only [h41027, h45992, h45996, h45997, h46002, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h41027, h45992, h45995, h45996, h45997, h46001, hlam]
                · linarith only [h41027, h45992, h45994, h45997, h46000, hlam]
              · linarith only [h41027, h45993, h45997, h45999, hlam]
            · linarith only [h39227, h41027, h45992, h45996, h45997, h45998, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h46015 | h46015
            · rcases m.htr 1 2 5 (by decide) (by decide) with h46016 | h46016
              · rcases m.htr 1 3 4 (by decide) (by decide) with h46017 | h46017
                · rcases m.htr 1 3 5 (by decide) (by decide) with h46018 | h46018
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h46019 | h46019
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h46020 | h46020
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h46021 | h46021
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h46022 | h46022
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h46023 | h46023
                            · rcases h1bigk with h46024c | h46024c | h46024c | h46024c | h46024c | h46024c | h46024c | h46024c | h46024c | h46024c | h46024c | h46024c | h46024c | h46024c | h46024c | h46024c | h46024c | h46024c | h46024c | h46024c | h46024c | h46024c | h46024c | h46024c | h46024c
                              · have p46024_0 := h46024c.1
                                have p46024_1 := h46024c.2.1
                                have p46024_2 := h46024c.2.2.1
                                have p46024_3 := h46024c.2.2.2
                                linarith only [hlam, p46024_0]
                              · have p46024_0 := h46024c.1
                                have p46024_1 := h46024c.2.1
                                have p46024_2 := h46024c.2.2.1
                                have p46024_3 := h46024c.2.2.2
                                linarith only [h0, hlam, p46024_0]
                              · have p46024_0 := h46024c.1
                                have p46024_1 := h46024c.2.1
                                have p46024_2 := h46024c.2.2.1
                                have p46024_3 := h46024c.2.2.2
                                linarith only [h33187, hlam, p46024_0]
                              · have p46024_0 := h46024c.1
                                have p46024_1 := h46024c.2.1
                                have p46024_2 := h46024c.2.2.1
                                have p46024_3 := h46024c.2.2.2
                                linarith only [h36828, hlam, p46024_0]
                              · have p46024_0 := h46024c.1
                                have p46024_1 := h46024c.2.1
                                have p46024_2 := h46024c.2.2.1
                                have p46024_3 := h46024c.2.2.2
                                linarith only [h39227, hlam, p46024_0]
                              · have p46024_0 := h46024c.1
                                have p46024_1 := h46024c.2.1
                                have p46024_2 := h46024c.2.2.1
                                have p46024_3 := h46024c.2.2.2
                                linarith only [h45997, hc01, hc23, hlam, hphi, ht12, p46024_1]
                              · have p46024_0 := h46024c.1
                                have p46024_1 := h46024c.2.1
                                have p46024_2 := h46024c.2.2.1
                                have p46024_3 := h46024c.2.2.2
                                linarith only [hlam, p46024_0]
                              · have p46024_0 := h46024c.1
                                have p46024_1 := h46024c.2.1
                                have p46024_2 := h46024c.2.2.1
                                have p46024_3 := h46024c.2.2.2
                                linarith only [h45997, hlam, p46024_1]
                              · have p46024_0 := h46024c.1
                                have p46024_1 := h46024c.2.1
                                have p46024_2 := h46024c.2.2.1
                                have p46024_3 := h46024c.2.2.2
                                linarith only [h36828, h45997, hc01, hc23, hlam, hphi, ht12, p46024_1]
                              · have p46024_0 := h46024c.1
                                have p46024_1 := h46024c.2.1
                                have p46024_2 := h46024c.2.2.1
                                have p46024_3 := h46024c.2.2.2
                                linarith only [h39227, h45997, hc01, hc23, hlam, hphi, ht12, p46024_1]
                              · have p46024_0 := h46024c.1
                                have p46024_1 := h46024c.2.1
                                have p46024_2 := h46024c.2.2.1
                                have p46024_3 := h46024c.2.2.2
                                rcases p46024_3 (m.d 0 1) (by simp) with h46035 | h46035
                                · linarith only [h46035, hlam, p46024_0]
                                · rcases p46024_3 (m.d 1 2) (by simp) with h46037 | h46037
                                  · linarith only [h45997, h46037, hlam]
                                  · linarith only [h0, h46037, hlam]
                              · have p46024_0 := h46024c.1
                                have p46024_1 := h46024c.2.1
                                have p46024_2 := h46024c.2.2.1
                                have p46024_3 := h46024c.2.2.2
                                linarith only [h0, h45992, h45997, h46020, h46023, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p46024_1]
                              · have p46024_0 := h46024c.1
                                have p46024_1 := h46024c.2.1
                                have p46024_2 := h46024c.2.2.1
                                have p46024_3 := h46024c.2.2.2
                                linarith only [hlam, p46024_0]
                              · have p46024_0 := h46024c.1
                                have p46024_1 := h46024c.2.1
                                have p46024_2 := h46024c.2.2.1
                                have p46024_3 := h46024c.2.2.2
                                linarith only [h39227, h45997, h46019, hc01, hc23, hlam, hphi, ht12, p46024_1]
                              · have p46024_0 := h46024c.1
                                have p46024_1 := h46024c.2.1
                                have p46024_2 := h46024c.2.2.1
                                have p46024_3 := h46024c.2.2.2
                                linarith only [h39227, h45997, hc01, hc23, hlam, hphi, ht12, p46024_1]
                              · have p46024_0 := h46024c.1
                                have p46024_1 := h46024c.2.1
                                have p46024_2 := h46024c.2.2.1
                                have p46024_3 := h46024c.2.2.2
                                linarith only [h45997, h46015, hc01, hc23, hlam, hphi, ht12, p46024_1]
                              · have p46024_0 := h46024c.1
                                have p46024_1 := h46024c.2.1
                                have p46024_2 := h46024c.2.2.1
                                have p46024_3 := h46024c.2.2.2
                                linarith only [h46015, hlam, p46024_0]
                              · have p46024_0 := h46024c.1
                                have p46024_1 := h46024c.2.1
                                have p46024_2 := h46024c.2.2.1
                                have p46024_3 := h46024c.2.2.2
                                linarith only [h46017, hlam, p46024_1]
                              · have p46024_0 := h46024c.1
                                have p46024_1 := h46024c.2.1
                                have p46024_2 := h46024c.2.2.1
                                have p46024_3 := h46024c.2.2.2
                                linarith only [hlam, p46024_0]
                              · have p46024_0 := h46024c.1
                                have p46024_1 := h46024c.2.1
                                have p46024_2 := h46024c.2.2.1
                                have p46024_3 := h46024c.2.2.2
                                linarith only [h39227, h45997, h46015, hc01, hc23, hlam, hphi, ht12, p46024_1]
                              · have p46024_0 := h46024c.1
                                have p46024_1 := h46024c.2.1
                                have p46024_2 := h46024c.2.2.1
                                have p46024_3 := h46024c.2.2.2
                                linarith only [h45997, h46016, hc01, hc23, hlam, hphi, ht12, p46024_1]
                              · have p46024_0 := h46024c.1
                                have p46024_1 := h46024c.2.1
                                have p46024_2 := h46024c.2.2.1
                                have p46024_3 := h46024c.2.2.2
                                linarith only [h46016, hlam, p46024_0]
                              · have p46024_0 := h46024c.1
                                have p46024_1 := h46024c.2.1
                                have p46024_2 := h46024c.2.2.1
                                have p46024_3 := h46024c.2.2.2
                                linarith only [h46018, hlam, p46024_0]
                              · have p46024_0 := h46024c.1
                                have p46024_1 := h46024c.2.1
                                have p46024_2 := h46024c.2.2.1
                                have p46024_3 := h46024c.2.2.2
                                linarith only [h46019, hlam, p46024_0]
                              · have p46024_0 := h46024c.1
                                have p46024_1 := h46024c.2.1
                                have p46024_2 := h46024c.2.2.1
                                have p46024_3 := h46024c.2.2.2
                                linarith only [hlam, p46024_0]
                            · linarith only [h0, h45992, h45997, h46022, h46023, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h46055 | h46055
                            · linarith only [h46020, h46022, h46055, hlam]
                            · rcases h1bigk with h46057c | h46057c | h46057c | h46057c | h46057c | h46057c | h46057c | h46057c | h46057c | h46057c | h46057c | h46057c | h46057c | h46057c | h46057c | h46057c | h46057c | h46057c | h46057c | h46057c | h46057c | h46057c | h46057c | h46057c | h46057c
                              · have p46057_0 := h46057c.1
                                have p46057_1 := h46057c.2.1
                                have p46057_2 := h46057c.2.2.1
                                have p46057_3 := h46057c.2.2.2
                                linarith only [hlam, p46057_0]
                              · have p46057_0 := h46057c.1
                                have p46057_1 := h46057c.2.1
                                have p46057_2 := h46057c.2.2.1
                                have p46057_3 := h46057c.2.2.2
                                linarith only [h0, hlam, p46057_0]
                              · have p46057_0 := h46057c.1
                                have p46057_1 := h46057c.2.1
                                have p46057_2 := h46057c.2.2.1
                                have p46057_3 := h46057c.2.2.2
                                linarith only [h33187, hlam, p46057_0]
                              · have p46057_0 := h46057c.1
                                have p46057_1 := h46057c.2.1
                                have p46057_2 := h46057c.2.2.1
                                have p46057_3 := h46057c.2.2.2
                                linarith only [h36828, hlam, p46057_0]
                              · have p46057_0 := h46057c.1
                                have p46057_1 := h46057c.2.1
                                have p46057_2 := h46057c.2.2.1
                                have p46057_3 := h46057c.2.2.2
                                linarith only [h39227, hlam, p46057_0]
                              · have p46057_0 := h46057c.1
                                have p46057_1 := h46057c.2.1
                                have p46057_2 := h46057c.2.2.1
                                have p46057_3 := h46057c.2.2.2
                                linarith only [h45997, hc01, hc23, hlam, hphi, ht12, p46057_1]
                              · have p46057_0 := h46057c.1
                                have p46057_1 := h46057c.2.1
                                have p46057_2 := h46057c.2.2.1
                                have p46057_3 := h46057c.2.2.2
                                linarith only [hlam, p46057_0]
                              · have p46057_0 := h46057c.1
                                have p46057_1 := h46057c.2.1
                                have p46057_2 := h46057c.2.2.1
                                have p46057_3 := h46057c.2.2.2
                                linarith only [h45997, hlam, p46057_1]
                              · have p46057_0 := h46057c.1
                                have p46057_1 := h46057c.2.1
                                have p46057_2 := h46057c.2.2.1
                                have p46057_3 := h46057c.2.2.2
                                linarith only [h36828, h45997, hc01, hc23, hlam, hphi, ht12, p46057_1]
                              · have p46057_0 := h46057c.1
                                have p46057_1 := h46057c.2.1
                                have p46057_2 := h46057c.2.2.1
                                have p46057_3 := h46057c.2.2.2
                                linarith only [h39227, h45997, hc01, hc23, hlam, hphi, ht12, p46057_1]
                              · have p46057_0 := h46057c.1
                                have p46057_1 := h46057c.2.1
                                have p46057_2 := h46057c.2.2.1
                                have p46057_3 := h46057c.2.2.2
                                rcases p46057_3 (m.d 0 1) (by simp) with h46068 | h46068
                                · linarith only [h46068, hlam, p46057_0]
                                · rcases p46057_3 (m.d 1 2) (by simp) with h46070 | h46070
                                  · linarith only [h45997, h46070, hlam]
                                  · linarith only [h0, h46070, hlam]
                              · have p46057_0 := h46057c.1
                                have p46057_1 := h46057c.2.1
                                have p46057_2 := h46057c.2.2.1
                                have p46057_3 := h46057c.2.2.2
                                linarith only [h0, h45992, h45996, h45997, h46022, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p46057_1]
                              · have p46057_0 := h46057c.1
                                have p46057_1 := h46057c.2.1
                                have p46057_2 := h46057c.2.2.1
                                have p46057_3 := h46057c.2.2.2
                                linarith only [hlam, p46057_0]
                              · have p46057_0 := h46057c.1
                                have p46057_1 := h46057c.2.1
                                have p46057_2 := h46057c.2.2.1
                                have p46057_3 := h46057c.2.2.2
                                linarith only [h36828, h45996, h45997, h46020, h46022, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p46057_1]
                              · have p46057_0 := h46057c.1
                                have p46057_1 := h46057c.2.1
                                have p46057_2 := h46057c.2.2.1
                                have p46057_3 := h46057c.2.2.2
                                linarith only [h39227, h45997, hc01, hc23, hlam, hphi, ht12, p46057_1]
                              · have p46057_0 := h46057c.1
                                have p46057_1 := h46057c.2.1
                                have p46057_2 := h46057c.2.2.1
                                have p46057_3 := h46057c.2.2.2
                                linarith only [h45997, h46015, hc01, hc23, hlam, hphi, ht12, p46057_1]
                              · have p46057_0 := h46057c.1
                                have p46057_1 := h46057c.2.1
                                have p46057_2 := h46057c.2.2.1
                                have p46057_3 := h46057c.2.2.2
                                linarith only [h46015, hlam, p46057_0]
                              · have p46057_0 := h46057c.1
                                have p46057_1 := h46057c.2.1
                                have p46057_2 := h46057c.2.2.1
                                have p46057_3 := h46057c.2.2.2
                                linarith only [h46017, hlam, p46057_1]
                              · have p46057_0 := h46057c.1
                                have p46057_1 := h46057c.2.1
                                have p46057_2 := h46057c.2.2.1
                                have p46057_3 := h46057c.2.2.2
                                linarith only [hlam, p46057_0]
                              · have p46057_0 := h46057c.1
                                have p46057_1 := h46057c.2.1
                                have p46057_2 := h46057c.2.2.1
                                have p46057_3 := h46057c.2.2.2
                                linarith only [h39227, h45997, h46015, hc01, hc23, hlam, hphi, ht12, p46057_1]
                              · have p46057_0 := h46057c.1
                                have p46057_1 := h46057c.2.1
                                have p46057_2 := h46057c.2.2.1
                                have p46057_3 := h46057c.2.2.2
                                linarith only [h45997, h46016, hc01, hc23, hlam, hphi, ht12, p46057_1]
                              · have p46057_0 := h46057c.1
                                have p46057_1 := h46057c.2.1
                                have p46057_2 := h46057c.2.2.1
                                have p46057_3 := h46057c.2.2.2
                                linarith only [h46016, hlam, p46057_0]
                              · have p46057_0 := h46057c.1
                                have p46057_1 := h46057c.2.1
                                have p46057_2 := h46057c.2.2.1
                                have p46057_3 := h46057c.2.2.2
                                linarith only [h46018, hlam, p46057_0]
                              · have p46057_0 := h46057c.1
                                have p46057_1 := h46057c.2.1
                                have p46057_2 := h46057c.2.2.1
                                have p46057_3 := h46057c.2.2.2
                                linarith only [h46019, hlam, p46057_0]
                              · have p46057_0 := h46057c.1
                                have p46057_1 := h46057c.2.1
                                have p46057_2 := h46057c.2.2.1
                                have p46057_3 := h46057c.2.2.2
                                linarith only [hlam, p46057_0]
                        · linarith only [h0, h45997, h46021, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h45997, h46020, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h36828, h45996, h46019, hlam]
                  · linarith only [h33187, h36828, h45995, h45996, h45997, h46015, h46018, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h33187, h45994, h46017, hlam]
              · linarith only [h0, h33187, h41027, h45993, h46016, hc01, hc13, hlam, hphi]
            · linarith only [h0, h45992, h46015, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h46094 | h46094
          · rcases m.htr 1 2 4 (by decide) (by decide) with h46095 | h46095
            · rcases m.htr 1 2 5 (by decide) (by decide) with h46096 | h46096
              · rcases m.htr 1 3 4 (by decide) (by decide) with h46097 | h46097
                · rcases m.htr 1 3 5 (by decide) (by decide) with h46098 | h46098
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h46099 | h46099
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h46100 | h46100
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h46101 | h46101
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h46102 | h46102
                          · linarith only [h41027, h45992, h45996, h46094, h46102, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h46104 | h46104
                            · linarith only [h36828, h41027, h45994, h45996, h46094, h46104, hc01, hc12, hlam, hphi]
                            · rcases h1bigk with h46106c | h46106c | h46106c | h46106c | h46106c | h46106c | h46106c | h46106c | h46106c | h46106c | h46106c | h46106c | h46106c | h46106c | h46106c | h46106c | h46106c | h46106c | h46106c | h46106c | h46106c | h46106c | h46106c | h46106c | h46106c
                              · have p46106_0 := h46106c.1
                                have p46106_1 := h46106c.2.1
                                have p46106_2 := h46106c.2.2.1
                                have p46106_3 := h46106c.2.2.2
                                linarith only [hlam, p46106_0]
                              · have p46106_0 := h46106c.1
                                have p46106_1 := h46106c.2.1
                                have p46106_2 := h46106c.2.2.1
                                have p46106_3 := h46106c.2.2.2
                                linarith only [h0, hlam, p46106_0]
                              · have p46106_0 := h46106c.1
                                have p46106_1 := h46106c.2.1
                                have p46106_2 := h46106c.2.2.1
                                have p46106_3 := h46106c.2.2.2
                                linarith only [h33187, hlam, p46106_0]
                              · have p46106_0 := h46106c.1
                                have p46106_1 := h46106c.2.1
                                have p46106_2 := h46106c.2.2.1
                                have p46106_3 := h46106c.2.2.2
                                linarith only [h36828, hlam, p46106_0]
                              · have p46106_0 := h46106c.1
                                have p46106_1 := h46106c.2.1
                                have p46106_2 := h46106c.2.2.1
                                have p46106_3 := h46106c.2.2.2
                                linarith only [h39227, hlam, p46106_0]
                              · have p46106_0 := h46106c.1
                                have p46106_1 := h46106c.2.1
                                have p46106_2 := h46106c.2.2.1
                                have p46106_3 := h46106c.2.2.2
                                rcases p46106_3 (m.d 0 1) (by simp) with h46112 | h46112
                                · linarith only [h46112, hlam, p46106_0]
                                · rcases p46106_3 (m.d 1 2) (by simp) with h46114 | h46114
                                  · rcases p46106_3 (m.d 1 3) (by simp) with h46115 | h46115
                                    · linarith only [h46094, h46115, hlam]
                                    · linarith only [h33187, h46115, hlam]
                                  · linarith only [h46114, hlam, p46106_0]
                              · have p46106_0 := h46106c.1
                                have p46106_1 := h46106c.2.1
                                have p46106_2 := h46106c.2.2.1
                                have p46106_3 := h46106c.2.2.2
                                linarith only [hlam, p46106_0]
                              · have p46106_0 := h46106c.1
                                have p46106_1 := h46106c.2.1
                                have p46106_2 := h46106c.2.2.1
                                have p46106_3 := h46106c.2.2.2
                                linarith only [h33187, hc01, hc12, hlam, hphi, p46106_1]
                              · have p46106_0 := h46106c.1
                                have p46106_1 := h46106c.2.1
                                have p46106_2 := h46106c.2.2.1
                                have p46106_3 := h46106c.2.2.2
                                linarith only [h36828, h45996, h46099, hc01, hc12, hlam, hphi, p46106_1]
                              · have p46106_0 := h46106c.1
                                have p46106_1 := h46106c.2.1
                                have p46106_2 := h46106c.2.2.1
                                have p46106_3 := h46106c.2.2.2
                                linarith only [h36828, h45996, h46099, hc01, hc12, hlam, hphi, p46106_1]
                              · have p46106_0 := h46106c.1
                                have p46106_1 := h46106c.2.1
                                have p46106_2 := h46106c.2.2.1
                                have p46106_3 := h46106c.2.2.2
                                rcases p46106_3 (m.d 0 1) (by simp) with h46123 | h46123
                                · linarith only [h46123, hlam, p46106_0]
                                · rcases p46106_3 (m.d 1 2) (by simp) with h46125 | h46125
                                  · rcases p46106_3 (m.d 1 3) (by simp) with h46126 | h46126
                                    · rcases p46106_3 (m.d 1 4) (by simp) with h46127 | h46127
                                      · linarith only [h46097, h46127, hlam]
                                      · linarith only [h36828, h46127, hlam]
                                    · linarith only [h46126, hlam, p46106_0]
                                  · linarith only [h0, h46125, hlam]
                              · have p46106_0 := h46106c.1
                                have p46106_1 := h46106c.2.1
                                have p46106_2 := h46106c.2.2.1
                                have p46106_3 := h46106c.2.2.2
                                linarith only [h46094, hlam, p46106_0]
                              · have p46106_0 := h46106c.1
                                have p46106_1 := h46106c.2.1
                                have p46106_2 := h46106c.2.2.1
                                have p46106_3 := h46106c.2.2.2
                                linarith only [hlam, p46106_0]
                              · have p46106_0 := h46106c.1
                                have p46106_1 := h46106c.2.1
                                have p46106_2 := h46106c.2.2.1
                                have p46106_3 := h46106c.2.2.2
                                linarith only [h36828, h45996, h46099, hc01, hc13, hlam, hphi, p46106_1]
                              · have p46106_0 := h46106c.1
                                have p46106_1 := h46106c.2.1
                                have p46106_2 := h46106c.2.2.1
                                have p46106_3 := h46106c.2.2.2
                                linarith only [h36828, h45996, h46094, h46099, hc01, hc12, hlam, hphi, p46106_1]
                              · have p46106_0 := h46106c.1
                                have p46106_1 := h46106c.2.1
                                have p46106_2 := h46106c.2.2.1
                                have p46106_3 := h46106c.2.2.2
                                rcases p46106_3 (m.d 0 1) (by simp) with h46136 | h46136
                                · linarith only [h46136, hlam, p46106_0]
                                · rcases p46106_3 (m.d 1 2) (by simp) with h46138 | h46138
                                  · rcases p46106_3 (m.d 1 3) (by simp) with h46139 | h46139
                                    · rcases p46106_3 (m.d 1 4) (by simp) with h46140 | h46140
                                      · rcases p46106_3 (m.d 1 5) (by simp) with h46141 | h46141
                                        · linarith only [h46099, h46141, hlam]
                                        · linarith only [h39227, h46141, hlam]
                                      · linarith only [h46140, hlam, p46106_0]
                                    · linarith only [h33187, h46139, hlam]
                                  · linarith only [h0, h46138, hlam]
                              · have p46106_0 := h46106c.1
                                have p46106_1 := h46106c.2.1
                                have p46106_2 := h46106c.2.2.1
                                have p46106_3 := h46106c.2.2.2
                                linarith only [h46095, hlam, p46106_0]
                              · have p46106_0 := h46106c.1
                                have p46106_1 := h46106c.2.1
                                have p46106_2 := h46106c.2.2.1
                                have p46106_3 := h46106c.2.2.2
                                linarith only [h46097, hlam, p46106_1]
                              · have p46106_0 := h46106c.1
                                have p46106_1 := h46106c.2.1
                                have p46106_2 := h46106c.2.2.1
                                have p46106_3 := h46106c.2.2.2
                                linarith only [hlam, p46106_0]
                              · have p46106_0 := h46106c.1
                                have p46106_1 := h46106c.2.1
                                have p46106_2 := h46106c.2.2.1
                                have p46106_3 := h46106c.2.2.2
                                linarith only [h36828, h45996, h46099, hc01, hc14, hlam, hphi, p46106_1]
                              · have p46106_0 := h46106c.1
                                have p46106_1 := h46106c.2.1
                                have p46106_2 := h46106c.2.2.1
                                have p46106_3 := h46106c.2.2.2
                                rcases p46106_3 (m.d 0 1) (by simp) with h46151 | h46151
                                · linarith only [h46151, hlam, p46106_0]
                                · rcases p46106_3 (m.d 1 2) (by simp) with h46153 | h46153
                                  · rcases p46106_3 (m.d 1 3) (by simp) with h46154 | h46154
                                    · rcases p46106_3 (m.d 1 4) (by simp) with h46155 | h46155
                                      · rcases p46106_3 (m.d 1 5) (by simp) with h46156 | h46156
                                        · rcases h1emax with h46157 | h46157 | h46157 | h46157 | h46157
                                          · rcases h2bigk with h46158c | h46158c | h46158c | h46158c | h46158c | h46158c | h46158c | h46158c | h46158c | h46158c | h46158c | h46158c | h46158c | h46158c | h46158c | h46158c | h46158c | h46158c | h46158c | h46158c | h46158c | h46158c | h46158c | h46158c | h46158c
                                            · have p46158_0 := h46158c.1
                                              have p46158_1 := h46158c.2.1
                                              have p46158_2 := h46158c.2.2.1
                                              have p46158_3 := h46158c.2.2.2
                                              linarith only [hlam, p46158_0]
                                            · have p46158_0 := h46158c.1
                                              have p46158_1 := h46158c.2.1
                                              have p46158_2 := h46158c.2.2.1
                                              have p46158_3 := h46158c.2.2.2
                                              linarith only [h0, hlam, p46158_0]
                                            · have p46158_0 := h46158c.1
                                              have p46158_1 := h46158c.2.1
                                              have p46158_2 := h46158c.2.2.1
                                              have p46158_3 := h46158c.2.2.2
                                              linarith only [h41027, hlam, p46158_0]
                                            · have p46158_0 := h46158c.1
                                              have p46158_1 := h46158c.2.1
                                              have p46158_2 := h46158c.2.2.1
                                              have p46158_3 := h46158c.2.2.2
                                              linarith only [h41027, h46094, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p46158_1]
                                            · have p46158_0 := h46158c.1
                                              have p46158_1 := h46158c.2.1
                                              have p46158_2 := h46158c.2.2.1
                                              have p46158_3 := h46158c.2.2.2
                                              linarith only [h41027, h46094, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p46158_1]
                                            · have p46158_0 := h46158c.1
                                              have p46158_1 := h46158c.2.1
                                              have p46158_2 := h46158c.2.2.1
                                              have p46158_3 := h46158c.2.2.2
                                              rcases p46158_3 (m.d 0 2) (by simp) with h46164 | h46164
                                              · linarith only [h0, h46164, hlam]
                                              · rcases p46158_3 (m.d 1 2) (by simp) with h46166 | h46166
                                                · rcases p46158_3 (m.d 2 3) (by simp) with h46167 | h46167
                                                  · linarith only [h46094, h46167, hlam]
                                                  · linarith only [h41027, h46167, hlam]
                                                · linarith only [h0, h46166, hlam]
                                            · have p46158_0 := h46158c.1
                                              have p46158_1 := h46158c.2.1
                                              have p46158_2 := h46158c.2.2.1
                                              have p46158_3 := h46158c.2.2.2
                                              linarith only [hlam, p46158_0]
                                            · have p46158_0 := h46158c.1
                                              have p46158_1 := h46158c.2.1
                                              have p46158_2 := h46158c.2.2.1
                                              have p46158_3 := h46158c.2.2.2
                                              linarith only [h0, h41027, hc01, hc12, hlam, hphi, p46158_1]
                                            · have p46158_0 := h46158c.1
                                              have p46158_1 := h46158c.2.1
                                              have p46158_2 := h46158c.2.2.1
                                              have p46158_3 := h46158c.2.2.2
                                              linarith only [h41027, h45993, h46094, h46102, hlam, p46158_2]
                                            · have p46158_0 := h46158c.1
                                              have p46158_1 := h46158c.2.1
                                              have p46158_2 := h46158c.2.2.1
                                              have p46158_3 := h46158c.2.2.2
                                              linarith only [h41027, h45993, h46094, hlam, p46158_2]
                                            · have p46158_0 := h46158c.1
                                              have p46158_1 := h46158c.2.1
                                              have p46158_2 := h46158c.2.2.1
                                              have p46158_3 := h46158c.2.2.2
                                              linarith only [h45993, h46094, h46100, h46102, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p46158_1]
                                            · have p46158_0 := h46158c.1
                                              have p46158_1 := h46158c.2.1
                                              have p46158_2 := h46158c.2.2.1
                                              have p46158_3 := h46158c.2.2.2
                                              linarith only [h46094, hlam, p46158_0]
                                            · have p46158_0 := h46158c.1
                                              have p46158_1 := h46158c.2.1
                                              have p46158_2 := h46158c.2.2.1
                                              have p46158_3 := h46158c.2.2.2
                                              linarith only [hlam, p46158_0]
                                            · have p46158_0 := h46158c.1
                                              have p46158_1 := h46158c.2.1
                                              have p46158_2 := h46158c.2.2.1
                                              have p46158_3 := h46158c.2.2.2
                                              rcases p46158_3 (m.d 0 2) (by simp) with h46178 | h46178
                                              · linarith only [h41027, h46178, hlam]
                                              · linarith only [h45992, h46178, hlam]
                                            · have p46158_0 := h46158c.1
                                              have p46158_1 := h46158c.2.1
                                              have p46158_2 := h46158c.2.2.1
                                              have p46158_3 := h46158c.2.2.2
                                              rcases p46158_3 (m.d 0 2) (by simp) with h46181 | h46181
                                              · linarith only [h41027, h46181, hlam]
                                              · linarith only [h45993, h46181, hlam]
                                            · have p46158_0 := h46158c.1
                                              have p46158_1 := h46158c.2.1
                                              have p46158_2 := h46158c.2.2.1
                                              have p46158_3 := h46158c.2.2.2
                                              linarith only [h45992, hlam, p46158_0]
                                            · have p46158_0 := h46158c.1
                                              have p46158_1 := h46158c.2.1
                                              have p46158_2 := h46158c.2.2.1
                                              have p46158_3 := h46158c.2.2.2
                                              linarith only [h46095, hlam, p46158_0]
                                            · have p46158_0 := h46158c.1
                                              have p46158_1 := h46158c.2.1
                                              have p46158_2 := h46158c.2.2.1
                                              have p46158_3 := h46158c.2.2.2
                                              linarith only [h46100, hlam, p46158_0]
                                            · have p46158_0 := h46158c.1
                                              have p46158_1 := h46158c.2.1
                                              have p46158_2 := h46158c.2.2.1
                                              have p46158_3 := h46158c.2.2.2
                                              linarith only [hlam, p46158_0]
                                            · have p46158_0 := h46158c.1
                                              have p46158_1 := h46158c.2.1
                                              have p46158_2 := h46158c.2.2.1
                                              have p46158_3 := h46158c.2.2.2
                                              linarith only [h46102, hlam, p46158_0]
                                            · have p46158_0 := h46158c.1
                                              have p46158_1 := h46158c.2.1
                                              have p46158_2 := h46158c.2.2.1
                                              have p46158_3 := h46158c.2.2.2
                                              linarith only [h45993, hlam, p46158_0]
                                            · have p46158_0 := h46158c.1
                                              have p46158_1 := h46158c.2.1
                                              have p46158_2 := h46158c.2.2.1
                                              have p46158_3 := h46158c.2.2.2
                                              linarith only [h46096, hlam, p46158_0]
                                            · have p46158_0 := h46158c.1
                                              have p46158_1 := h46158c.2.1
                                              have p46158_2 := h46158c.2.2.1
                                              have p46158_3 := h46158c.2.2.2
                                              linarith only [h46101, hlam, p46158_0]
                                            · have p46158_0 := h46158c.1
                                              have p46158_1 := h46158c.2.1
                                              have p46158_2 := h46158c.2.2.1
                                              have p46158_3 := h46158c.2.2.2
                                              linarith only [h41027, h45993, h46094, h46100, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p46158_1]
                                            · have p46158_0 := h46158c.1
                                              have p46158_1 := h46158c.2.1
                                              have p46158_2 := h46158c.2.2.1
                                              have p46158_3 := h46158c.2.2.2
                                              linarith only [hlam, p46158_0]
                                          · linarith only [h41027, h46094, h46157, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                          · linarith only [h33187, h46157, hc01, hlam]
                                          · linarith only [h36828, h45996, h46099, h46157, hc01, hlam]
                                          · linarith only [h46157, hc01, hlam, p46106_1]
                                        · linarith only [h46156, hlam, p46106_0]
                                      · linarith only [h36828, h46155, hlam]
                                    · linarith only [h33187, h46154, hlam]
                                  · linarith only [h0, h46153, hlam]
                              · have p46106_0 := h46106c.1
                                have p46106_1 := h46106c.2.1
                                have p46106_2 := h46106c.2.2.1
                                have p46106_3 := h46106c.2.2.2
                                linarith only [h46096, hlam, p46106_0]
                              · have p46106_0 := h46106c.1
                                have p46106_1 := h46106c.2.1
                                have p46106_2 := h46106c.2.2.1
                                have p46106_3 := h46106c.2.2.2
                                linarith only [h46098, hlam, p46106_0]
                              · have p46106_0 := h46106c.1
                                have p46106_1 := h46106c.2.1
                                have p46106_2 := h46106c.2.2.1
                                have p46106_3 := h46106c.2.2.2
                                linarith only [h46099, hlam, p46106_0]
                              · have p46106_0 := h46106c.1
                                have p46106_1 := h46106c.2.1
                                have p46106_2 := h46106c.2.2.1
                                have p46106_3 := h46106c.2.2.2
                                linarith only [hlam, p46106_0]
                        · linarith only [h41027, h45993, h45995, h46101, hc03, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h41027, h45994, h46100, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h46208 | h46208
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h46209 | h46209
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h46210 | h46210
                          · linarith only [h41027, h45992, h46094, h46099, h46210, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h46212 | h46212
                            · linarith only [h41027, h45993, h46094, h46099, h46208, h46210, h46212, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases h1bigk with h46214c | h46214c | h46214c | h46214c | h46214c | h46214c | h46214c | h46214c | h46214c | h46214c | h46214c | h46214c | h46214c | h46214c | h46214c | h46214c | h46214c | h46214c | h46214c | h46214c | h46214c | h46214c | h46214c | h46214c | h46214c
                              · have p46214_0 := h46214c.1
                                have p46214_1 := h46214c.2.1
                                have p46214_2 := h46214c.2.2.1
                                have p46214_3 := h46214c.2.2.2
                                linarith only [hlam, p46214_0]
                              · have p46214_0 := h46214c.1
                                have p46214_1 := h46214c.2.1
                                have p46214_2 := h46214c.2.2.1
                                have p46214_3 := h46214c.2.2.2
                                linarith only [h0, hlam, p46214_0]
                              · have p46214_0 := h46214c.1
                                have p46214_1 := h46214c.2.1
                                have p46214_2 := h46214c.2.2.1
                                have p46214_3 := h46214c.2.2.2
                                linarith only [h33187, hlam, p46214_0]
                              · have p46214_0 := h46214c.1
                                have p46214_1 := h46214c.2.1
                                have p46214_2 := h46214c.2.2.1
                                have p46214_3 := h46214c.2.2.2
                                linarith only [h36828, hlam, p46214_0]
                              · have p46214_0 := h46214c.1
                                have p46214_1 := h46214c.2.1
                                have p46214_2 := h46214c.2.2.1
                                have p46214_3 := h46214c.2.2.2
                                linarith only [h39227, hlam, p46214_0]
                              · have p46214_0 := h46214c.1
                                have p46214_1 := h46214c.2.1
                                have p46214_2 := h46214c.2.2.1
                                have p46214_3 := h46214c.2.2.2
                                rcases p46214_3 (m.d 0 1) (by simp) with h46220 | h46220
                                · linarith only [h46220, hlam, p46214_0]
                                · rcases p46214_3 (m.d 1 2) (by simp) with h46222 | h46222
                                  · rcases p46214_3 (m.d 1 3) (by simp) with h46223 | h46223
                                    · linarith only [h46094, h46223, hlam]
                                    · linarith only [h33187, h46223, hlam]
                                  · linarith only [h46222, hlam, p46214_0]
                              · have p46214_0 := h46214c.1
                                have p46214_1 := h46214c.2.1
                                have p46214_2 := h46214c.2.2.1
                                have p46214_3 := h46214c.2.2.2
                                linarith only [hlam, p46214_0]
                              · have p46214_0 := h46214c.1
                                have p46214_1 := h46214c.2.1
                                have p46214_2 := h46214c.2.2.1
                                have p46214_3 := h46214c.2.2.2
                                linarith only [h33187, hc01, hc12, hlam, hphi, p46214_1]
                              · have p46214_0 := h46214c.1
                                have p46214_1 := h46214c.2.1
                                have p46214_2 := h46214c.2.2.1
                                have p46214_3 := h46214c.2.2.2
                                linarith only [h36828, hc01, hc12, hlam, hphi, p46214_1]
                              · have p46214_0 := h46214c.1
                                have p46214_1 := h46214c.2.1
                                have p46214_2 := h46214c.2.2.1
                                have p46214_3 := h46214c.2.2.2
                                linarith only [h36828, h46099, hc01, hc12, hlam, hphi, p46214_1]
                              · have p46214_0 := h46214c.1
                                have p46214_1 := h46214c.2.1
                                have p46214_2 := h46214c.2.2.1
                                have p46214_3 := h46214c.2.2.2
                                rcases p46214_3 (m.d 0 1) (by simp) with h46231 | h46231
                                · linarith only [h46231, hlam, p46214_0]
                                · rcases p46214_3 (m.d 1 2) (by simp) with h46233 | h46233
                                  · rcases p46214_3 (m.d 1 3) (by simp) with h46234 | h46234
                                    · rcases p46214_3 (m.d 1 4) (by simp) with h46235 | h46235
                                      · linarith only [h46097, h46235, hlam]
                                      · linarith only [h36828, h46235, hlam]
                                    · linarith only [h46234, hlam, p46214_0]
                                  · linarith only [h0, h46233, hlam]
                              · have p46214_0 := h46214c.1
                                have p46214_1 := h46214c.2.1
                                have p46214_2 := h46214c.2.2.1
                                have p46214_3 := h46214c.2.2.2
                                linarith only [h46094, hlam, p46214_0]
                              · have p46214_0 := h46214c.1
                                have p46214_1 := h46214c.2.1
                                have p46214_2 := h46214c.2.2.1
                                have p46214_3 := h46214c.2.2.2
                                linarith only [hlam, p46214_0]
                              · have p46214_0 := h46214c.1
                                have p46214_1 := h46214c.2.1
                                have p46214_2 := h46214c.2.2.1
                                have p46214_3 := h46214c.2.2.2
                                linarith only [h36828, hc01, hc13, hlam, hphi, p46214_1]
                              · have p46214_0 := h46214c.1
                                have p46214_1 := h46214c.2.1
                                have p46214_2 := h46214c.2.2.1
                                have p46214_3 := h46214c.2.2.2
                                linarith only [h36828, h46094, h46099, hc01, hc12, hlam, hphi, p46214_1]
                              · have p46214_0 := h46214c.1
                                have p46214_1 := h46214c.2.1
                                have p46214_2 := h46214c.2.2.1
                                have p46214_3 := h46214c.2.2.2
                                linarith only [h46099, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p46214_1]
                              · have p46214_0 := h46214c.1
                                have p46214_1 := h46214c.2.1
                                have p46214_2 := h46214c.2.2.1
                                have p46214_3 := h46214c.2.2.2
                                linarith only [h46095, hlam, p46214_0]
                              · have p46214_0 := h46214c.1
                                have p46214_1 := h46214c.2.1
                                have p46214_2 := h46214c.2.2.1
                                have p46214_3 := h46214c.2.2.2
                                linarith only [h46097, hlam, p46214_1]
                              · have p46214_0 := h46214c.1
                                have p46214_1 := h46214c.2.1
                                have p46214_2 := h46214c.2.2.1
                                have p46214_3 := h46214c.2.2.2
                                linarith only [hlam, p46214_0]
                              · have p46214_0 := h46214c.1
                                have p46214_1 := h46214c.2.1
                                have p46214_2 := h46214c.2.2.1
                                have p46214_3 := h46214c.2.2.2
                                linarith only [h46099, hlam, p46214_1]
                              · have p46214_0 := h46214c.1
                                have p46214_1 := h46214c.2.1
                                have p46214_2 := h46214c.2.2.1
                                have p46214_3 := h46214c.2.2.2
                                rcases p46214_3 (m.d 0 1) (by simp) with h46249 | h46249
                                · linarith only [h46249, hlam, p46214_0]
                                · rcases p46214_3 (m.d 1 2) (by simp) with h46251 | h46251
                                  · rcases p46214_3 (m.d 1 3) (by simp) with h46252 | h46252
                                    · rcases p46214_3 (m.d 1 4) (by simp) with h46253 | h46253
                                      · linarith only [h46099, h46253, hlam]
                                      · linarith only [h36828, h46253, hlam]
                                    · linarith only [h33187, h46252, hlam]
                                  · linarith only [h0, h46251, hlam]
                              · have p46214_0 := h46214c.1
                                have p46214_1 := h46214c.2.1
                                have p46214_2 := h46214c.2.2.1
                                have p46214_3 := h46214c.2.2.2
                                linarith only [h46096, hlam, p46214_0]
                              · have p46214_0 := h46214c.1
                                have p46214_1 := h46214c.2.1
                                have p46214_2 := h46214c.2.2.1
                                have p46214_3 := h46214c.2.2.2
                                linarith only [h46098, hlam, p46214_0]
                              · have p46214_0 := h46214c.1
                                have p46214_1 := h46214c.2.1
                                have p46214_2 := h46214c.2.2.1
                                have p46214_3 := h46214c.2.2.2
                                linarith only [h36828, hc01, hc15, hlam, hphi, p46214_1]
                              · have p46214_0 := h46214c.1
                                have p46214_1 := h46214c.2.1
                                have p46214_2 := h46214c.2.2.1
                                have p46214_3 := h46214c.2.2.2
                                linarith only [hlam, p46214_0]
                        · linarith only [h41027, h45992, h45995, h46208, h46209, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h41027, h45994, h46208, hlam]
                  · linarith only [h33187, h41027, h45993, h45995, h46098, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h41027, h45993, h45994, h46094, h46097, hc03, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h41027, h45992, h46094, h46096, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h41027, h45992, h46094, h46095, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h46268 | h46268
            · rcases m.htr 1 2 5 (by decide) (by decide) with h46269 | h46269
              · rcases m.htr 1 3 4 (by decide) (by decide) with h46270 | h46270
                · rcases m.htr 1 3 5 (by decide) (by decide) with h46271 | h46271
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h46272 | h46272
                    · linarith only [h36828, h45996, h46094, h46268, h46272, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h46274 | h46274
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h46275 | h46275
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h46276 | h46276
                          · linarith only [h0, h45992, h46094, h46272, h46276, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h46278 | h46278
                            · linarith only [h36828, h46272, h46278, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h1bigk with h46280c | h46280c | h46280c | h46280c | h46280c | h46280c | h46280c | h46280c | h46280c | h46280c | h46280c | h46280c | h46280c | h46280c | h46280c | h46280c | h46280c | h46280c | h46280c | h46280c | h46280c | h46280c | h46280c | h46280c | h46280c
                              · have p46280_0 := h46280c.1
                                have p46280_1 := h46280c.2.1
                                have p46280_2 := h46280c.2.2.1
                                have p46280_3 := h46280c.2.2.2
                                linarith only [hlam, p46280_0]
                              · have p46280_0 := h46280c.1
                                have p46280_1 := h46280c.2.1
                                have p46280_2 := h46280c.2.2.1
                                have p46280_3 := h46280c.2.2.2
                                linarith only [h0, hlam, p46280_0]
                              · have p46280_0 := h46280c.1
                                have p46280_1 := h46280c.2.1
                                have p46280_2 := h46280c.2.2.1
                                have p46280_3 := h46280c.2.2.2
                                linarith only [h33187, hlam, p46280_0]
                              · have p46280_0 := h46280c.1
                                have p46280_1 := h46280c.2.1
                                have p46280_2 := h46280c.2.2.1
                                have p46280_3 := h46280c.2.2.2
                                linarith only [h36828, hlam, p46280_0]
                              · have p46280_0 := h46280c.1
                                have p46280_1 := h46280c.2.1
                                have p46280_2 := h46280c.2.2.1
                                have p46280_3 := h46280c.2.2.2
                                linarith only [h39227, hlam, p46280_0]
                              · have p46280_0 := h46280c.1
                                have p46280_1 := h46280c.2.1
                                have p46280_2 := h46280c.2.2.1
                                have p46280_3 := h46280c.2.2.2
                                linarith only [h46094, hc01, hc23, hlam, hphi, ht12, p46280_1]
                              · have p46280_0 := h46280c.1
                                have p46280_1 := h46280c.2.1
                                have p46280_2 := h46280c.2.2.1
                                have p46280_3 := h46280c.2.2.2
                                linarith only [hlam, p46280_0]
                              · have p46280_0 := h46280c.1
                                have p46280_1 := h46280c.2.1
                                have p46280_2 := h46280c.2.2.1
                                have p46280_3 := h46280c.2.2.2
                                linarith only [h46094, hlam, p46280_1]
                              · have p46280_0 := h46280c.1
                                have p46280_1 := h46280c.2.1
                                have p46280_2 := h46280c.2.2.1
                                have p46280_3 := h46280c.2.2.2
                                linarith only [h36828, h46094, hc01, hc23, hlam, hphi, ht12, p46280_1]
                              · have p46280_0 := h46280c.1
                                have p46280_1 := h46280c.2.1
                                have p46280_2 := h46280c.2.2.1
                                have p46280_3 := h46280c.2.2.2
                                linarith only [h39227, h46094, hc01, hc23, hlam, hphi, ht12, p46280_1]
                              · have p46280_0 := h46280c.1
                                have p46280_1 := h46280c.2.1
                                have p46280_2 := h46280c.2.2.1
                                have p46280_3 := h46280c.2.2.2
                                rcases p46280_3 (m.d 0 1) (by simp) with h46291 | h46291
                                · linarith only [h46291, hlam, p46280_0]
                                · rcases p46280_3 (m.d 1 2) (by simp) with h46293 | h46293
                                  · linarith only [h46094, h46293, hlam]
                                  · linarith only [h0, h46293, hlam]
                              · have p46280_0 := h46280c.1
                                have p46280_1 := h46280c.2.1
                                have p46280_2 := h46280c.2.2.1
                                have p46280_3 := h46280c.2.2.2
                                linarith only [h0, h46094, hc01, hc23, hlam, hphi, ht12, p46280_1]
                              · have p46280_0 := h46280c.1
                                have p46280_1 := h46280c.2.1
                                have p46280_2 := h46280c.2.2.1
                                have p46280_3 := h46280c.2.2.2
                                linarith only [hlam, p46280_0]
                              · have p46280_0 := h46280c.1
                                have p46280_1 := h46280c.2.1
                                have p46280_2 := h46280c.2.2.1
                                have p46280_3 := h46280c.2.2.2
                                linarith only [h36828, h46094, hc01, hc23, hlam, hphi, ht12, p46280_1]
                              · have p46280_0 := h46280c.1
                                have p46280_1 := h46280c.2.1
                                have p46280_2 := h46280c.2.2.1
                                have p46280_3 := h46280c.2.2.2
                                linarith only [h36828, h46094, h46272, hc01, hc23, hlam, hphi, ht12, p46280_1]
                              · have p46280_0 := h46280c.1
                                have p46280_1 := h46280c.2.1
                                have p46280_2 := h46280c.2.2.1
                                have p46280_3 := h46280c.2.2.2
                                linarith only [h46272, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p46280_1]
                              · have p46280_0 := h46280c.1
                                have p46280_1 := h46280c.2.1
                                have p46280_2 := h46280c.2.2.1
                                have p46280_3 := h46280c.2.2.2
                                linarith only [h46268, hlam, p46280_0]
                              · have p46280_0 := h46280c.1
                                have p46280_1 := h46280c.2.1
                                have p46280_2 := h46280c.2.2.1
                                have p46280_3 := h46280c.2.2.2
                                linarith only [h46270, hlam, p46280_1]
                              · have p46280_0 := h46280c.1
                                have p46280_1 := h46280c.2.1
                                have p46280_2 := h46280c.2.2.1
                                have p46280_3 := h46280c.2.2.2
                                linarith only [hlam, p46280_0]
                              · have p46280_0 := h46280c.1
                                have p46280_1 := h46280c.2.1
                                have p46280_2 := h46280c.2.2.1
                                have p46280_3 := h46280c.2.2.2
                                linarith only [h46272, hlam, p46280_1]
                              · have p46280_0 := h46280c.1
                                have p46280_1 := h46280c.2.1
                                have p46280_2 := h46280c.2.2.1
                                have p46280_3 := h46280c.2.2.2
                                linarith only [h46094, h46269, hc01, hc23, hlam, hphi, ht12, p46280_1]
                              · have p46280_0 := h46280c.1
                                have p46280_1 := h46280c.2.1
                                have p46280_2 := h46280c.2.2.1
                                have p46280_3 := h46280c.2.2.2
                                linarith only [h46269, hlam, p46280_0]
                              · have p46280_0 := h46280c.1
                                have p46280_1 := h46280c.2.1
                                have p46280_2 := h46280c.2.2.1
                                have p46280_3 := h46280c.2.2.2
                                linarith only [h46271, hlam, p46280_0]
                              · have p46280_0 := h46280c.1
                                have p46280_1 := h46280c.2.1
                                have p46280_2 := h46280c.2.2.1
                                have p46280_3 := h46280c.2.2.2
                                linarith only [h36828, h46094, h46269, hc01, hc23, hlam, hphi, ht12, p46280_1]
                              · have p46280_0 := h46280c.1
                                have p46280_1 := h46280c.2.1
                                have p46280_2 := h46280c.2.2.1
                                have p46280_3 := h46280c.2.2.2
                                linarith only [hlam, p46280_0]
                        · linarith only [h0, h46094, h46275, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h46094, h46274, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h33187, h45993, h45995, h46094, h46271, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h33187, h41027, h45992, h45994, h46270, hlam]
              · linarith only [h0, h45993, h46269, hlam]
            · linarith only [h0, h45992, h46268, hlam]
      · linarith only [h41027, h45993, h45995, hlam]
    · linarith only [h41027, h45992, h45994, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h46318 | h46318
    · rcases m.htr 0 3 5 (by decide) (by decide) with h46319 | h46319
      · rcases m.htr 0 4 5 (by decide) (by decide) with h46320 | h46320
        · linarith only [h45992, h45993, h46320, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h46322 | h46322
          · rcases m.htr 1 2 4 (by decide) (by decide) with h46323 | h46323
            · rcases m.htr 1 2 5 (by decide) (by decide) with h46324 | h46324
              · rcases m.htr 1 3 4 (by decide) (by decide) with h46325 | h46325
                · rcases m.htr 1 3 5 (by decide) (by decide) with h46326 | h46326
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h46327 | h46327
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h46328 | h46328
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h46329 | h46329
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h46330 | h46330
                          · linarith only [h45992, h45993, h46320, h46322, h46329, h46330, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h46332 | h46332
                            · linarith only [h45992, h45993, h46328, h46330, h46332, hlam]
                            · rcases h1bigk with h46334c | h46334c | h46334c | h46334c | h46334c | h46334c | h46334c | h46334c | h46334c | h46334c | h46334c | h46334c | h46334c | h46334c | h46334c | h46334c | h46334c | h46334c | h46334c | h46334c | h46334c | h46334c | h46334c | h46334c | h46334c
                              · have p46334_0 := h46334c.1
                                have p46334_1 := h46334c.2.1
                                have p46334_2 := h46334c.2.2.1
                                have p46334_3 := h46334c.2.2.2
                                linarith only [hlam, p46334_0]
                              · have p46334_0 := h46334c.1
                                have p46334_1 := h46334c.2.1
                                have p46334_2 := h46334c.2.2.1
                                have p46334_3 := h46334c.2.2.2
                                linarith only [h0, hlam, p46334_0]
                              · have p46334_0 := h46334c.1
                                have p46334_1 := h46334c.2.1
                                have p46334_2 := h46334c.2.2.1
                                have p46334_3 := h46334c.2.2.2
                                linarith only [h33187, hlam, p46334_0]
                              · have p46334_0 := h46334c.1
                                have p46334_1 := h46334c.2.1
                                have p46334_2 := h46334c.2.2.1
                                have p46334_3 := h46334c.2.2.2
                                linarith only [h36828, hlam, p46334_0]
                              · have p46334_0 := h46334c.1
                                have p46334_1 := h46334c.2.1
                                have p46334_2 := h46334c.2.2.1
                                have p46334_3 := h46334c.2.2.2
                                linarith only [h39227, hlam, p46334_0]
                              · have p46334_0 := h46334c.1
                                have p46334_1 := h46334c.2.1
                                have p46334_2 := h46334c.2.2.1
                                have p46334_3 := h46334c.2.2.2
                                rcases p46334_3 (m.d 0 1) (by simp) with h46340 | h46340
                                · linarith only [h46340, hlam, p46334_0]
                                · rcases p46334_3 (m.d 1 2) (by simp) with h46342 | h46342
                                  · rcases p46334_3 (m.d 1 3) (by simp) with h46343 | h46343
                                    · linarith only [h46322, h46343, hlam]
                                    · linarith only [h33187, h46343, hlam]
                                  · linarith only [h46342, hlam, p46334_0]
                              · have p46334_0 := h46334c.1
                                have p46334_1 := h46334c.2.1
                                have p46334_2 := h46334c.2.2.1
                                have p46334_3 := h46334c.2.2.2
                                linarith only [hlam, p46334_0]
                              · have p46334_0 := h46334c.1
                                have p46334_1 := h46334c.2.1
                                have p46334_2 := h46334c.2.2.1
                                have p46334_3 := h46334c.2.2.2
                                linarith only [h45993, h46325, h46327, h46330, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p46334_1]
                              · have p46334_0 := h46334c.1
                                have p46334_1 := h46334c.2.1
                                have p46334_2 := h46334c.2.2.1
                                have p46334_3 := h46334c.2.2.2
                                linarith only [h45992, h45993, h46327, h46328, h46330, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p46334_1]
                              · have p46334_0 := h46334c.1
                                have p46334_1 := h46334c.2.1
                                have p46334_2 := h46334c.2.2.1
                                have p46334_3 := h46334c.2.2.2
                                linarith only [h45992, h45993, h46327, h46328, h46330, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p46334_1]
                              · have p46334_0 := h46334c.1
                                have p46334_1 := h46334c.2.1
                                have p46334_2 := h46334c.2.2.1
                                have p46334_3 := h46334c.2.2.2
                                rcases p46334_3 (m.d 0 1) (by simp) with h46351 | h46351
                                · linarith only [h46351, hlam, p46334_0]
                                · rcases p46334_3 (m.d 1 2) (by simp) with h46353 | h46353
                                  · rcases p46334_3 (m.d 1 3) (by simp) with h46354 | h46354
                                    · rcases p46334_3 (m.d 1 4) (by simp) with h46355 | h46355
                                      · linarith only [h46325, h46355, hlam]
                                      · linarith only [h36828, h46355, hlam]
                                    · linarith only [h46354, hlam, p46334_0]
                                  · linarith only [h0, h46353, hlam]
                              · have p46334_0 := h46334c.1
                                have p46334_1 := h46334c.2.1
                                have p46334_2 := h46334c.2.2.1
                                have p46334_3 := h46334c.2.2.2
                                linarith only [h46322, hlam, p46334_0]
                              · have p46334_0 := h46334c.1
                                have p46334_1 := h46334c.2.1
                                have p46334_2 := h46334c.2.2.1
                                have p46334_3 := h46334c.2.2.2
                                linarith only [hlam, p46334_0]
                              · have p46334_0 := h46334c.1
                                have p46334_1 := h46334c.2.1
                                have p46334_2 := h46334c.2.2.1
                                have p46334_3 := h46334c.2.2.2
                                linarith only [h45992, h45993, h46327, h46328, h46330, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p46334_1]
                              · have p46334_0 := h46334c.1
                                have p46334_1 := h46334c.2.1
                                have p46334_2 := h46334c.2.2.1
                                have p46334_3 := h46334c.2.2.2
                                linarith only [h45992, h45993, h46322, h46327, h46328, h46330, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p46334_1]
                              · have p46334_0 := h46334c.1
                                have p46334_1 := h46334c.2.1
                                have p46334_2 := h46334c.2.2.1
                                have p46334_3 := h46334c.2.2.2
                                rcases p46334_3 (m.d 0 1) (by simp) with h46364 | h46364
                                · linarith only [h46364, hlam, p46334_0]
                                · rcases p46334_3 (m.d 1 2) (by simp) with h46366 | h46366
                                  · rcases p46334_3 (m.d 1 3) (by simp) with h46367 | h46367
                                    · rcases p46334_3 (m.d 1 4) (by simp) with h46368 | h46368
                                      · rcases p46334_3 (m.d 1 5) (by simp) with h46369 | h46369
                                        · linarith only [h46327, h46369, hlam]
                                        · linarith only [h39227, h46369, hlam]
                                      · linarith only [h46368, hlam, p46334_0]
                                    · linarith only [h33187, h46367, hlam]
                                  · linarith only [h0, h46366, hlam]
                              · have p46334_0 := h46334c.1
                                have p46334_1 := h46334c.2.1
                                have p46334_2 := h46334c.2.2.1
                                have p46334_3 := h46334c.2.2.2
                                linarith only [h46323, hlam, p46334_0]
                              · have p46334_0 := h46334c.1
                                have p46334_1 := h46334c.2.1
                                have p46334_2 := h46334c.2.2.1
                                have p46334_3 := h46334c.2.2.2
                                linarith only [h46325, hlam, p46334_1]
                              · have p46334_0 := h46334c.1
                                have p46334_1 := h46334c.2.1
                                have p46334_2 := h46334c.2.2.1
                                have p46334_3 := h46334c.2.2.2
                                linarith only [hlam, p46334_0]
                              · have p46334_0 := h46334c.1
                                have p46334_1 := h46334c.2.1
                                have p46334_2 := h46334c.2.2.1
                                have p46334_3 := h46334c.2.2.2
                                linarith only [h45992, h45993, h46327, h46328, h46330, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p46334_1]
                              · have p46334_0 := h46334c.1
                                have p46334_1 := h46334c.2.1
                                have p46334_2 := h46334c.2.2.1
                                have p46334_3 := h46334c.2.2.2
                                rcases p46334_3 (m.d 0 1) (by simp) with h46379 | h46379
                                · linarith only [h46379, hlam, p46334_0]
                                · rcases p46334_3 (m.d 1 2) (by simp) with h46381 | h46381
                                  · rcases p46334_3 (m.d 1 3) (by simp) with h46382 | h46382
                                    · rcases p46334_3 (m.d 1 4) (by simp) with h46383 | h46383
                                      · rcases p46334_3 (m.d 1 5) (by simp) with h46384 | h46384
                                        · rcases h1emax with h46385 | h46385 | h46385 | h46385 | h46385
                                          · rcases h2bigk with h46386c | h46386c | h46386c | h46386c | h46386c | h46386c | h46386c | h46386c | h46386c | h46386c | h46386c | h46386c | h46386c | h46386c | h46386c | h46386c | h46386c | h46386c | h46386c | h46386c | h46386c | h46386c | h46386c | h46386c | h46386c
                                            · have p46386_0 := h46386c.1
                                              have p46386_1 := h46386c.2.1
                                              have p46386_2 := h46386c.2.2.1
                                              have p46386_3 := h46386c.2.2.2
                                              linarith only [hlam, p46386_0]
                                            · have p46386_0 := h46386c.1
                                              have p46386_1 := h46386c.2.1
                                              have p46386_2 := h46386c.2.2.1
                                              have p46386_3 := h46386c.2.2.2
                                              linarith only [h0, hlam, p46386_0]
                                            · have p46386_0 := h46386c.1
                                              have p46386_1 := h46386c.2.1
                                              have p46386_2 := h46386c.2.2.1
                                              have p46386_3 := h46386c.2.2.2
                                              linarith only [h41027, hlam, p46386_0]
                                            · have p46386_0 := h46386c.1
                                              have p46386_1 := h46386c.2.1
                                              have p46386_2 := h46386c.2.2.1
                                              have p46386_3 := h46386c.2.2.2
                                              linarith only [h45993, h46328, h46330, hc34, hc45, hlam, hphi, p46386_1]
                                            · have p46386_0 := h46386c.1
                                              have p46386_1 := h46386c.2.1
                                              have p46386_2 := h46386c.2.2.1
                                              have p46386_3 := h46386c.2.2.2
                                              linarith only [h45993, hlam, p46386_0]
                                            · have p46386_0 := h46386c.1
                                              have p46386_1 := h46386c.2.1
                                              have p46386_2 := h46386c.2.2.1
                                              have p46386_3 := h46386c.2.2.2
                                              rcases p46386_3 (m.d 0 2) (by simp) with h46392 | h46392
                                              · linarith only [h0, h46392, hlam]
                                              · rcases p46386_3 (m.d 1 2) (by simp) with h46394 | h46394
                                                · rcases p46386_3 (m.d 2 3) (by simp) with h46395 | h46395
                                                  · linarith only [h46322, h46395, hlam]
                                                  · linarith only [h41027, h46395, hlam]
                                                · linarith only [h0, h46394, hlam]
                                            · have p46386_0 := h46386c.1
                                              have p46386_1 := h46386c.2.1
                                              have p46386_2 := h46386c.2.2.1
                                              have p46386_3 := h46386c.2.2.2
                                              linarith only [hlam, p46386_0]
                                            · have p46386_0 := h46386c.1
                                              have p46386_1 := h46386c.2.1
                                              have p46386_2 := h46386c.2.2.1
                                              have p46386_3 := h46386c.2.2.2
                                              linarith only [h0, h41027, hc01, hc12, hlam, hphi, p46386_1]
                                            · have p46386_0 := h46386c.1
                                              have p46386_1 := h46386c.2.1
                                              have p46386_2 := h46386c.2.2.1
                                              have p46386_3 := h46386c.2.2.2
                                              linarith only [h45992, h45993, h46322, h46325, h46327, h46330, hlam, p46386_2]
                                            · have p46386_0 := h46386c.1
                                              have p46386_1 := h46386c.2.1
                                              have p46386_2 := h46386c.2.2.1
                                              have p46386_3 := h46386c.2.2.2
                                              linarith only [h45992, h45993, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p46386_1]
                                            · have p46386_0 := h46386c.1
                                              have p46386_1 := h46386c.2.1
                                              have p46386_2 := h46386c.2.2.1
                                              have p46386_3 := h46386c.2.2.2
                                              linarith only [h45992, h46322, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p46386_1]
                                            · have p46386_0 := h46386c.1
                                              have p46386_1 := h46386c.2.1
                                              have p46386_2 := h46386c.2.2.1
                                              have p46386_3 := h46386c.2.2.2
                                              linarith only [h46322, hlam, p46386_0]
                                            · have p46386_0 := h46386c.1
                                              have p46386_1 := h46386c.2.1
                                              have p46386_2 := h46386c.2.2.1
                                              have p46386_3 := h46386c.2.2.2
                                              linarith only [hlam, p46386_0]
                                            · have p46386_0 := h46386c.1
                                              have p46386_1 := h46386c.2.1
                                              have p46386_2 := h46386c.2.2.1
                                              have p46386_3 := h46386c.2.2.2
                                              rcases p46386_3 (m.d 0 2) (by simp) with h46406 | h46406
                                              · linarith only [h41027, h46406, hlam]
                                              · linarith only [h45992, h46406, hlam]
                                            · have p46386_0 := h46386c.1
                                              have p46386_1 := h46386c.2.1
                                              have p46386_2 := h46386c.2.2.1
                                              have p46386_3 := h46386c.2.2.2
                                              linarith only [h45992, h45993, h46322, h46328, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p46386_1]
                                            · have p46386_0 := h46386c.1
                                              have p46386_1 := h46386c.2.1
                                              have p46386_2 := h46386c.2.2.1
                                              have p46386_3 := h46386c.2.2.2
                                              linarith only [h45992, hlam, p46386_0]
                                            · have p46386_0 := h46386c.1
                                              have p46386_1 := h46386c.2.1
                                              have p46386_2 := h46386c.2.2.1
                                              have p46386_3 := h46386c.2.2.2
                                              linarith only [h46323, hlam, p46386_0]
                                            · have p46386_0 := h46386c.1
                                              have p46386_1 := h46386c.2.1
                                              have p46386_2 := h46386c.2.2.1
                                              have p46386_3 := h46386c.2.2.2
                                              linarith only [h46328, hlam, p46386_0]
                                            · have p46386_0 := h46386c.1
                                              have p46386_1 := h46386c.2.1
                                              have p46386_2 := h46386c.2.2.1
                                              have p46386_3 := h46386c.2.2.2
                                              linarith only [hlam, p46386_0]
                                            · have p46386_0 := h46386c.1
                                              have p46386_1 := h46386c.2.1
                                              have p46386_2 := h46386c.2.2.1
                                              have p46386_3 := h46386c.2.2.2
                                              linarith only [h46330, hlam, p46386_0]
                                            · have p46386_0 := h46386c.1
                                              have p46386_1 := h46386c.2.1
                                              have p46386_2 := h46386c.2.2.1
                                              have p46386_3 := h46386c.2.2.2
                                              linarith only [h45992, h46324, h46328, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p46386_1]
                                            · have p46386_0 := h46386c.1
                                              have p46386_1 := h46386c.2.1
                                              have p46386_2 := h46386c.2.2.1
                                              have p46386_3 := h46386c.2.2.2
                                              linarith only [h46324, hlam, p46386_0]
                                            · have p46386_0 := h46386c.1
                                              have p46386_1 := h46386c.2.1
                                              have p46386_2 := h46386c.2.2.1
                                              have p46386_3 := h46386c.2.2.2
                                              linarith only [h46329, hlam, p46386_0]
                                            · have p46386_0 := h46386c.1
                                              have p46386_1 := h46386c.2.1
                                              have p46386_2 := h46386c.2.2.1
                                              have p46386_3 := h46386c.2.2.2
                                              rcases p46386_3 (m.d 0 2) (by simp) with h46418 | h46418
                                              · linarith only [h45993, h46418, hlam]
                                              · linarith only [h45992, h46418, hlam]
                                            · have p46386_0 := h46386c.1
                                              have p46386_1 := h46386c.2.1
                                              have p46386_2 := h46386c.2.2.1
                                              have p46386_3 := h46386c.2.2.2
                                              linarith only [hlam, p46386_0]
                                          · linarith only [h0, h46385, hc01, hlam]
                                          · linarith only [h45992, h45993, h46325, h46327, h46328, h46330, h46385, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                          · linarith only [h45992, h45993, h46327, h46328, h46330, h46385, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                          · linarith only [h46385, hc01, hlam, p46334_1]
                                        · linarith only [h46384, hlam, p46334_0]
                                      · linarith only [h36828, h46383, hlam]
                                    · linarith only [h33187, h46382, hlam]
                                  · linarith only [h0, h46381, hlam]
                              · have p46334_0 := h46334c.1
                                have p46334_1 := h46334c.2.1
                                have p46334_2 := h46334c.2.2.1
                                have p46334_3 := h46334c.2.2.2
                                linarith only [h46324, hlam, p46334_0]
                              · have p46334_0 := h46334c.1
                                have p46334_1 := h46334c.2.1
                                have p46334_2 := h46334c.2.2.1
                                have p46334_3 := h46334c.2.2.2
                                linarith only [h46326, hlam, p46334_0]
                              · have p46334_0 := h46334c.1
                                have p46334_1 := h46334c.2.1
                                have p46334_2 := h46334c.2.2.1
                                have p46334_3 := h46334c.2.2.2
                                linarith only [h46327, hlam, p46334_0]
                              · have p46334_0 := h46334c.1
                                have p46334_1 := h46334c.2.1
                                have p46334_2 := h46334c.2.2.1
                                have p46334_3 := h46334c.2.2.2
                                linarith only [hlam, p46334_0]
                        · linarith only [h33187, h41027, h45992, h46319, h46322, h46328, h46329, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h41027, h46318, h46328, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h46436 | h46436
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h46437 | h46437
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h46438 | h46438
                          · linarith only [h45992, h45993, h46327, h46438, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h46440 | h46440
                            · linarith only [h39227, h45992, h45993, h46327, h46436, h46440, hc01, hc25, hlam, hphi, ht12]
                            · rcases h1bigk with h46442c | h46442c | h46442c | h46442c | h46442c | h46442c | h46442c | h46442c | h46442c | h46442c | h46442c | h46442c | h46442c | h46442c | h46442c | h46442c | h46442c | h46442c | h46442c | h46442c | h46442c | h46442c | h46442c | h46442c | h46442c
                              · have p46442_0 := h46442c.1
                                have p46442_1 := h46442c.2.1
                                have p46442_2 := h46442c.2.2.1
                                have p46442_3 := h46442c.2.2.2
                                linarith only [hlam, p46442_0]
                              · have p46442_0 := h46442c.1
                                have p46442_1 := h46442c.2.1
                                have p46442_2 := h46442c.2.2.1
                                have p46442_3 := h46442c.2.2.2
                                linarith only [h0, hlam, p46442_0]
                              · have p46442_0 := h46442c.1
                                have p46442_1 := h46442c.2.1
                                have p46442_2 := h46442c.2.2.1
                                have p46442_3 := h46442c.2.2.2
                                linarith only [h33187, hlam, p46442_0]
                              · have p46442_0 := h46442c.1
                                have p46442_1 := h46442c.2.1
                                have p46442_2 := h46442c.2.2.1
                                have p46442_3 := h46442c.2.2.2
                                linarith only [h36828, hlam, p46442_0]
                              · have p46442_0 := h46442c.1
                                have p46442_1 := h46442c.2.1
                                have p46442_2 := h46442c.2.2.1
                                have p46442_3 := h46442c.2.2.2
                                linarith only [h39227, hlam, p46442_0]
                              · have p46442_0 := h46442c.1
                                have p46442_1 := h46442c.2.1
                                have p46442_2 := h46442c.2.2.1
                                have p46442_3 := h46442c.2.2.2
                                rcases p46442_3 (m.d 0 1) (by simp) with h46448 | h46448
                                · linarith only [h46448, hlam, p46442_0]
                                · rcases p46442_3 (m.d 1 2) (by simp) with h46450 | h46450
                                  · rcases p46442_3 (m.d 1 3) (by simp) with h46451 | h46451
                                    · linarith only [h46322, h46451, hlam]
                                    · linarith only [h33187, h46451, hlam]
                                  · linarith only [h46450, hlam, p46442_0]
                              · have p46442_0 := h46442c.1
                                have p46442_1 := h46442c.2.1
                                have p46442_2 := h46442c.2.2.1
                                have p46442_3 := h46442c.2.2.2
                                linarith only [hlam, p46442_0]
                              · have p46442_0 := h46442c.1
                                have p46442_1 := h46442c.2.1
                                have p46442_2 := h46442c.2.2.1
                                have p46442_3 := h46442c.2.2.2
                                linarith only [h33187, hc01, hc12, hlam, hphi, p46442_1]
                              · have p46442_0 := h46442c.1
                                have p46442_1 := h46442c.2.1
                                have p46442_2 := h46442c.2.2.1
                                have p46442_3 := h46442c.2.2.2
                                linarith only [h36828, hc01, hc12, hlam, hphi, p46442_1]
                              · have p46442_0 := h46442c.1
                                have p46442_1 := h46442c.2.1
                                have p46442_2 := h46442c.2.2.1
                                have p46442_3 := h46442c.2.2.2
                                linarith only [h45992, h45993, h46324, h46436, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p46442_1]
                              · have p46442_0 := h46442c.1
                                have p46442_1 := h46442c.2.1
                                have p46442_2 := h46442c.2.2.1
                                have p46442_3 := h46442c.2.2.2
                                rcases p46442_3 (m.d 0 1) (by simp) with h46459 | h46459
                                · linarith only [h46459, hlam, p46442_0]
                                · rcases p46442_3 (m.d 1 2) (by simp) with h46461 | h46461
                                  · rcases p46442_3 (m.d 1 3) (by simp) with h46462 | h46462
                                    · rcases p46442_3 (m.d 1 4) (by simp) with h46463 | h46463
                                      · linarith only [h46325, h46463, hlam]
                                      · linarith only [h36828, h46463, hlam]
                                    · linarith only [h46462, hlam, p46442_0]
                                  · linarith only [h0, h46461, hlam]
                              · have p46442_0 := h46442c.1
                                have p46442_1 := h46442c.2.1
                                have p46442_2 := h46442c.2.2.1
                                have p46442_3 := h46442c.2.2.2
                                linarith only [h46322, hlam, p46442_0]
                              · have p46442_0 := h46442c.1
                                have p46442_1 := h46442c.2.1
                                have p46442_2 := h46442c.2.2.1
                                have p46442_3 := h46442c.2.2.2
                                linarith only [hlam, p46442_0]
                              · have p46442_0 := h46442c.1
                                have p46442_1 := h46442c.2.1
                                have p46442_2 := h46442c.2.2.1
                                have p46442_3 := h46442c.2.2.2
                                linarith only [h36828, hc01, hc13, hlam, hphi, p46442_1]
                              · have p46442_0 := h46442c.1
                                have p46442_1 := h46442c.2.1
                                have p46442_2 := h46442c.2.2.1
                                have p46442_3 := h46442c.2.2.2
                                linarith only [h45992, h45993, h46322, h46324, h46436, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p46442_1]
                              · have p46442_0 := h46442c.1
                                have p46442_1 := h46442c.2.1
                                have p46442_2 := h46442c.2.2.1
                                have p46442_3 := h46442c.2.2.2
                                linarith only [h46327, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p46442_1]
                              · have p46442_0 := h46442c.1
                                have p46442_1 := h46442c.2.1
                                have p46442_2 := h46442c.2.2.1
                                have p46442_3 := h46442c.2.2.2
                                linarith only [h46323, hlam, p46442_0]
                              · have p46442_0 := h46442c.1
                                have p46442_1 := h46442c.2.1
                                have p46442_2 := h46442c.2.2.1
                                have p46442_3 := h46442c.2.2.2
                                linarith only [h46325, hlam, p46442_1]
                              · have p46442_0 := h46442c.1
                                have p46442_1 := h46442c.2.1
                                have p46442_2 := h46442c.2.2.1
                                have p46442_3 := h46442c.2.2.2
                                linarith only [hlam, p46442_0]
                              · have p46442_0 := h46442c.1
                                have p46442_1 := h46442c.2.1
                                have p46442_2 := h46442c.2.2.1
                                have p46442_3 := h46442c.2.2.2
                                linarith only [h46327, hlam, p46442_1]
                              · have p46442_0 := h46442c.1
                                have p46442_1 := h46442c.2.1
                                have p46442_2 := h46442c.2.2.1
                                have p46442_3 := h46442c.2.2.2
                                rcases p46442_3 (m.d 0 1) (by simp) with h46477 | h46477
                                · linarith only [h46477, hlam, p46442_0]
                                · rcases p46442_3 (m.d 1 2) (by simp) with h46479 | h46479
                                  · rcases p46442_3 (m.d 1 3) (by simp) with h46480 | h46480
                                    · rcases p46442_3 (m.d 1 4) (by simp) with h46481 | h46481
                                      · linarith only [h46327, h46481, hlam]
                                      · linarith only [h36828, h46481, hlam]
                                    · linarith only [h33187, h46480, hlam]
                                  · linarith only [h0, h46479, hlam]
                              · have p46442_0 := h46442c.1
                                have p46442_1 := h46442c.2.1
                                have p46442_2 := h46442c.2.2.1
                                have p46442_3 := h46442c.2.2.2
                                linarith only [h46324, hlam, p46442_0]
                              · have p46442_0 := h46442c.1
                                have p46442_1 := h46442c.2.1
                                have p46442_2 := h46442c.2.2.1
                                have p46442_3 := h46442c.2.2.2
                                linarith only [h46326, hlam, p46442_0]
                              · have p46442_0 := h46442c.1
                                have p46442_1 := h46442c.2.1
                                have p46442_2 := h46442c.2.2.1
                                have p46442_3 := h46442c.2.2.2
                                linarith only [h36828, hc01, hc15, hlam, hphi, p46442_1]
                              · have p46442_0 := h46442c.1
                                have p46442_1 := h46442c.2.1
                                have p46442_2 := h46442c.2.2.1
                                have p46442_3 := h46442c.2.2.2
                                linarith only [hlam, p46442_0]
                        · linarith only [h41027, h46319, h46437, hlam]
                      · linarith only [h41027, h45992, h46318, h46436, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h33187, h46319, h46326, hlam]
                · linarith only [h33187, h45992, h45993, h46318, h46325, hc01, hc25, hlam, hphi, ht12]
              · linarith only [h41027, h46322, h46324, hc02, hc25, hlam, hphi]
            · linarith only [h41027, h45992, h46322, h46323, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h46496 | h46496
            · rcases m.htr 1 2 5 (by decide) (by decide) with h46497 | h46497
              · linarith only [h45992, h45993, h46322, h46497, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h46499 | h46499
                · rcases m.htr 1 3 5 (by decide) (by decide) with h46500 | h46500
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h46501 | h46501
                    · linarith only [h36828, h46320, h46322, h46496, h46501, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h46503 | h46503
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h46504 | h46504
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h46505 | h46505
                          · linarith only [h0, h45992, h46497, h46501, h46504, h46505, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h46507 | h46507
                            · linarith only [h0, h46497, h46505, h46507, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h1bigk with h46509c | h46509c | h46509c | h46509c | h46509c | h46509c | h46509c | h46509c | h46509c | h46509c | h46509c | h46509c | h46509c | h46509c | h46509c | h46509c | h46509c | h46509c | h46509c | h46509c | h46509c | h46509c | h46509c | h46509c | h46509c
                              · have p46509_0 := h46509c.1
                                have p46509_1 := h46509c.2.1
                                have p46509_2 := h46509c.2.2.1
                                have p46509_3 := h46509c.2.2.2
                                linarith only [hlam, p46509_0]
                              · have p46509_0 := h46509c.1
                                have p46509_1 := h46509c.2.1
                                have p46509_2 := h46509c.2.2.1
                                have p46509_3 := h46509c.2.2.2
                                linarith only [h0, hlam, p46509_0]
                              · have p46509_0 := h46509c.1
                                have p46509_1 := h46509c.2.1
                                have p46509_2 := h46509c.2.2.1
                                have p46509_3 := h46509c.2.2.2
                                linarith only [h33187, hlam, p46509_0]
                              · have p46509_0 := h46509c.1
                                have p46509_1 := h46509c.2.1
                                have p46509_2 := h46509c.2.2.1
                                have p46509_3 := h46509c.2.2.2
                                linarith only [h36828, hlam, p46509_0]
                              · have p46509_0 := h46509c.1
                                have p46509_1 := h46509c.2.1
                                have p46509_2 := h46509c.2.2.1
                                have p46509_3 := h46509c.2.2.2
                                linarith only [h39227, hlam, p46509_0]
                              · have p46509_0 := h46509c.1
                                have p46509_1 := h46509c.2.1
                                have p46509_2 := h46509c.2.2.1
                                have p46509_3 := h46509c.2.2.2
                                linarith only [h46497, h46504, hc01, hc23, hlam, hphi, ht12, p46509_1]
                              · have p46509_0 := h46509c.1
                                have p46509_1 := h46509c.2.1
                                have p46509_2 := h46509c.2.2.1
                                have p46509_3 := h46509c.2.2.2
                                linarith only [hlam, p46509_0]
                              · have p46509_0 := h46509c.1
                                have p46509_1 := h46509c.2.1
                                have p46509_2 := h46509c.2.2.1
                                have p46509_3 := h46509c.2.2.2
                                linarith only [h46322, hlam, p46509_1]
                              · have p46509_0 := h46509c.1
                                have p46509_1 := h46509c.2.1
                                have p46509_2 := h46509c.2.2.1
                                have p46509_3 := h46509c.2.2.2
                                linarith only [h46497, h46505, hc14, hc45, hlam, hphi, p46509_1]
                              · have p46509_0 := h46509c.1
                                have p46509_1 := h46509c.2.1
                                have p46509_2 := h46509c.2.2.1
                                have p46509_3 := h46509c.2.2.2
                                linarith only [h46497, hlam, p46509_1]
                              · have p46509_0 := h46509c.1
                                have p46509_1 := h46509c.2.1
                                have p46509_2 := h46509c.2.2.1
                                have p46509_3 := h46509c.2.2.2
                                rcases p46509_3 (m.d 0 1) (by simp) with h46520 | h46520
                                · linarith only [h46520, hlam, p46509_0]
                                · rcases p46509_3 (m.d 1 2) (by simp) with h46522 | h46522
                                  · linarith only [h46322, h46522, hlam]
                                  · linarith only [h0, h46522, hlam]
                              · have p46509_0 := h46509c.1
                                have p46509_1 := h46509c.2.1
                                have p46509_2 := h46509c.2.2.1
                                have p46509_3 := h46509c.2.2.2
                                linarith only [h0, hc01, hc13, hlam, hphi, p46509_1]
                              · have p46509_0 := h46509c.1
                                have p46509_1 := h46509c.2.1
                                have p46509_2 := h46509c.2.2.1
                                have p46509_3 := h46509c.2.2.2
                                linarith only [hlam, p46509_0]
                              · have p46509_0 := h46509c.1
                                have p46509_1 := h46509c.2.1
                                have p46509_2 := h46509c.2.2.1
                                have p46509_3 := h46509c.2.2.2
                                linarith only [h36828, h46322, hc01, hc23, hlam, hphi, ht12, p46509_1]
                              · have p46509_0 := h46509c.1
                                have p46509_1 := h46509c.2.1
                                have p46509_2 := h46509c.2.2.1
                                have p46509_3 := h46509c.2.2.2
                                linarith only [h36828, h46322, h46496, h46497, hc01, hc23, hlam, hphi, ht12, p46509_1]
                              · have p46509_0 := h46509c.1
                                have p46509_1 := h46509c.2.1
                                have p46509_2 := h46509c.2.2.1
                                have p46509_3 := h46509c.2.2.2
                                linarith only [h46496, h46497, hc01, hc25, hlam, hphi, ht12, p46509_1]
                              · have p46509_0 := h46509c.1
                                have p46509_1 := h46509c.2.1
                                have p46509_2 := h46509c.2.2.1
                                have p46509_3 := h46509c.2.2.2
                                linarith only [h46496, hlam, p46509_0]
                              · have p46509_0 := h46509c.1
                                have p46509_1 := h46509c.2.1
                                have p46509_2 := h46509c.2.2.1
                                have p46509_3 := h46509c.2.2.2
                                linarith only [h46499, hlam, p46509_1]
                              · have p46509_0 := h46509c.1
                                have p46509_1 := h46509c.2.1
                                have p46509_2 := h46509c.2.2.1
                                have p46509_3 := h46509c.2.2.2
                                linarith only [hlam, p46509_0]
                              · have p46509_0 := h46509c.1
                                have p46509_1 := h46509c.2.1
                                have p46509_2 := h46509c.2.2.1
                                have p46509_3 := h46509c.2.2.2
                                linarith only [h46501, hlam, p46509_1]
                              · have p46509_0 := h46509c.1
                                have p46509_1 := h46509c.2.1
                                have p46509_2 := h46509c.2.2.1
                                have p46509_3 := h46509c.2.2.2
                                rcases p46509_3 (m.d 0 1) (by simp) with h46534 | h46534
                                · linarith only [h46534, hlam, p46509_0]
                                · rcases p46509_3 (m.d 1 2) (by simp) with h46536 | h46536
                                  · linarith only [h46497, h46536, hlam]
                                  · linarith only [h0, h46536, hlam]
                              · have p46509_0 := h46509c.1
                                have p46509_1 := h46509c.2.1
                                have p46509_2 := h46509c.2.2.1
                                have p46509_3 := h46509c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p46509_1]
                              · have p46509_0 := h46509c.1
                                have p46509_1 := h46509c.2.1
                                have p46509_2 := h46509c.2.2.1
                                have p46509_3 := h46509c.2.2.2
                                linarith only [h46500, hlam, p46509_0]
                              · have p46509_0 := h46509c.1
                                have p46509_1 := h46509c.2.1
                                have p46509_2 := h46509c.2.2.1
                                have p46509_3 := h46509c.2.2.2
                                linarith only [h36828, hc01, hc15, hlam, hphi, p46509_1]
                              · have p46509_0 := h46509c.1
                                have p46509_1 := h46509c.2.1
                                have p46509_2 := h46509c.2.2.1
                                have p46509_3 := h46509c.2.2.2
                                linarith only [hlam, p46509_0]
                        · linarith only [h33187, h46319, h46322, h46504, hlam]
                      · linarith only [h33187, h46318, h46322, h46503, hlam]
                  · linarith only [h33187, h46319, h46500, hlam]
                · linarith only [h33187, h36828, h46318, h46322, h46496, h46499, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h0, h39227, h45992, h45993, h46496, hc01, hc15, hlam, hphi]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h46548 | h46548
        · linarith only [h41027, h45992, h46319, h46548, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h46550 | h46550
          · rcases m.htr 1 2 4 (by decide) (by decide) with h46551 | h46551
            · rcases m.htr 1 2 5 (by decide) (by decide) with h46552 | h46552
              · rcases m.htr 1 3 4 (by decide) (by decide) with h46553 | h46553
                · rcases m.htr 1 3 5 (by decide) (by decide) with h46554 | h46554
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h46555 | h46555
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h46556 | h46556
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h46557 | h46557
                        · linarith only [h41027, h45992, h46319, h46550, h46557, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h41027, h45992, h46550, h46554, h46556, h46557, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h41027, h46318, h46556, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h46561 | h46561
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h46562 | h46562
                        · linarith only [h33187, h46319, h46550, h46562, hc01, hc12, hlam, hphi]
                        · linarith only [h41027, h45992, h46550, h46554, h46561, h46562, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h41027, h46318, h46561, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h46566 | h46566
                    · linarith only [h36828, h46548, h46553, h46554, h46566, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h46568 | h46568
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h46569 | h46569
                        · linarith only [h46550, h46554, h46569, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h46571 | h46571
                          · linarith only [h0, h39227, h45992, h46566, h46571, hc01, hc12, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h46573 | h46573
                            · linarith only [h41027, h45993, h46318, h46550, h46552, h46554, h46566, h46573, hc02, hc35, hlam, hphi, ht23]
                            · linarith only [h41027, h45992, h46550, h46554, h46568, h46573, hc34, hc45, hlam, hphi]
                      · linarith only [h41027, h46318, h46568, hlam]
                · linarith only [h41027, h45992, h46318, h46550, h46553, hlam]
              · linarith only [h41027, h45992, h46550, h46552, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h41027, h45992, h46550, h46551, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h46580 | h46580
            · rcases m.htr 1 2 5 (by decide) (by decide) with h46581 | h46581
              · linarith only [h45992, h45993, h46550, h46581, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h46583 | h46583
                · rcases m.htr 1 3 5 (by decide) (by decide) with h46584 | h46584
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h46585 | h46585
                    · linarith only [h36828, h46548, h46550, h46580, h46585, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h46587 | h46587
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h46588 | h46588
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h46589 | h46589
                          · linarith only [h0, h39227, h45992, h46581, h46585, h46588, h46589, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h46591 | h46591
                            · linarith only [h36828, h45992, h46580, h46581, h46587, h46589, h46591, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                            · rcases h1bigk with h46593c | h46593c | h46593c | h46593c | h46593c | h46593c | h46593c | h46593c | h46593c | h46593c | h46593c | h46593c | h46593c | h46593c | h46593c | h46593c | h46593c | h46593c | h46593c | h46593c | h46593c | h46593c | h46593c | h46593c | h46593c
                              · have p46593_0 := h46593c.1
                                have p46593_1 := h46593c.2.1
                                have p46593_2 := h46593c.2.2.1
                                have p46593_3 := h46593c.2.2.2
                                linarith only [hlam, p46593_0]
                              · have p46593_0 := h46593c.1
                                have p46593_1 := h46593c.2.1
                                have p46593_2 := h46593c.2.2.1
                                have p46593_3 := h46593c.2.2.2
                                linarith only [h0, hlam, p46593_0]
                              · have p46593_0 := h46593c.1
                                have p46593_1 := h46593c.2.1
                                have p46593_2 := h46593c.2.2.1
                                have p46593_3 := h46593c.2.2.2
                                linarith only [h33187, hlam, p46593_0]
                              · have p46593_0 := h46593c.1
                                have p46593_1 := h46593c.2.1
                                have p46593_2 := h46593c.2.2.1
                                have p46593_3 := h46593c.2.2.2
                                linarith only [h36828, hlam, p46593_0]
                              · have p46593_0 := h46593c.1
                                have p46593_1 := h46593c.2.1
                                have p46593_2 := h46593c.2.2.1
                                have p46593_3 := h46593c.2.2.2
                                linarith only [h39227, hlam, p46593_0]
                              · have p46593_0 := h46593c.1
                                have p46593_1 := h46593c.2.1
                                have p46593_2 := h46593c.2.2.1
                                have p46593_3 := h46593c.2.2.2
                                linarith only [h41027, h45992, h46319, h46550, h46581, h46584, h46587, h46589, hc01, hc23, hc34, hc45, hlam, hphi, ht12, p46593_1]
                              · have p46593_0 := h46593c.1
                                have p46593_1 := h46593c.2.1
                                have p46593_2 := h46593c.2.2.1
                                have p46593_3 := h46593c.2.2.2
                                linarith only [hlam, p46593_0]
                              · have p46593_0 := h46593c.1
                                have p46593_1 := h46593c.2.1
                                have p46593_2 := h46593c.2.2.1
                                have p46593_3 := h46593c.2.2.2
                                linarith only [h46550, hlam, p46593_1]
                              · have p46593_0 := h46593c.1
                                have p46593_1 := h46593c.2.1
                                have p46593_2 := h46593c.2.2.1
                                have p46593_3 := h46593c.2.2.2
                                linarith only [h36828, h41027, h45992, h46319, h46550, h46581, h46584, h46587, h46589, hc01, hc23, hc34, hc45, hlam, hphi, ht12, p46593_1]
                              · have p46593_0 := h46593c.1
                                have p46593_1 := h46593c.2.1
                                have p46593_2 := h46593c.2.2.1
                                have p46593_3 := h46593c.2.2.2
                                linarith only [h46581, hlam, p46593_1]
                              · have p46593_0 := h46593c.1
                                have p46593_1 := h46593c.2.1
                                have p46593_2 := h46593c.2.2.1
                                have p46593_3 := h46593c.2.2.2
                                rcases p46593_3 (m.d 0 1) (by simp) with h46604 | h46604
                                · linarith only [h46604, hlam, p46593_0]
                                · rcases p46593_3 (m.d 1 2) (by simp) with h46606 | h46606
                                  · linarith only [h46550, h46606, hlam]
                                  · linarith only [h0, h46606, hlam]
                              · have p46593_0 := h46593c.1
                                have p46593_1 := h46593c.2.1
                                have p46593_2 := h46593c.2.2.1
                                have p46593_3 := h46593c.2.2.2
                                linarith only [h0, h46550, hc01, hc23, hlam, hphi, ht12, p46593_1]
                              · have p46593_0 := h46593c.1
                                have p46593_1 := h46593c.2.1
                                have p46593_2 := h46593c.2.2.1
                                have p46593_3 := h46593c.2.2.2
                                linarith only [hlam, p46593_0]
                              · have p46593_0 := h46593c.1
                                have p46593_1 := h46593c.2.1
                                have p46593_2 := h46593c.2.2.1
                                have p46593_3 := h46593c.2.2.2
                                linarith only [h36828, h46550, hc01, hc23, hlam, hphi, ht12, p46593_1]
                              · have p46593_0 := h46593c.1
                                have p46593_1 := h46593c.2.1
                                have p46593_2 := h46593c.2.2.1
                                have p46593_3 := h46593c.2.2.2
                                linarith only [h39227, h46550, hc01, hc23, hlam, hphi, ht12, p46593_1]
                              · have p46593_0 := h46593c.1
                                have p46593_1 := h46593c.2.1
                                have p46593_2 := h46593c.2.2.1
                                have p46593_3 := h46593c.2.2.2
                                linarith only [h46550, h46580, hc01, hc23, hlam, hphi, ht12, p46593_1]
                              · have p46593_0 := h46593c.1
                                have p46593_1 := h46593c.2.1
                                have p46593_2 := h46593c.2.2.1
                                have p46593_3 := h46593c.2.2.2
                                linarith only [h46580, hlam, p46593_0]
                              · have p46593_0 := h46593c.1
                                have p46593_1 := h46593c.2.1
                                have p46593_2 := h46593c.2.2.1
                                have p46593_3 := h46593c.2.2.2
                                linarith only [h46583, hlam, p46593_1]
                              · have p46593_0 := h46593c.1
                                have p46593_1 := h46593c.2.1
                                have p46593_2 := h46593c.2.2.1
                                have p46593_3 := h46593c.2.2.2
                                linarith only [hlam, p46593_0]
                              · have p46593_0 := h46593c.1
                                have p46593_1 := h46593c.2.1
                                have p46593_2 := h46593c.2.2.1
                                have p46593_3 := h46593c.2.2.2
                                linarith only [h46585, hlam, p46593_1]
                              · have p46593_0 := h46593c.1
                                have p46593_1 := h46593c.2.1
                                have p46593_2 := h46593c.2.2.1
                                have p46593_3 := h46593c.2.2.2
                                rcases p46593_3 (m.d 0 1) (by simp) with h46618 | h46618
                                · linarith only [h46618, hlam, p46593_0]
                                · rcases p46593_3 (m.d 1 2) (by simp) with h46620 | h46620
                                  · linarith only [h46581, h46620, hlam]
                                  · linarith only [h0, h46620, hlam]
                              · have p46593_0 := h46593c.1
                                have p46593_1 := h46593c.2.1
                                have p46593_2 := h46593c.2.2.1
                                have p46593_3 := h46593c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p46593_1]
                              · have p46593_0 := h46593c.1
                                have p46593_1 := h46593c.2.1
                                have p46593_2 := h46593c.2.2.1
                                have p46593_3 := h46593c.2.2.2
                                linarith only [h46584, hlam, p46593_0]
                              · have p46593_0 := h46593c.1
                                have p46593_1 := h46593c.2.1
                                have p46593_2 := h46593c.2.2.1
                                have p46593_3 := h46593c.2.2.2
                                linarith only [h36828, h41027, h45992, h46319, h46550, h46581, h46584, h46587, h46589, hc01, hc23, hc34, hc45, hlam, hphi, ht12, p46593_1]
                              · have p46593_0 := h46593c.1
                                have p46593_1 := h46593c.2.1
                                have p46593_2 := h46593c.2.2.1
                                have p46593_3 := h46593c.2.2.2
                                linarith only [hlam, p46593_0]
                        · linarith only [h46550, h46584, h46588, hlam]
                      · linarith only [h41027, h45992, h46319, h46550, h46584, h46587, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h46629 | h46629
                    · linarith only [h36828, h46548, h46550, h46580, h46629, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h46631 | h46631
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h46632 | h46632
                        · linarith only [h33187, h46584, h46632, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h36828, h46550, h46580, h46632, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h36828, h46550, h46580, h46631, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h36828, h46318, h46550, h46580, h46583, hlam]
            · linarith only [h0, h45992, h46580, hlam]
    · linarith only [h41027, h45992, h46318, hlam]

end R2N4
