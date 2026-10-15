import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S22

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x1_x1_x1_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h10760 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h11236 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h11248 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h11249 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 4 5 (by decide) (by decide) with h12020 | h12020
  · linarith only [h12020, h2, h9, hlam]
  · rcases m.htr 2 3 4 (by decide) (by decide) with h12022 | h12022
    · rcases m.htr 2 3 5 (by decide) (by decide) with h12023 | h12023
      · linarith only [h11248, h11249, h12023, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h12025 | h12025
        · linarith only [h11248, h11249, h12022, h12023, h12025, h3, h8, h9, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h12027 | h12027
          · linarith only [h1, h11248, h12023, h12027, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases h1bigk with h12029c | h12029c | h12029c | h12029c | h12029c | h12029c | h12029c | h12029c | h12029c | h12029c | h12029c | h12029c | h12029c | h12029c | h12029c | h12029c | h12029c | h12029c | h12029c | h12029c | h12029c | h12029c | h12029c | h12029c | h12029c
            · have p12029_0 := h12029c.1
              have p12029_1 := h12029c.2.1
              have p12029_2 := h12029c.2.2.1
              have p12029_3 := h12029c.2.2.2
              linarith only [hlam, p12029_0]
            · have p12029_0 := h12029c.1
              have p12029_1 := h12029c.2.1
              have p12029_2 := h12029c.2.2.1
              have p12029_3 := h12029c.2.2.2
              linarith only [h0, h10760, h12022, h12023, h4, h8, hlam, p12029_2]
            · have p12029_0 := h12029c.1
              have p12029_1 := h12029c.2.1
              have p12029_2 := h12029c.2.2.1
              have p12029_3 := h12029c.2.2.2
              rcases p12029_3 (m.d 0 1) (by simp) with h12032 | h12032
              · rcases p12029_3 (m.d 1 2) (by simp) with h12033 | h12033
                · linarith only [h0, h12033, hlam]
                · rcases p12029_3 (m.d 1 3) (by simp) with h12035 | h12035
                  · linarith only [h12035, hlam, p12029_0]
                  · rcases p12029_3 (m.d 1 4) (by simp) with h12037 | h12037
                    · linarith only [h12037, h2, hlam]
                    · rcases p12029_3 (m.d 1 5) (by simp) with h12039 | h12039
                      · linarith only [h12039, h3, hlam]
                      · linarith only [h11249, h12039, hlam]
              · linarith only [h12032, hlam, p12029_0]
            · have p12029_0 := h12029c.1
              have p12029_1 := h12029c.2.1
              have p12029_2 := h12029c.2.2.1
              have p12029_3 := h12029c.2.2.2
              rcases p12029_3 (m.d 0 1) (by simp) with h12043 | h12043
              · rcases p12029_3 (m.d 1 2) (by simp) with h12044 | h12044
                · linarith only [h0, h12044, hlam]
                · rcases p12029_3 (m.d 1 3) (by simp) with h12046 | h12046
                  · linarith only [h1, h12046, hlam]
                  · linarith only [h11248, h12046, hlam]
              · linarith only [h12043, hlam, p12029_0]
            · have p12029_0 := h12029c.1
              have p12029_1 := h12029c.2.1
              have p12029_2 := h12029c.2.2.1
              have p12029_3 := h12029c.2.2.2
              rcases p12029_3 (m.d 0 1) (by simp) with h12050 | h12050
              · rcases p12029_3 (m.d 1 2) (by simp) with h12051 | h12051
                · linarith only [h0, h12051, hlam]
                · rcases p12029_3 (m.d 1 3) (by simp) with h12053 | h12053
                  · linarith only [h1, h12053, hlam]
                  · rcases p12029_3 (m.d 1 4) (by simp) with h12055 | h12055
                    · linarith only [h12055, h2, hlam]
                    · rcases p12029_3 (m.d 1 5) (by simp) with h12057 | h12057
                      · linarith only [h12057, hlam, p12029_0]
                      · rcases h1emax with h12059 | h12059 | h12059 | h12059 | h12059
                        · linarith only [h0, h10760, h12022, h12023, h12059, h4, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases h2bigk with h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c | h12061c
                          · have p12061_0 := h12061c.1
                            have p12061_1 := h12061c.2.1
                            have p12061_2 := h12061c.2.2.1
                            have p12061_3 := h12061c.2.2.2
                            linarith only [hlam, p12061_0]
                          · have p12061_0 := h12061c.1
                            have p12061_1 := h12061c.2.1
                            have p12061_2 := h12061c.2.2.1
                            have p12061_3 := h12061c.2.2.2
                            linarith only [h10760, h12022, h12023, h4, h8, hlam, p12061_2]
                          · have p12061_0 := h12061c.1
                            have p12061_1 := h12061c.2.1
                            have p12061_2 := h12061c.2.2.1
                            have p12061_3 := h12061c.2.2.2
                            rcases p12061_3 (m.d 0 2) (by simp) with h12064 | h12064
                            · rcases p12061_3 (m.d 1 2) (by simp) with h12065 | h12065
                              · linarith only [h0, h12065, hlam]
                              · rcases p12061_3 (m.d 2 3) (by simp) with h12067 | h12067
                                · linarith only [h12067, hlam, p12061_0]
                                · rcases p12061_3 (m.d 2 4) (by simp) with h12069 | h12069
                                  · linarith only [h12069, h5, hlam]
                                  · rcases p12061_3 (m.d 2 5) (by simp) with h12071 | h12071
                                    · linarith only [h12071, h6, hlam]
                                    · linarith only [h12023, h12071, hlam]
                            · linarith only [h12064, hlam, p12061_0]
                          · have p12061_0 := h12061c.1
                            have p12061_1 := h12061c.2.1
                            have p12061_2 := h12061c.2.2.1
                            have p12061_3 := h12061c.2.2.2
                            rcases p12061_3 (m.d 0 2) (by simp) with h12075 | h12075
                            · rcases p12061_3 (m.d 1 2) (by simp) with h12076 | h12076
                              · linarith only [h0, h12076, hlam]
                              · rcases p12061_3 (m.d 2 3) (by simp) with h12078 | h12078
                                · linarith only [h12078, h4, hlam]
                                · linarith only [h12022, h12078, hlam]
                            · linarith only [h12075, hlam, p12061_0]
                          · have p12061_0 := h12061c.1
                            have p12061_1 := h12061c.2.1
                            have p12061_2 := h12061c.2.2.1
                            have p12061_3 := h12061c.2.2.2
                            rcases p12061_3 (m.d 0 2) (by simp) with h12082 | h12082
                            · rcases p12061_3 (m.d 1 2) (by simp) with h12083 | h12083
                              · linarith only [h0, h12083, hlam]
                              · rcases p12061_3 (m.d 2 3) (by simp) with h12085 | h12085
                                · linarith only [h12085, h4, hlam]
                                · rcases p12061_3 (m.d 2 4) (by simp) with h12087 | h12087
                                  · linarith only [h12087, h5, hlam]
                                  · rcases p12061_3 (m.d 2 5) (by simp) with h12089 | h12089
                                    · linarith only [h12089, hlam, p12061_0]
                                    · rcases h4bigk with h12091c | h12091c | h12091c | h12091c | h12091c | h12091c | h12091c | h12091c | h12091c | h12091c | h12091c | h12091c | h12091c | h12091c | h12091c | h12091c | h12091c | h12091c | h12091c | h12091c | h12091c | h12091c | h12091c | h12091c | h12091c
                                      · have p12091_0 := h12091c.1
                                        have p12091_1 := h12091c.2.1
                                        have p12091_2 := h12091c.2.2.1
                                        have p12091_3 := h12091c.2.2.2
                                        linarith only [hlam, p12091_0]
                                      · have p12091_0 := h12091c.1
                                        have p12091_1 := h12091c.2.1
                                        have p12091_2 := h12091c.2.2.1
                                        have p12091_3 := h12091c.2.2.2
                                        linarith only [h9, hc14, hc45, hlam, hphi, p12091_1]
                                      · have p12091_0 := h12091c.1
                                        have p12091_1 := h12091c.2.1
                                        have p12091_2 := h12091c.2.2.1
                                        have p12091_3 := h12091c.2.2.2
                                        linarith only [h10760, h9, hc12, hc45, hlam, hphi, ht23, ht34, p12091_1]
                                      · have p12091_0 := h12091c.1
                                        have p12091_1 := h12091c.2.1
                                        have p12091_2 := h12091c.2.2.1
                                        have p12091_3 := h12091c.2.2.2
                                        linarith only [h9, hc34, hc45, hlam, hphi, p12091_1]
                                      · have p12091_0 := h12091c.1
                                        have p12091_1 := h12091c.2.1
                                        have p12091_2 := h12091c.2.2.1
                                        have p12091_3 := h12091c.2.2.2
                                        linarith only [h9, hlam, p12091_0]
                                      · have p12091_0 := h12091c.1
                                        have p12091_1 := h12091c.2.1
                                        have p12091_2 := h12091c.2.2.1
                                        have p12091_3 := h12091c.2.2.2
                                        linarith only [h2, hlam, p12091_0]
                                      · have p12091_0 := h12091c.1
                                        have p12091_1 := h12091c.2.1
                                        have p12091_2 := h12091c.2.2.1
                                        have p12091_3 := h12091c.2.2.2
                                        linarith only [hlam, p12091_0]
                                      · have p12091_0 := h12091c.1
                                        have p12091_1 := h12091c.2.1
                                        have p12091_2 := h12091c.2.2.1
                                        have p12091_3 := h12091c.2.2.2
                                        linarith only [h10760, hlam, p12091_1]
                                      · have p12091_0 := h12091c.1
                                        have p12091_1 := h12091c.2.1
                                        have p12091_2 := h12091c.2.2.1
                                        have p12091_3 := h12091c.2.2.2
                                        linarith only [h2, h9, hc34, hc45, hlam, hphi, p12091_1]
                                      · have p12091_0 := h12091c.1
                                        have p12091_1 := h12091c.2.1
                                        have p12091_2 := h12091c.2.2.1
                                        have p12091_3 := h12091c.2.2.2
                                        linarith only [h12020, hlam, p12091_0]
                                      · have p12091_0 := h12091c.1
                                        have p12091_1 := h12091c.2.1
                                        have p12091_2 := h12091c.2.2.1
                                        have p12091_3 := h12091c.2.2.2
                                        linarith only [h5, hlam, p12091_0]
                                      · have p12091_0 := h12091c.1
                                        have p12091_1 := h12091c.2.1
                                        have p12091_2 := h12091c.2.2.1
                                        have p12091_3 := h12091c.2.2.2
                                        linarith only [h0, h12022, h12023, h4, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p12091_1]
                                      · have p12091_0 := h12091c.1
                                        have p12091_1 := h12091c.2.1
                                        have p12091_2 := h12091c.2.2.1
                                        have p12091_3 := h12091c.2.2.2
                                        linarith only [hlam, p12091_0]
                                      · have p12091_0 := h12091c.1
                                        have p12091_1 := h12091c.2.1
                                        have p12091_2 := h12091c.2.2.1
                                        have p12091_3 := h12091c.2.2.2
                                        linarith only [h0, h12022, h12023, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p12091_1]
                                      · have p12091_0 := h12091c.1
                                        have p12091_1 := h12091c.2.1
                                        have p12091_2 := h12091c.2.2.1
                                        have p12091_3 := h12091c.2.2.2
                                        linarith only [h12025, hlam, p12091_0]
                                      · have p12091_0 := h12091c.1
                                        have p12091_1 := h12091c.2.1
                                        have p12091_2 := h12091c.2.2.1
                                        have p12091_3 := h12091c.2.2.2
                                        linarith only [h7, hlam, p12091_0]
                                      · have p12091_0 := h12091c.1
                                        have p12091_1 := h12091c.2.1
                                        have p12091_2 := h12091c.2.2.1
                                        have p12091_3 := h12091c.2.2.2
                                        linarith only [h11248, hlam, p12091_0]
                                      · have p12091_0 := h12091c.1
                                        have p12091_1 := h12091c.2.1
                                        have p12091_2 := h12091c.2.2.1
                                        have p12091_3 := h12091c.2.2.2
                                        linarith only [h12022, hlam, p12091_0]
                                      · have p12091_0 := h12091c.1
                                        have p12091_1 := h12091c.2.1
                                        have p12091_2 := h12091c.2.2.1
                                        have p12091_3 := h12091c.2.2.2
                                        linarith only [hlam, p12091_0]
                                      · have p12091_0 := h12091c.1
                                        have p12091_1 := h12091c.2.1
                                        have p12091_2 := h12091c.2.2.1
                                        have p12091_3 := h12091c.2.2.2
                                        linarith only [h12027, hlam, p12091_0]
                                      · have p12091_0 := h12091c.1
                                        have p12091_1 := h12091c.2.1
                                        have p12091_2 := h12091c.2.2.1
                                        have p12091_3 := h12091c.2.2.2
                                        linarith only [h10760, h5, hc12, hc45, hlam, hphi, ht23, ht34, p12091_1]
                                      · have p12091_0 := h12091c.1
                                        have p12091_1 := h12091c.2.1
                                        have p12091_2 := h12091c.2.2.1
                                        have p12091_3 := h12091c.2.2.2
                                        rcases p12091_3 (m.d 0 4) (by simp) with h12113 | h12113
                                        · linarith only [h12113, h9, hlam]
                                        · linarith only [h12113, h2, hlam]
                                      · have p12091_0 := h12091c.1
                                        have p12091_1 := h12091c.2.1
                                        have p12091_2 := h12091c.2.2.1
                                        have p12091_3 := h12091c.2.2.2
                                        linarith only [h10760, hc12, hc45, hlam, hphi, ht23, ht34, p12091_1]
                                      · have p12091_0 := h12091c.1
                                        have p12091_1 := h12091c.2.1
                                        have p12091_2 := h12091c.2.2.1
                                        have p12091_3 := h12091c.2.2.2
                                        rcases p12091_3 (m.d 0 4) (by simp) with h12117 | h12117
                                        · linarith only [h12117, h9, hlam]
                                        · linarith only [h12117, h7, hlam]
                                      · have p12091_0 := h12091c.1
                                        have p12091_1 := h12091c.2.1
                                        have p12091_2 := h12091c.2.2.1
                                        have p12091_3 := h12091c.2.2.2
                                        linarith only [hlam, p12091_0]
                            · linarith only [h12082, hlam, p12061_0]
                          · have p12061_0 := h12061c.1
                            have p12061_1 := h12061c.2.1
                            have p12061_2 := h12061c.2.2.1
                            have p12061_3 := h12061c.2.2.2
                            linarith only [h0, hlam, p12061_1]
                          · have p12061_0 := h12061c.1
                            have p12061_1 := h12061c.2.1
                            have p12061_2 := h12061c.2.2.1
                            have p12061_3 := h12061c.2.2.2
                            linarith only [hlam, p12061_0]
                          · have p12061_0 := h12061c.1
                            have p12061_1 := h12061c.2.1
                            have p12061_2 := h12061c.2.2.1
                            have p12061_3 := h12061c.2.2.2
                            linarith only [h9268, hlam, p12061_0]
                          · have p12061_0 := h12061c.1
                            have p12061_1 := h12061c.2.1
                            have p12061_2 := h12061c.2.2.1
                            have p12061_3 := h12061c.2.2.2
                            linarith only [h10760, hlam, p12061_0]
                          · have p12061_0 := h12061c.1
                            have p12061_1 := h12061c.2.1
                            have p12061_2 := h12061c.2.2.1
                            have p12061_3 := h12061c.2.2.2
                            linarith only [h11236, hlam, p12061_0]
                          · have p12061_0 := h12061c.1
                            have p12061_1 := h12061c.2.1
                            have p12061_2 := h12061c.2.2.1
                            have p12061_3 := h12061c.2.2.2
                            linarith only [h4, hlam, p12061_0]
                          · have p12061_0 := h12061c.1
                            have p12061_1 := h12061c.2.1
                            have p12061_2 := h12061c.2.2.1
                            have p12061_3 := h12061c.2.2.2
                            linarith only [h0, h12023, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12061_1]
                          · have p12061_0 := h12061c.1
                            have p12061_1 := h12061c.2.1
                            have p12061_2 := h12061c.2.2.1
                            have p12061_3 := h12061c.2.2.2
                            linarith only [hlam, p12061_0]
                          · have p12061_0 := h12061c.1
                            have p12061_1 := h12061c.2.1
                            have p12061_2 := h12061c.2.2.1
                            have p12061_3 := h12061c.2.2.2
                            linarith only [h0, h10760, h12023, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12061_1]
                          · have p12061_0 := h12061c.1
                            have p12061_1 := h12061c.2.1
                            have p12061_2 := h12061c.2.2.1
                            have p12061_3 := h12061c.2.2.2
                            linarith only [h12023, hlam, p12061_1]
                          · have p12061_0 := h12061c.1
                            have p12061_1 := h12061c.2.1
                            have p12061_2 := h12061c.2.2.1
                            have p12061_3 := h12061c.2.2.2
                            linarith only [h5, hlam, p12061_0]
                          · have p12061_0 := h12061c.1
                            have p12061_1 := h12061c.2.1
                            have p12061_2 := h12061c.2.2.1
                            have p12061_3 := h12061c.2.2.2
                            linarith only [h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p12061_1]
                          · have p12061_0 := h12061c.1
                            have p12061_1 := h12061c.2.1
                            have p12061_2 := h12061c.2.2.1
                            have p12061_3 := h12061c.2.2.2
                            linarith only [h12022, hlam, p12061_0]
                          · have p12061_0 := h12061c.1
                            have p12061_1 := h12061c.2.1
                            have p12061_2 := h12061c.2.2.1
                            have p12061_3 := h12061c.2.2.2
                            linarith only [hlam, p12061_0]
                          · have p12061_0 := h12061c.1
                            have p12061_1 := h12061c.2.1
                            have p12061_2 := h12061c.2.2.1
                            have p12061_3 := h12061c.2.2.2
                            linarith only [h12025, hlam, p12061_0]
                          · have p12061_0 := h12061c.1
                            have p12061_1 := h12061c.2.1
                            have p12061_2 := h12061c.2.2.1
                            have p12061_3 := h12061c.2.2.2
                            linarith only [h6, hlam, p12061_0]
                          · have p12061_0 := h12061c.1
                            have p12061_1 := h12061c.2.1
                            have p12061_2 := h12061c.2.2.1
                            have p12061_3 := h12061c.2.2.2
                            rcases p12061_3 (m.d 0 2) (by simp) with h12138 | h12138
                            · rcases p12061_3 (m.d 1 2) (by simp) with h12139 | h12139
                              · linarith only [h12139, hlam, p12061_0]
                              · rcases p12061_3 (m.d 2 3) (by simp) with h12141 | h12141
                                · linarith only [h12023, h12141, hlam]
                                · linarith only [h12141, h9268, hlam]
                            · linarith only [h0, h12138, hlam]
                          · have p12061_0 := h12061c.1
                            have p12061_1 := h12061c.2.1
                            have p12061_2 := h12061c.2.2.1
                            have p12061_3 := h12061c.2.2.2
                            linarith only [h0, h6, h9268, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12061_1]
                          · have p12061_0 := h12061c.1
                            have p12061_1 := h12061c.2.1
                            have p12061_2 := h12061c.2.2.1
                            have p12061_3 := h12061c.2.2.2
                            linarith only [h0, h10760, h12023, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12061_1]
                          · have p12061_0 := h12061c.1
                            have p12061_1 := h12061c.2.1
                            have p12061_2 := h12061c.2.2.1
                            have p12061_3 := h12061c.2.2.2
                            linarith only [hlam, p12061_0]
                        · rcases h2bigk with h12148c | h12148c | h12148c | h12148c | h12148c | h12148c | h12148c | h12148c | h12148c | h12148c | h12148c | h12148c | h12148c | h12148c | h12148c | h12148c | h12148c | h12148c | h12148c | h12148c | h12148c | h12148c | h12148c | h12148c | h12148c
                          · have p12148_0 := h12148c.1
                            have p12148_1 := h12148c.2.1
                            have p12148_2 := h12148c.2.2.1
                            have p12148_3 := h12148c.2.2.2
                            linarith only [hlam, p12148_0]
                          · have p12148_0 := h12148c.1
                            have p12148_1 := h12148c.2.1
                            have p12148_2 := h12148c.2.2.1
                            have p12148_3 := h12148c.2.2.2
                            linarith only [h10760, h12022, h12023, h4, h8, hlam, p12148_2]
                          · have p12148_0 := h12148c.1
                            have p12148_1 := h12148c.2.1
                            have p12148_2 := h12148c.2.2.1
                            have p12148_3 := h12148c.2.2.2
                            rcases p12148_3 (m.d 0 2) (by simp) with h12151 | h12151
                            · rcases p12148_3 (m.d 1 2) (by simp) with h12152 | h12152
                              · linarith only [h0, h12152, hlam]
                              · rcases p12148_3 (m.d 2 3) (by simp) with h12154 | h12154
                                · linarith only [h12154, hlam, p12148_0]
                                · rcases p12148_3 (m.d 2 4) (by simp) with h12156 | h12156
                                  · linarith only [h12156, h5, hlam]
                                  · rcases p12148_3 (m.d 2 5) (by simp) with h12158 | h12158
                                    · linarith only [h12158, h6, hlam]
                                    · linarith only [h12023, h12158, hlam]
                            · linarith only [h12151, hlam, p12148_0]
                          · have p12148_0 := h12148c.1
                            have p12148_1 := h12148c.2.1
                            have p12148_2 := h12148c.2.2.1
                            have p12148_3 := h12148c.2.2.2
                            rcases p12148_3 (m.d 0 2) (by simp) with h12162 | h12162
                            · rcases p12148_3 (m.d 1 2) (by simp) with h12163 | h12163
                              · linarith only [h0, h12163, hlam]
                              · rcases p12148_3 (m.d 2 3) (by simp) with h12165 | h12165
                                · linarith only [h12165, h4, hlam]
                                · linarith only [h12022, h12165, hlam]
                            · linarith only [h12162, hlam, p12148_0]
                          · have p12148_0 := h12148c.1
                            have p12148_1 := h12148c.2.1
                            have p12148_2 := h12148c.2.2.1
                            have p12148_3 := h12148c.2.2.2
                            rcases p12148_3 (m.d 0 2) (by simp) with h12169 | h12169
                            · rcases p12148_3 (m.d 1 2) (by simp) with h12170 | h12170
                              · linarith only [h0, h12170, hlam]
                              · rcases p12148_3 (m.d 2 3) (by simp) with h12172 | h12172
                                · linarith only [h12172, h4, hlam]
                                · rcases p12148_3 (m.d 2 4) (by simp) with h12174 | h12174
                                  · linarith only [h12174, h5, hlam]
                                  · rcases p12148_3 (m.d 2 5) (by simp) with h12176 | h12176
                                    · linarith only [h12176, hlam, p12148_0]
                                    · rcases h4bigk with h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c | h12178c
                                      · have p12178_0 := h12178c.1
                                        have p12178_1 := h12178c.2.1
                                        have p12178_2 := h12178c.2.2.1
                                        have p12178_3 := h12178c.2.2.2
                                        linarith only [hlam, p12178_0]
                                      · have p12178_0 := h12178c.1
                                        have p12178_1 := h12178c.2.1
                                        have p12178_2 := h12178c.2.2.1
                                        have p12178_3 := h12178c.2.2.2
                                        linarith only [h10760, h9, hc12, hc45, hlam, hphi, ht23, ht34, p12178_1]
                                      · have p12178_0 := h12178c.1
                                        have p12178_1 := h12178c.2.1
                                        have p12178_2 := h12178c.2.2.1
                                        have p12178_3 := h12178c.2.2.2
                                        linarith only [h10760, h9, hc12, hc45, hlam, hphi, ht23, ht34, p12178_1]
                                      · have p12178_0 := h12178c.1
                                        have p12178_1 := h12178c.2.1
                                        have p12178_2 := h12178c.2.2.1
                                        have p12178_3 := h12178c.2.2.2
                                        linarith only [h9, hc34, hc45, hlam, hphi, p12178_1]
                                      · have p12178_0 := h12178c.1
                                        have p12178_1 := h12178c.2.1
                                        have p12178_2 := h12178c.2.2.1
                                        have p12178_3 := h12178c.2.2.2
                                        linarith only [h9, hlam, p12178_0]
                                      · have p12178_0 := h12178c.1
                                        have p12178_1 := h12178c.2.1
                                        have p12178_2 := h12178c.2.2.1
                                        have p12178_3 := h12178c.2.2.2
                                        linarith only [h2, hlam, p12178_0]
                                      · have p12178_0 := h12178c.1
                                        have p12178_1 := h12178c.2.1
                                        have p12178_2 := h12178c.2.2.1
                                        have p12178_3 := h12178c.2.2.2
                                        linarith only [hlam, p12178_0]
                                      · have p12178_0 := h12178c.1
                                        have p12178_1 := h12178c.2.1
                                        have p12178_2 := h12178c.2.2.1
                                        have p12178_3 := h12178c.2.2.2
                                        linarith only [h10760, hlam, p12178_1]
                                      · have p12178_0 := h12178c.1
                                        have p12178_1 := h12178c.2.1
                                        have p12178_2 := h12178c.2.2.1
                                        have p12178_3 := h12178c.2.2.2
                                        linarith only [h2, h9, hc34, hc45, hlam, hphi, p12178_1]
                                      · have p12178_0 := h12178c.1
                                        have p12178_1 := h12178c.2.1
                                        have p12178_2 := h12178c.2.2.1
                                        have p12178_3 := h12178c.2.2.2
                                        linarith only [h12020, hlam, p12178_0]
                                      · have p12178_0 := h12178c.1
                                        have p12178_1 := h12178c.2.1
                                        have p12178_2 := h12178c.2.2.1
                                        have p12178_3 := h12178c.2.2.2
                                        linarith only [h5, hlam, p12178_0]
                                      · have p12178_0 := h12178c.1
                                        have p12178_1 := h12178c.2.1
                                        have p12178_2 := h12178c.2.2.1
                                        have p12178_3 := h12178c.2.2.2
                                        linarith only [h12022, h12023, h4, h8, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p12178_1]
                                      · have p12178_0 := h12178c.1
                                        have p12178_1 := h12178c.2.1
                                        have p12178_2 := h12178c.2.2.1
                                        have p12178_3 := h12178c.2.2.2
                                        linarith only [hlam, p12178_0]
                                      · have p12178_0 := h12178c.1
                                        have p12178_1 := h12178c.2.1
                                        have p12178_2 := h12178c.2.2.1
                                        have p12178_3 := h12178c.2.2.2
                                        linarith only [h0, h12022, h12023, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p12178_1]
                                      · have p12178_0 := h12178c.1
                                        have p12178_1 := h12178c.2.1
                                        have p12178_2 := h12178c.2.2.1
                                        have p12178_3 := h12178c.2.2.2
                                        linarith only [h12025, hlam, p12178_0]
                                      · have p12178_0 := h12178c.1
                                        have p12178_1 := h12178c.2.1
                                        have p12178_2 := h12178c.2.2.1
                                        have p12178_3 := h12178c.2.2.2
                                        linarith only [h7, hlam, p12178_0]
                                      · have p12178_0 := h12178c.1
                                        have p12178_1 := h12178c.2.1
                                        have p12178_2 := h12178c.2.2.1
                                        have p12178_3 := h12178c.2.2.2
                                        linarith only [h11248, hlam, p12178_0]
                                      · have p12178_0 := h12178c.1
                                        have p12178_1 := h12178c.2.1
                                        have p12178_2 := h12178c.2.2.1
                                        have p12178_3 := h12178c.2.2.2
                                        linarith only [h12022, hlam, p12178_0]
                                      · have p12178_0 := h12178c.1
                                        have p12178_1 := h12178c.2.1
                                        have p12178_2 := h12178c.2.2.1
                                        have p12178_3 := h12178c.2.2.2
                                        linarith only [hlam, p12178_0]
                                      · have p12178_0 := h12178c.1
                                        have p12178_1 := h12178c.2.1
                                        have p12178_2 := h12178c.2.2.1
                                        have p12178_3 := h12178c.2.2.2
                                        linarith only [h12027, hlam, p12178_0]
                                      · have p12178_0 := h12178c.1
                                        have p12178_1 := h12178c.2.1
                                        have p12178_2 := h12178c.2.2.1
                                        have p12178_3 := h12178c.2.2.2
                                        linarith only [h10760, h5, hc12, hc45, hlam, hphi, ht23, ht34, p12178_1]
                                      · have p12178_0 := h12178c.1
                                        have p12178_1 := h12178c.2.1
                                        have p12178_2 := h12178c.2.2.1
                                        have p12178_3 := h12178c.2.2.2
                                        rcases p12178_3 (m.d 0 4) (by simp) with h12200 | h12200
                                        · linarith only [h12200, h9, hlam]
                                        · linarith only [h12200, h2, hlam]
                                      · have p12178_0 := h12178c.1
                                        have p12178_1 := h12178c.2.1
                                        have p12178_2 := h12178c.2.2.1
                                        have p12178_3 := h12178c.2.2.2
                                        linarith only [h10760, hc12, hc45, hlam, hphi, ht23, ht34, p12178_1]
                                      · have p12178_0 := h12178c.1
                                        have p12178_1 := h12178c.2.1
                                        have p12178_2 := h12178c.2.2.1
                                        have p12178_3 := h12178c.2.2.2
                                        rcases p12178_3 (m.d 0 4) (by simp) with h12204 | h12204
                                        · linarith only [h12204, h9, hlam]
                                        · linarith only [h12204, h7, hlam]
                                      · have p12178_0 := h12178c.1
                                        have p12178_1 := h12178c.2.1
                                        have p12178_2 := h12178c.2.2.1
                                        have p12178_3 := h12178c.2.2.2
                                        linarith only [hlam, p12178_0]
                            · linarith only [h12169, hlam, p12148_0]
                          · have p12148_0 := h12148c.1
                            have p12148_1 := h12148c.2.1
                            have p12148_2 := h12148c.2.2.1
                            have p12148_3 := h12148c.2.2.2
                            linarith only [h0, hlam, p12148_1]
                          · have p12148_0 := h12148c.1
                            have p12148_1 := h12148c.2.1
                            have p12148_2 := h12148c.2.2.1
                            have p12148_3 := h12148c.2.2.2
                            linarith only [hlam, p12148_0]
                          · have p12148_0 := h12148c.1
                            have p12148_1 := h12148c.2.1
                            have p12148_2 := h12148c.2.2.1
                            have p12148_3 := h12148c.2.2.2
                            linarith only [h9268, hlam, p12148_0]
                          · have p12148_0 := h12148c.1
                            have p12148_1 := h12148c.2.1
                            have p12148_2 := h12148c.2.2.1
                            have p12148_3 := h12148c.2.2.2
                            linarith only [h10760, hlam, p12148_0]
                          · have p12148_0 := h12148c.1
                            have p12148_1 := h12148c.2.1
                            have p12148_2 := h12148c.2.2.1
                            have p12148_3 := h12148c.2.2.2
                            linarith only [h11236, hlam, p12148_0]
                          · have p12148_0 := h12148c.1
                            have p12148_1 := h12148c.2.1
                            have p12148_2 := h12148c.2.2.1
                            have p12148_3 := h12148c.2.2.2
                            linarith only [h4, hlam, p12148_0]
                          · have p12148_0 := h12148c.1
                            have p12148_1 := h12148c.2.1
                            have p12148_2 := h12148c.2.2.1
                            have p12148_3 := h12148c.2.2.2
                            linarith only [h0, h12023, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12148_1]
                          · have p12148_0 := h12148c.1
                            have p12148_1 := h12148c.2.1
                            have p12148_2 := h12148c.2.2.1
                            have p12148_3 := h12148c.2.2.2
                            linarith only [hlam, p12148_0]
                          · have p12148_0 := h12148c.1
                            have p12148_1 := h12148c.2.1
                            have p12148_2 := h12148c.2.2.1
                            have p12148_3 := h12148c.2.2.2
                            linarith only [h0, h10760, h12023, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12148_1]
                          · have p12148_0 := h12148c.1
                            have p12148_1 := h12148c.2.1
                            have p12148_2 := h12148c.2.2.1
                            have p12148_3 := h12148c.2.2.2
                            linarith only [h12023, hlam, p12148_1]
                          · have p12148_0 := h12148c.1
                            have p12148_1 := h12148c.2.1
                            have p12148_2 := h12148c.2.2.1
                            have p12148_3 := h12148c.2.2.2
                            linarith only [h5, hlam, p12148_0]
                          · have p12148_0 := h12148c.1
                            have p12148_1 := h12148c.2.1
                            have p12148_2 := h12148c.2.2.1
                            have p12148_3 := h12148c.2.2.2
                            linarith only [h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p12148_1]
                          · have p12148_0 := h12148c.1
                            have p12148_1 := h12148c.2.1
                            have p12148_2 := h12148c.2.2.1
                            have p12148_3 := h12148c.2.2.2
                            linarith only [h12022, hlam, p12148_0]
                          · have p12148_0 := h12148c.1
                            have p12148_1 := h12148c.2.1
                            have p12148_2 := h12148c.2.2.1
                            have p12148_3 := h12148c.2.2.2
                            linarith only [hlam, p12148_0]
                          · have p12148_0 := h12148c.1
                            have p12148_1 := h12148c.2.1
                            have p12148_2 := h12148c.2.2.1
                            have p12148_3 := h12148c.2.2.2
                            linarith only [h12025, hlam, p12148_0]
                          · have p12148_0 := h12148c.1
                            have p12148_1 := h12148c.2.1
                            have p12148_2 := h12148c.2.2.1
                            have p12148_3 := h12148c.2.2.2
                            linarith only [h6, hlam, p12148_0]
                          · have p12148_0 := h12148c.1
                            have p12148_1 := h12148c.2.1
                            have p12148_2 := h12148c.2.2.1
                            have p12148_3 := h12148c.2.2.2
                            rcases p12148_3 (m.d 0 2) (by simp) with h12225 | h12225
                            · rcases p12148_3 (m.d 1 2) (by simp) with h12226 | h12226
                              · linarith only [h12226, hlam, p12148_0]
                              · rcases p12148_3 (m.d 2 3) (by simp) with h12228 | h12228
                                · linarith only [h12023, h12228, hlam]
                                · linarith only [h12228, h9268, hlam]
                            · linarith only [h0, h12225, hlam]
                          · have p12148_0 := h12148c.1
                            have p12148_1 := h12148c.2.1
                            have p12148_2 := h12148c.2.2.1
                            have p12148_3 := h12148c.2.2.2
                            linarith only [h0, h6, h9268, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12148_1]
                          · have p12148_0 := h12148c.1
                            have p12148_1 := h12148c.2.1
                            have p12148_2 := h12148c.2.2.1
                            have p12148_3 := h12148c.2.2.2
                            linarith only [h0, h10760, h12023, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12148_1]
                          · have p12148_0 := h12148c.1
                            have p12148_1 := h12148c.2.1
                            have p12148_2 := h12148c.2.2.1
                            have p12148_3 := h12148c.2.2.2
                            linarith only [hlam, p12148_0]
                        · rcases h2bigk with h12235c | h12235c | h12235c | h12235c | h12235c | h12235c | h12235c | h12235c | h12235c | h12235c | h12235c | h12235c | h12235c | h12235c | h12235c | h12235c | h12235c | h12235c | h12235c | h12235c | h12235c | h12235c | h12235c | h12235c | h12235c
                          · have p12235_0 := h12235c.1
                            have p12235_1 := h12235c.2.1
                            have p12235_2 := h12235c.2.2.1
                            have p12235_3 := h12235c.2.2.2
                            linarith only [hlam, p12235_0]
                          · have p12235_0 := h12235c.1
                            have p12235_1 := h12235c.2.1
                            have p12235_2 := h12235c.2.2.1
                            have p12235_3 := h12235c.2.2.2
                            linarith only [h10760, h12022, h12023, h4, h8, hlam, p12235_2]
                          · have p12235_0 := h12235c.1
                            have p12235_1 := h12235c.2.1
                            have p12235_2 := h12235c.2.2.1
                            have p12235_3 := h12235c.2.2.2
                            rcases p12235_3 (m.d 0 2) (by simp) with h12238 | h12238
                            · rcases p12235_3 (m.d 1 2) (by simp) with h12239 | h12239
                              · linarith only [h0, h12239, hlam]
                              · rcases p12235_3 (m.d 2 3) (by simp) with h12241 | h12241
                                · linarith only [h12241, hlam, p12235_0]
                                · rcases p12235_3 (m.d 2 4) (by simp) with h12243 | h12243
                                  · linarith only [h12243, h5, hlam]
                                  · rcases p12235_3 (m.d 2 5) (by simp) with h12245 | h12245
                                    · linarith only [h12245, h6, hlam]
                                    · linarith only [h12023, h12245, hlam]
                            · linarith only [h12238, hlam, p12235_0]
                          · have p12235_0 := h12235c.1
                            have p12235_1 := h12235c.2.1
                            have p12235_2 := h12235c.2.2.1
                            have p12235_3 := h12235c.2.2.2
                            rcases p12235_3 (m.d 0 2) (by simp) with h12249 | h12249
                            · rcases p12235_3 (m.d 1 2) (by simp) with h12250 | h12250
                              · linarith only [h0, h12250, hlam]
                              · rcases p12235_3 (m.d 2 3) (by simp) with h12252 | h12252
                                · linarith only [h12252, h4, hlam]
                                · linarith only [h12022, h12252, hlam]
                            · linarith only [h12249, hlam, p12235_0]
                          · have p12235_0 := h12235c.1
                            have p12235_1 := h12235c.2.1
                            have p12235_2 := h12235c.2.2.1
                            have p12235_3 := h12235c.2.2.2
                            rcases p12235_3 (m.d 0 2) (by simp) with h12256 | h12256
                            · rcases p12235_3 (m.d 1 2) (by simp) with h12257 | h12257
                              · linarith only [h0, h12257, hlam]
                              · rcases p12235_3 (m.d 2 3) (by simp) with h12259 | h12259
                                · linarith only [h12259, h4, hlam]
                                · rcases p12235_3 (m.d 2 4) (by simp) with h12261 | h12261
                                  · linarith only [h12261, h5, hlam]
                                  · rcases p12235_3 (m.d 2 5) (by simp) with h12263 | h12263
                                    · linarith only [h12263, hlam, p12235_0]
                                    · rcases h4bigk with h12265c | h12265c | h12265c | h12265c | h12265c | h12265c | h12265c | h12265c | h12265c | h12265c | h12265c | h12265c | h12265c | h12265c | h12265c | h12265c | h12265c | h12265c | h12265c | h12265c | h12265c | h12265c | h12265c | h12265c | h12265c
                                      · have p12265_0 := h12265c.1
                                        have p12265_1 := h12265c.2.1
                                        have p12265_2 := h12265c.2.2.1
                                        have p12265_3 := h12265c.2.2.2
                                        linarith only [hlam, p12265_0]
                                      · have p12265_0 := h12265c.1
                                        have p12265_1 := h12265c.2.1
                                        have p12265_2 := h12265c.2.2.1
                                        have p12265_3 := h12265c.2.2.2
                                        linarith only [h10760, h9, hc12, hc45, hlam, hphi, ht23, ht34, p12265_1]
                                      · have p12265_0 := h12265c.1
                                        have p12265_1 := h12265c.2.1
                                        have p12265_2 := h12265c.2.2.1
                                        have p12265_3 := h12265c.2.2.2
                                        linarith only [h10760, h9, hc12, hc45, hlam, hphi, ht23, ht34, p12265_1]
                                      · have p12265_0 := h12265c.1
                                        have p12265_1 := h12265c.2.1
                                        have p12265_2 := h12265c.2.2.1
                                        have p12265_3 := h12265c.2.2.2
                                        linarith only [h9, hc34, hc45, hlam, hphi, p12265_1]
                                      · have p12265_0 := h12265c.1
                                        have p12265_1 := h12265c.2.1
                                        have p12265_2 := h12265c.2.2.1
                                        have p12265_3 := h12265c.2.2.2
                                        linarith only [h9, hlam, p12265_0]
                                      · have p12265_0 := h12265c.1
                                        have p12265_1 := h12265c.2.1
                                        have p12265_2 := h12265c.2.2.1
                                        have p12265_3 := h12265c.2.2.2
                                        linarith only [h2, hlam, p12265_0]
                                      · have p12265_0 := h12265c.1
                                        have p12265_1 := h12265c.2.1
                                        have p12265_2 := h12265c.2.2.1
                                        have p12265_3 := h12265c.2.2.2
                                        linarith only [hlam, p12265_0]
                                      · have p12265_0 := h12265c.1
                                        have p12265_1 := h12265c.2.1
                                        have p12265_2 := h12265c.2.2.1
                                        have p12265_3 := h12265c.2.2.2
                                        linarith only [h10760, hlam, p12265_1]
                                      · have p12265_0 := h12265c.1
                                        have p12265_1 := h12265c.2.1
                                        have p12265_2 := h12265c.2.2.1
                                        have p12265_3 := h12265c.2.2.2
                                        linarith only [h2, h9, hc34, hc45, hlam, hphi, p12265_1]
                                      · have p12265_0 := h12265c.1
                                        have p12265_1 := h12265c.2.1
                                        have p12265_2 := h12265c.2.2.1
                                        have p12265_3 := h12265c.2.2.2
                                        linarith only [h12020, hlam, p12265_0]
                                      · have p12265_0 := h12265c.1
                                        have p12265_1 := h12265c.2.1
                                        have p12265_2 := h12265c.2.2.1
                                        have p12265_3 := h12265c.2.2.2
                                        linarith only [h5, hlam, p12265_0]
                                      · have p12265_0 := h12265c.1
                                        have p12265_1 := h12265c.2.1
                                        have p12265_2 := h12265c.2.2.1
                                        have p12265_3 := h12265c.2.2.2
                                        linarith only [h12022, h12023, h4, h8, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b, p12265_1]
                                      · have p12265_0 := h12265c.1
                                        have p12265_1 := h12265c.2.1
                                        have p12265_2 := h12265c.2.2.1
                                        have p12265_3 := h12265c.2.2.2
                                        linarith only [hlam, p12265_0]
                                      · have p12265_0 := h12265c.1
                                        have p12265_1 := h12265c.2.1
                                        have p12265_2 := h12265c.2.2.1
                                        have p12265_3 := h12265c.2.2.2
                                        linarith only [h0, h12022, h12023, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p12265_1]
                                      · have p12265_0 := h12265c.1
                                        have p12265_1 := h12265c.2.1
                                        have p12265_2 := h12265c.2.2.1
                                        have p12265_3 := h12265c.2.2.2
                                        linarith only [h12025, hlam, p12265_0]
                                      · have p12265_0 := h12265c.1
                                        have p12265_1 := h12265c.2.1
                                        have p12265_2 := h12265c.2.2.1
                                        have p12265_3 := h12265c.2.2.2
                                        linarith only [h7, hlam, p12265_0]
                                      · have p12265_0 := h12265c.1
                                        have p12265_1 := h12265c.2.1
                                        have p12265_2 := h12265c.2.2.1
                                        have p12265_3 := h12265c.2.2.2
                                        linarith only [h11248, hlam, p12265_0]
                                      · have p12265_0 := h12265c.1
                                        have p12265_1 := h12265c.2.1
                                        have p12265_2 := h12265c.2.2.1
                                        have p12265_3 := h12265c.2.2.2
                                        linarith only [h12022, hlam, p12265_0]
                                      · have p12265_0 := h12265c.1
                                        have p12265_1 := h12265c.2.1
                                        have p12265_2 := h12265c.2.2.1
                                        have p12265_3 := h12265c.2.2.2
                                        linarith only [hlam, p12265_0]
                                      · have p12265_0 := h12265c.1
                                        have p12265_1 := h12265c.2.1
                                        have p12265_2 := h12265c.2.2.1
                                        have p12265_3 := h12265c.2.2.2
                                        linarith only [h12027, hlam, p12265_0]
                                      · have p12265_0 := h12265c.1
                                        have p12265_1 := h12265c.2.1
                                        have p12265_2 := h12265c.2.2.1
                                        have p12265_3 := h12265c.2.2.2
                                        linarith only [h10760, h5, hc12, hc45, hlam, hphi, ht23, ht34, p12265_1]
                                      · have p12265_0 := h12265c.1
                                        have p12265_1 := h12265c.2.1
                                        have p12265_2 := h12265c.2.2.1
                                        have p12265_3 := h12265c.2.2.2
                                        rcases p12265_3 (m.d 0 4) (by simp) with h12287 | h12287
                                        · linarith only [h12287, h9, hlam]
                                        · linarith only [h12287, h2, hlam]
                                      · have p12265_0 := h12265c.1
                                        have p12265_1 := h12265c.2.1
                                        have p12265_2 := h12265c.2.2.1
                                        have p12265_3 := h12265c.2.2.2
                                        linarith only [h10760, hc12, hc45, hlam, hphi, ht23, ht34, p12265_1]
                                      · have p12265_0 := h12265c.1
                                        have p12265_1 := h12265c.2.1
                                        have p12265_2 := h12265c.2.2.1
                                        have p12265_3 := h12265c.2.2.2
                                        rcases p12265_3 (m.d 0 4) (by simp) with h12291 | h12291
                                        · linarith only [h12291, h9, hlam]
                                        · linarith only [h12291, h7, hlam]
                                      · have p12265_0 := h12265c.1
                                        have p12265_1 := h12265c.2.1
                                        have p12265_2 := h12265c.2.2.1
                                        have p12265_3 := h12265c.2.2.2
                                        linarith only [hlam, p12265_0]
                            · linarith only [h12256, hlam, p12235_0]
                          · have p12235_0 := h12235c.1
                            have p12235_1 := h12235c.2.1
                            have p12235_2 := h12235c.2.2.1
                            have p12235_3 := h12235c.2.2.2
                            linarith only [h0, hlam, p12235_1]
                          · have p12235_0 := h12235c.1
                            have p12235_1 := h12235c.2.1
                            have p12235_2 := h12235c.2.2.1
                            have p12235_3 := h12235c.2.2.2
                            linarith only [hlam, p12235_0]
                          · have p12235_0 := h12235c.1
                            have p12235_1 := h12235c.2.1
                            have p12235_2 := h12235c.2.2.1
                            have p12235_3 := h12235c.2.2.2
                            linarith only [h9268, hlam, p12235_0]
                          · have p12235_0 := h12235c.1
                            have p12235_1 := h12235c.2.1
                            have p12235_2 := h12235c.2.2.1
                            have p12235_3 := h12235c.2.2.2
                            linarith only [h10760, hlam, p12235_0]
                          · have p12235_0 := h12235c.1
                            have p12235_1 := h12235c.2.1
                            have p12235_2 := h12235c.2.2.1
                            have p12235_3 := h12235c.2.2.2
                            linarith only [h11236, hlam, p12235_0]
                          · have p12235_0 := h12235c.1
                            have p12235_1 := h12235c.2.1
                            have p12235_2 := h12235c.2.2.1
                            have p12235_3 := h12235c.2.2.2
                            linarith only [h4, hlam, p12235_0]
                          · have p12235_0 := h12235c.1
                            have p12235_1 := h12235c.2.1
                            have p12235_2 := h12235c.2.2.1
                            have p12235_3 := h12235c.2.2.2
                            linarith only [h0, h12023, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12235_1]
                          · have p12235_0 := h12235c.1
                            have p12235_1 := h12235c.2.1
                            have p12235_2 := h12235c.2.2.1
                            have p12235_3 := h12235c.2.2.2
                            linarith only [hlam, p12235_0]
                          · have p12235_0 := h12235c.1
                            have p12235_1 := h12235c.2.1
                            have p12235_2 := h12235c.2.2.1
                            have p12235_3 := h12235c.2.2.2
                            linarith only [h0, h10760, h12023, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12235_1]
                          · have p12235_0 := h12235c.1
                            have p12235_1 := h12235c.2.1
                            have p12235_2 := h12235c.2.2.1
                            have p12235_3 := h12235c.2.2.2
                            linarith only [h12023, hlam, p12235_1]
                          · have p12235_0 := h12235c.1
                            have p12235_1 := h12235c.2.1
                            have p12235_2 := h12235c.2.2.1
                            have p12235_3 := h12235c.2.2.2
                            linarith only [h5, hlam, p12235_0]
                          · have p12235_0 := h12235c.1
                            have p12235_1 := h12235c.2.1
                            have p12235_2 := h12235c.2.2.1
                            have p12235_3 := h12235c.2.2.2
                            linarith only [h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p12235_1]
                          · have p12235_0 := h12235c.1
                            have p12235_1 := h12235c.2.1
                            have p12235_2 := h12235c.2.2.1
                            have p12235_3 := h12235c.2.2.2
                            linarith only [h12022, hlam, p12235_0]
                          · have p12235_0 := h12235c.1
                            have p12235_1 := h12235c.2.1
                            have p12235_2 := h12235c.2.2.1
                            have p12235_3 := h12235c.2.2.2
                            linarith only [hlam, p12235_0]
                          · have p12235_0 := h12235c.1
                            have p12235_1 := h12235c.2.1
                            have p12235_2 := h12235c.2.2.1
                            have p12235_3 := h12235c.2.2.2
                            linarith only [h12025, hlam, p12235_0]
                          · have p12235_0 := h12235c.1
                            have p12235_1 := h12235c.2.1
                            have p12235_2 := h12235c.2.2.1
                            have p12235_3 := h12235c.2.2.2
                            linarith only [h6, hlam, p12235_0]
                          · have p12235_0 := h12235c.1
                            have p12235_1 := h12235c.2.1
                            have p12235_2 := h12235c.2.2.1
                            have p12235_3 := h12235c.2.2.2
                            rcases p12235_3 (m.d 0 2) (by simp) with h12312 | h12312
                            · rcases p12235_3 (m.d 1 2) (by simp) with h12313 | h12313
                              · linarith only [h12313, hlam, p12235_0]
                              · rcases p12235_3 (m.d 2 3) (by simp) with h12315 | h12315
                                · linarith only [h12023, h12315, hlam]
                                · linarith only [h12315, h9268, hlam]
                            · linarith only [h0, h12312, hlam]
                          · have p12235_0 := h12235c.1
                            have p12235_1 := h12235c.2.1
                            have p12235_2 := h12235c.2.2.1
                            have p12235_3 := h12235c.2.2.2
                            linarith only [h0, h6, h9268, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12235_1]
                          · have p12235_0 := h12235c.1
                            have p12235_1 := h12235c.2.1
                            have p12235_2 := h12235c.2.2.1
                            have p12235_3 := h12235c.2.2.2
                            linarith only [h0, h10760, h12023, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12235_1]
                          · have p12235_0 := h12235c.1
                            have p12235_1 := h12235c.2.1
                            have p12235_2 := h12235c.2.2.1
                            have p12235_3 := h12235c.2.2.2
                            linarith only [hlam, p12235_0]
                        · rcases h2bigk with h12322c | h12322c | h12322c | h12322c | h12322c | h12322c | h12322c | h12322c | h12322c | h12322c | h12322c | h12322c | h12322c | h12322c | h12322c | h12322c | h12322c | h12322c | h12322c | h12322c | h12322c | h12322c | h12322c | h12322c | h12322c
                          · have p12322_0 := h12322c.1
                            have p12322_1 := h12322c.2.1
                            have p12322_2 := h12322c.2.2.1
                            have p12322_3 := h12322c.2.2.2
                            linarith only [hlam, p12322_0]
                          · have p12322_0 := h12322c.1
                            have p12322_1 := h12322c.2.1
                            have p12322_2 := h12322c.2.2.1
                            have p12322_3 := h12322c.2.2.2
                            linarith only [h10760, h12022, h12023, h4, h8, hlam, p12322_2]
                          · have p12322_0 := h12322c.1
                            have p12322_1 := h12322c.2.1
                            have p12322_2 := h12322c.2.2.1
                            have p12322_3 := h12322c.2.2.2
                            rcases p12322_3 (m.d 0 2) (by simp) with h12325 | h12325
                            · rcases p12322_3 (m.d 1 2) (by simp) with h12326 | h12326
                              · linarith only [h0, h12326, hlam]
                              · rcases p12322_3 (m.d 2 3) (by simp) with h12328 | h12328
                                · linarith only [h12328, hlam, p12322_0]
                                · rcases p12322_3 (m.d 2 4) (by simp) with h12330 | h12330
                                  · linarith only [h12330, h5, hlam]
                                  · rcases p12322_3 (m.d 2 5) (by simp) with h12332 | h12332
                                    · linarith only [h12332, h6, hlam]
                                    · linarith only [h12023, h12332, hlam]
                            · linarith only [h12325, hlam, p12322_0]
                          · have p12322_0 := h12322c.1
                            have p12322_1 := h12322c.2.1
                            have p12322_2 := h12322c.2.2.1
                            have p12322_3 := h12322c.2.2.2
                            rcases p12322_3 (m.d 0 2) (by simp) with h12336 | h12336
                            · rcases p12322_3 (m.d 1 2) (by simp) with h12337 | h12337
                              · linarith only [h0, h12337, hlam]
                              · rcases p12322_3 (m.d 2 3) (by simp) with h12339 | h12339
                                · linarith only [h12339, h4, hlam]
                                · linarith only [h12022, h12339, hlam]
                            · linarith only [h12336, hlam, p12322_0]
                          · have p12322_0 := h12322c.1
                            have p12322_1 := h12322c.2.1
                            have p12322_2 := h12322c.2.2.1
                            have p12322_3 := h12322c.2.2.2
                            rcases p12322_3 (m.d 0 2) (by simp) with h12343 | h12343
                            · rcases p12322_3 (m.d 1 2) (by simp) with h12344 | h12344
                              · linarith only [h0, h12344, hlam]
                              · rcases p12322_3 (m.d 2 3) (by simp) with h12346 | h12346
                                · linarith only [h12346, h4, hlam]
                                · rcases p12322_3 (m.d 2 4) (by simp) with h12348 | h12348
                                  · linarith only [h12348, h5, hlam]
                                  · rcases p12322_3 (m.d 2 5) (by simp) with h12350 | h12350
                                    · linarith only [h12350, hlam, p12322_0]
                                    · rcases h4bigk with h12352c | h12352c | h12352c | h12352c | h12352c | h12352c | h12352c | h12352c | h12352c | h12352c | h12352c | h12352c | h12352c | h12352c | h12352c | h12352c | h12352c | h12352c | h12352c | h12352c | h12352c | h12352c | h12352c | h12352c | h12352c
                                      · have p12352_0 := h12352c.1
                                        have p12352_1 := h12352c.2.1
                                        have p12352_2 := h12352c.2.2.1
                                        have p12352_3 := h12352c.2.2.2
                                        linarith only [hlam, p12352_0]
                                      · have p12352_0 := h12352c.1
                                        have p12352_1 := h12352c.2.1
                                        have p12352_2 := h12352c.2.2.1
                                        have p12352_3 := h12352c.2.2.2
                                        linarith only [h10760, h9, hc12, hc45, hlam, hphi, ht23, ht34, p12352_1]
                                      · have p12352_0 := h12352c.1
                                        have p12352_1 := h12352c.2.1
                                        have p12352_2 := h12352c.2.2.1
                                        have p12352_3 := h12352c.2.2.2
                                        linarith only [h9, hc24, hc45, hlam, hphi, p12352_1]
                                      · have p12352_0 := h12352c.1
                                        have p12352_1 := h12352c.2.1
                                        have p12352_2 := h12352c.2.2.1
                                        have p12352_3 := h12352c.2.2.2
                                        linarith only [h9, hc34, hc45, hlam, hphi, p12352_1]
                                      · have p12352_0 := h12352c.1
                                        have p12352_1 := h12352c.2.1
                                        have p12352_2 := h12352c.2.2.1
                                        have p12352_3 := h12352c.2.2.2
                                        linarith only [h9, hlam, p12352_0]
                                      · have p12352_0 := h12352c.1
                                        have p12352_1 := h12352c.2.1
                                        have p12352_2 := h12352c.2.2.1
                                        have p12352_3 := h12352c.2.2.2
                                        linarith only [h2, hlam, p12352_0]
                                      · have p12352_0 := h12352c.1
                                        have p12352_1 := h12352c.2.1
                                        have p12352_2 := h12352c.2.2.1
                                        have p12352_3 := h12352c.2.2.2
                                        linarith only [hlam, p12352_0]
                                      · have p12352_0 := h12352c.1
                                        have p12352_1 := h12352c.2.1
                                        have p12352_2 := h12352c.2.2.1
                                        have p12352_3 := h12352c.2.2.2
                                        linarith only [h10760, hlam, p12352_1]
                                      · have p12352_0 := h12352c.1
                                        have p12352_1 := h12352c.2.1
                                        have p12352_2 := h12352c.2.2.1
                                        have p12352_3 := h12352c.2.2.2
                                        linarith only [h2, h9, hc34, hc45, hlam, hphi, p12352_1]
                                      · have p12352_0 := h12352c.1
                                        have p12352_1 := h12352c.2.1
                                        have p12352_2 := h12352c.2.2.1
                                        have p12352_3 := h12352c.2.2.2
                                        linarith only [h12020, hlam, p12352_0]
                                      · have p12352_0 := h12352c.1
                                        have p12352_1 := h12352c.2.1
                                        have p12352_2 := h12352c.2.2.1
                                        have p12352_3 := h12352c.2.2.2
                                        linarith only [h5, hlam, p12352_0]
                                      · have p12352_0 := h12352c.1
                                        have p12352_1 := h12352c.2.1
                                        have p12352_2 := h12352c.2.2.1
                                        have p12352_3 := h12352c.2.2.2
                                        linarith only [h5, h9, hc14, hc45, hlam, hphi, p12352_1]
                                      · have p12352_0 := h12352c.1
                                        have p12352_1 := h12352c.2.1
                                        have p12352_2 := h12352c.2.2.1
                                        have p12352_3 := h12352c.2.2.2
                                        linarith only [hlam, p12352_0]
                                      · have p12352_0 := h12352c.1
                                        have p12352_1 := h12352c.2.1
                                        have p12352_2 := h12352c.2.2.1
                                        have p12352_3 := h12352c.2.2.2
                                        linarith only [h0, h12022, h12023, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p12352_1]
                                      · have p12352_0 := h12352c.1
                                        have p12352_1 := h12352c.2.1
                                        have p12352_2 := h12352c.2.2.1
                                        have p12352_3 := h12352c.2.2.2
                                        linarith only [h12025, hlam, p12352_0]
                                      · have p12352_0 := h12352c.1
                                        have p12352_1 := h12352c.2.1
                                        have p12352_2 := h12352c.2.2.1
                                        have p12352_3 := h12352c.2.2.2
                                        linarith only [h7, hlam, p12352_0]
                                      · have p12352_0 := h12352c.1
                                        have p12352_1 := h12352c.2.1
                                        have p12352_2 := h12352c.2.2.1
                                        have p12352_3 := h12352c.2.2.2
                                        linarith only [h11248, hlam, p12352_0]
                                      · have p12352_0 := h12352c.1
                                        have p12352_1 := h12352c.2.1
                                        have p12352_2 := h12352c.2.2.1
                                        have p12352_3 := h12352c.2.2.2
                                        linarith only [h12022, hlam, p12352_0]
                                      · have p12352_0 := h12352c.1
                                        have p12352_1 := h12352c.2.1
                                        have p12352_2 := h12352c.2.2.1
                                        have p12352_3 := h12352c.2.2.2
                                        linarith only [hlam, p12352_0]
                                      · have p12352_0 := h12352c.1
                                        have p12352_1 := h12352c.2.1
                                        have p12352_2 := h12352c.2.2.1
                                        have p12352_3 := h12352c.2.2.2
                                        linarith only [h12027, hlam, p12352_0]
                                      · have p12352_0 := h12352c.1
                                        have p12352_1 := h12352c.2.1
                                        have p12352_2 := h12352c.2.2.1
                                        have p12352_3 := h12352c.2.2.2
                                        linarith only [h10760, h5, hc12, hc45, hlam, hphi, ht23, ht34, p12352_1]
                                      · have p12352_0 := h12352c.1
                                        have p12352_1 := h12352c.2.1
                                        have p12352_2 := h12352c.2.2.1
                                        have p12352_3 := h12352c.2.2.2
                                        rcases p12352_3 (m.d 0 4) (by simp) with h12374 | h12374
                                        · linarith only [h12374, h9, hlam]
                                        · linarith only [h12374, h2, hlam]
                                      · have p12352_0 := h12352c.1
                                        have p12352_1 := h12352c.2.1
                                        have p12352_2 := h12352c.2.2.1
                                        have p12352_3 := h12352c.2.2.2
                                        linarith only [h10760, hc12, hc45, hlam, hphi, ht23, ht34, p12352_1]
                                      · have p12352_0 := h12352c.1
                                        have p12352_1 := h12352c.2.1
                                        have p12352_2 := h12352c.2.2.1
                                        have p12352_3 := h12352c.2.2.2
                                        rcases p12352_3 (m.d 0 4) (by simp) with h12378 | h12378
                                        · linarith only [h12378, h9, hlam]
                                        · linarith only [h12378, h7, hlam]
                                      · have p12352_0 := h12352c.1
                                        have p12352_1 := h12352c.2.1
                                        have p12352_2 := h12352c.2.2.1
                                        have p12352_3 := h12352c.2.2.2
                                        linarith only [hlam, p12352_0]
                            · linarith only [h12343, hlam, p12322_0]
                          · have p12322_0 := h12322c.1
                            have p12322_1 := h12322c.2.1
                            have p12322_2 := h12322c.2.2.1
                            have p12322_3 := h12322c.2.2.2
                            linarith only [h0, hlam, p12322_1]
                          · have p12322_0 := h12322c.1
                            have p12322_1 := h12322c.2.1
                            have p12322_2 := h12322c.2.2.1
                            have p12322_3 := h12322c.2.2.2
                            linarith only [hlam, p12322_0]
                          · have p12322_0 := h12322c.1
                            have p12322_1 := h12322c.2.1
                            have p12322_2 := h12322c.2.2.1
                            have p12322_3 := h12322c.2.2.2
                            linarith only [h9268, hlam, p12322_0]
                          · have p12322_0 := h12322c.1
                            have p12322_1 := h12322c.2.1
                            have p12322_2 := h12322c.2.2.1
                            have p12322_3 := h12322c.2.2.2
                            linarith only [h10760, hlam, p12322_0]
                          · have p12322_0 := h12322c.1
                            have p12322_1 := h12322c.2.1
                            have p12322_2 := h12322c.2.2.1
                            have p12322_3 := h12322c.2.2.2
                            linarith only [h11236, hlam, p12322_0]
                          · have p12322_0 := h12322c.1
                            have p12322_1 := h12322c.2.1
                            have p12322_2 := h12322c.2.2.1
                            have p12322_3 := h12322c.2.2.2
                            linarith only [h4, hlam, p12322_0]
                          · have p12322_0 := h12322c.1
                            have p12322_1 := h12322c.2.1
                            have p12322_2 := h12322c.2.2.1
                            have p12322_3 := h12322c.2.2.2
                            linarith only [h0, h12023, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12322_1]
                          · have p12322_0 := h12322c.1
                            have p12322_1 := h12322c.2.1
                            have p12322_2 := h12322c.2.2.1
                            have p12322_3 := h12322c.2.2.2
                            linarith only [hlam, p12322_0]
                          · have p12322_0 := h12322c.1
                            have p12322_1 := h12322c.2.1
                            have p12322_2 := h12322c.2.2.1
                            have p12322_3 := h12322c.2.2.2
                            linarith only [h0, h10760, h12023, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12322_1]
                          · have p12322_0 := h12322c.1
                            have p12322_1 := h12322c.2.1
                            have p12322_2 := h12322c.2.2.1
                            have p12322_3 := h12322c.2.2.2
                            linarith only [h12023, hlam, p12322_1]
                          · have p12322_0 := h12322c.1
                            have p12322_1 := h12322c.2.1
                            have p12322_2 := h12322c.2.2.1
                            have p12322_3 := h12322c.2.2.2
                            linarith only [h5, hlam, p12322_0]
                          · have p12322_0 := h12322c.1
                            have p12322_1 := h12322c.2.1
                            have p12322_2 := h12322c.2.2.1
                            have p12322_3 := h12322c.2.2.2
                            linarith only [h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p12322_1]
                          · have p12322_0 := h12322c.1
                            have p12322_1 := h12322c.2.1
                            have p12322_2 := h12322c.2.2.1
                            have p12322_3 := h12322c.2.2.2
                            linarith only [h12022, hlam, p12322_0]
                          · have p12322_0 := h12322c.1
                            have p12322_1 := h12322c.2.1
                            have p12322_2 := h12322c.2.2.1
                            have p12322_3 := h12322c.2.2.2
                            linarith only [hlam, p12322_0]
                          · have p12322_0 := h12322c.1
                            have p12322_1 := h12322c.2.1
                            have p12322_2 := h12322c.2.2.1
                            have p12322_3 := h12322c.2.2.2
                            linarith only [h12025, hlam, p12322_0]
                          · have p12322_0 := h12322c.1
                            have p12322_1 := h12322c.2.1
                            have p12322_2 := h12322c.2.2.1
                            have p12322_3 := h12322c.2.2.2
                            linarith only [h6, hlam, p12322_0]
                          · have p12322_0 := h12322c.1
                            have p12322_1 := h12322c.2.1
                            have p12322_2 := h12322c.2.2.1
                            have p12322_3 := h12322c.2.2.2
                            rcases p12322_3 (m.d 0 2) (by simp) with h12399 | h12399
                            · rcases p12322_3 (m.d 1 2) (by simp) with h12400 | h12400
                              · linarith only [h12400, hlam, p12322_0]
                              · rcases p12322_3 (m.d 2 3) (by simp) with h12402 | h12402
                                · linarith only [h12023, h12402, hlam]
                                · linarith only [h12402, h9268, hlam]
                            · linarith only [h0, h12399, hlam]
                          · have p12322_0 := h12322c.1
                            have p12322_1 := h12322c.2.1
                            have p12322_2 := h12322c.2.2.1
                            have p12322_3 := h12322c.2.2.2
                            linarith only [h0, h6, h9268, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12322_1]
                          · have p12322_0 := h12322c.1
                            have p12322_1 := h12322c.2.1
                            have p12322_2 := h12322c.2.2.1
                            have p12322_3 := h12322c.2.2.2
                            linarith only [h0, h10760, h12023, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12322_1]
                          · have p12322_0 := h12322c.1
                            have p12322_1 := h12322c.2.1
                            have p12322_2 := h12322c.2.2.1
                            have p12322_3 := h12322c.2.2.2
                            linarith only [hlam, p12322_0]
              · linarith only [h12050, hlam, p12029_0]
            · have p12029_0 := h12029c.1
              have p12029_1 := h12029c.2.1
              have p12029_2 := h12029c.2.2.1
              have p12029_3 := h12029c.2.2.2
              linarith only [h0, hlam, p12029_0]
            · have p12029_0 := h12029c.1
              have p12029_1 := h12029c.2.1
              have p12029_2 := h12029c.2.2.1
              have p12029_3 := h12029c.2.2.2
              linarith only [hlam, p12029_0]
            · have p12029_0 := h12029c.1
              have p12029_1 := h12029c.2.1
              have p12029_2 := h12029c.2.2.1
              have p12029_3 := h12029c.2.2.2
              linarith only [h9268, hlam, p12029_1]
            · have p12029_0 := h12029c.1
              have p12029_1 := h12029c.2.1
              have p12029_2 := h12029c.2.2.1
              have p12029_3 := h12029c.2.2.2
              linarith only [h10760, hlam, p12029_1]
            · have p12029_0 := h12029c.1
              have p12029_1 := h12029c.2.1
              have p12029_2 := h12029c.2.2.1
              have p12029_3 := h12029c.2.2.2
              linarith only [h11236, hlam, p12029_1]
            · have p12029_0 := h12029c.1
              have p12029_1 := h12029c.2.1
              have p12029_2 := h12029c.2.2.1
              have p12029_3 := h12029c.2.2.2
              linarith only [h1, hlam, p12029_0]
            · have p12029_0 := h12029c.1
              have p12029_1 := h12029c.2.1
              have p12029_2 := h12029c.2.2.1
              have p12029_3 := h12029c.2.2.2
              linarith only [h0, h11249, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12029_1]
            · have p12029_0 := h12029c.1
              have p12029_1 := h12029c.2.1
              have p12029_2 := h12029c.2.2.1
              have p12029_3 := h12029c.2.2.2
              linarith only [hlam, p12029_0]
            · have p12029_0 := h12029c.1
              have p12029_1 := h12029c.2.1
              have p12029_2 := h12029c.2.2.1
              have p12029_3 := h12029c.2.2.2
              linarith only [h0, h10760, h11249, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12029_1]
            · have p12029_0 := h12029c.1
              have p12029_1 := h12029c.2.1
              have p12029_2 := h12029c.2.2.1
              have p12029_3 := h12029c.2.2.2
              linarith only [h11249, hlam, p12029_1]
            · have p12029_0 := h12029c.1
              have p12029_1 := h12029c.2.1
              have p12029_2 := h12029c.2.2.1
              have p12029_3 := h12029c.2.2.2
              linarith only [h2, hlam, p12029_0]
            · have p12029_0 := h12029c.1
              have p12029_1 := h12029c.2.1
              have p12029_2 := h12029c.2.2.1
              have p12029_3 := h12029c.2.2.2
              linarith only [h2, h9, hc12, hc45, hlam, hphi, ht23, ht34, p12029_1]
            · have p12029_0 := h12029c.1
              have p12029_1 := h12029c.2.1
              have p12029_2 := h12029c.2.2.1
              have p12029_3 := h12029c.2.2.2
              linarith only [h11248, hlam, p12029_1]
            · have p12029_0 := h12029c.1
              have p12029_1 := h12029c.2.1
              have p12029_2 := h12029c.2.2.1
              have p12029_3 := h12029c.2.2.2
              linarith only [hlam, p12029_0]
            · have p12029_0 := h12029c.1
              have p12029_1 := h12029c.2.1
              have p12029_2 := h12029c.2.2.1
              have p12029_3 := h12029c.2.2.2
              linarith only [h12020, hlam, p12029_1]
            · have p12029_0 := h12029c.1
              have p12029_1 := h12029c.2.1
              have p12029_2 := h12029c.2.2.1
              have p12029_3 := h12029c.2.2.2
              linarith only [h3, hlam, p12029_0]
            · have p12029_0 := h12029c.1
              have p12029_1 := h12029c.2.1
              have p12029_2 := h12029c.2.2.1
              have p12029_3 := h12029c.2.2.2
              rcases p12029_3 (m.d 0 1) (by simp) with h12426 | h12426
              · rcases p12029_3 (m.d 1 2) (by simp) with h12427 | h12427
                · linarith only [h11236, h12427, hlam]
                · rcases p12029_3 (m.d 1 3) (by simp) with h12429 | h12429
                  · linarith only [h11249, h12429, hlam]
                  · linarith only [h12429, h9268, hlam]
              · linarith only [h0, h12426, hlam]
            · have p12029_0 := h12029c.1
              have p12029_1 := h12029c.2.1
              have p12029_2 := h12029c.2.2.1
              have p12029_3 := h12029c.2.2.2
              linarith only [h0, h11236, h11248, h12023, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p12029_1]
            · have p12029_0 := h12029c.1
              have p12029_1 := h12029c.2.1
              have p12029_2 := h12029c.2.2.1
              have p12029_3 := h12029c.2.2.2
              rcases p12029_3 (m.d 0 1) (by simp) with h12434 | h12434
              · rcases p12029_3 (m.d 1 2) (by simp) with h12435 | h12435
                · linarith only [h11236, h12435, hlam]
                · rcases p12029_3 (m.d 1 3) (by simp) with h12437 | h12437
                  · linarith only [h11249, h12437, hlam]
                  · linarith only [h11248, h12437, hlam]
              · linarith only [h12434, h2, hlam]
            · have p12029_0 := h12029c.1
              have p12029_1 := h12029c.2.1
              have p12029_2 := h12029c.2.2.1
              have p12029_3 := h12029c.2.2.2
              linarith only [hlam, p12029_0]
    · linarith only [h1, h11248, h12022, h9268, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h10760 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h11236 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h11248 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 3 5 (by decide) (by decide) with h11249 | h11249
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x1_x1_x1_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h10760 h11236 h11248 h11249
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x1_x1_x1_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h10760 h11236 h11248 h11249

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h10760 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h11236 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h11248 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 3 5 (by decide) (by decide) with h12443 | h12443
  · rcases m.htr 1 4 5 (by decide) (by decide) with h12444 | h12444
    · linarith only [h11248, h12443, h12444, h7, h9, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
    · linarith only [h11248, h12443, h12444, hlam]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h12447 | h12447
    · linarith only [h11248, h12447, h2, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h12449 | h12449
      · rcases m.htr 2 3 5 (by decide) (by decide) with h12450 | h12450
        · rcases m.htr 2 4 5 (by decide) (by decide) with h12451 | h12451
          · linarith only [h12451, h5, h9, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h12453 | h12453
            · linarith only [h12449, h12453, h5, h9, hlam]
            · rcases h1bigk with h12455c | h12455c | h12455c | h12455c | h12455c | h12455c | h12455c | h12455c | h12455c | h12455c | h12455c | h12455c | h12455c | h12455c | h12455c | h12455c | h12455c | h12455c | h12455c | h12455c | h12455c | h12455c | h12455c | h12455c | h12455c
              · have p12455_0 := h12455c.1
                have p12455_1 := h12455c.2.1
                have p12455_2 := h12455c.2.2.1
                have p12455_3 := h12455c.2.2.2
                linarith only [hlam, p12455_0]
              · have p12455_0 := h12455c.1
                have p12455_1 := h12455c.2.1
                have p12455_2 := h12455c.2.2.1
                have p12455_3 := h12455c.2.2.2
                linarith only [h0, h11248, h12449, h4, h9268, hlam, p12455_2]
              · have p12455_0 := h12455c.1
                have p12455_1 := h12455c.2.1
                have p12455_2 := h12455c.2.2.1
                have p12455_3 := h12455c.2.2.2
                linarith only [h0, h11248, h12449, h4, hlam, p12455_2]
              · have p12455_0 := h12455c.1
                have p12455_1 := h12455c.2.1
                have p12455_2 := h12455c.2.2.1
                have p12455_3 := h12455c.2.2.2
                rcases p12455_3 (m.d 0 1) (by simp) with h12459 | h12459
                · rcases p12455_3 (m.d 1 2) (by simp) with h12460 | h12460
                  · linarith only [h0, h12460, hlam]
                  · rcases p12455_3 (m.d 1 3) (by simp) with h12462 | h12462
                    · linarith only [h1, h12462, hlam]
                    · rcases p12455_3 (m.d 1 4) (by simp) with h12464 | h12464
                      · linarith only [h12464, hlam, p12455_0]
                      · rcases p12455_3 (m.d 1 5) (by simp) with h12466 | h12466
                        · linarith only [h12466, h3, hlam]
                        · linarith only [h12447, h12466, hlam]
                · linarith only [h12459, hlam, p12455_0]
              · have p12455_0 := h12455c.1
                have p12455_1 := h12455c.2.1
                have p12455_2 := h12455c.2.2.1
                have p12455_3 := h12455c.2.2.2
                rcases p12455_3 (m.d 0 1) (by simp) with h12470 | h12470
                · rcases p12455_3 (m.d 1 2) (by simp) with h12471 | h12471
                  · linarith only [h0, h12471, hlam]
                  · rcases p12455_3 (m.d 1 3) (by simp) with h12473 | h12473
                    · linarith only [h1, h12473, hlam]
                    · rcases p12455_3 (m.d 1 4) (by simp) with h12475 | h12475
                      · linarith only [h12475, h2, hlam]
                      · rcases p12455_3 (m.d 1 5) (by simp) with h12477 | h12477
                        · linarith only [h12477, hlam, p12455_0]
                        · rcases h1emax with h12479 | h12479 | h12479 | h12479 | h12479
                          · linarith only [h0, h11248, h12450, h12453, h12479, h4, h9268, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                          · rcases h2bigk with h12481c | h12481c | h12481c | h12481c | h12481c | h12481c | h12481c | h12481c | h12481c | h12481c | h12481c | h12481c | h12481c | h12481c | h12481c | h12481c | h12481c | h12481c | h12481c | h12481c | h12481c | h12481c | h12481c | h12481c | h12481c
                            · have p12481_0 := h12481c.1
                              have p12481_1 := h12481c.2.1
                              have p12481_2 := h12481c.2.2.1
                              have p12481_3 := h12481c.2.2.2
                              linarith only [hlam, p12481_0]
                            · have p12481_0 := h12481c.1
                              have p12481_1 := h12481c.2.1
                              have p12481_2 := h12481c.2.2.1
                              have p12481_3 := h12481c.2.2.2
                              linarith only [h11248, h12450, h12453, h4, h9268, hlam, p12481_2]
                            · have p12481_0 := h12481c.1
                              have p12481_1 := h12481c.2.1
                              have p12481_2 := h12481c.2.2.1
                              have p12481_3 := h12481c.2.2.2
                              linarith only [h0, h11248, h12450, h12453, h9268, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12481_1]
                            · have p12481_0 := h12481c.1
                              have p12481_1 := h12481c.2.1
                              have p12481_2 := h12481c.2.2.1
                              have p12481_3 := h12481c.2.2.2
                              rcases p12481_3 (m.d 0 2) (by simp) with h12485 | h12485
                              · rcases p12481_3 (m.d 1 2) (by simp) with h12486 | h12486
                                · linarith only [h0, h12486, hlam]
                                · rcases p12481_3 (m.d 2 3) (by simp) with h12488 | h12488
                                  · linarith only [h12488, h4, hlam]
                                  · linarith only [h12449, h12488, hlam]
                              · linarith only [h12485, hlam, p12481_0]
                            · have p12481_0 := h12481c.1
                              have p12481_1 := h12481c.2.1
                              have p12481_2 := h12481c.2.2.1
                              have p12481_3 := h12481c.2.2.2
                              rcases p12481_3 (m.d 0 2) (by simp) with h12492 | h12492
                              · rcases p12481_3 (m.d 1 2) (by simp) with h12493 | h12493
                                · linarith only [h0, h12493, hlam]
                                · rcases p12481_3 (m.d 2 3) (by simp) with h12495 | h12495
                                  · linarith only [h12495, h4, hlam]
                                  · linarith only [h12450, h12495, hlam]
                              · linarith only [h12492, hlam, p12481_0]
                            · have p12481_0 := h12481c.1
                              have p12481_1 := h12481c.2.1
                              have p12481_2 := h12481c.2.2.1
                              have p12481_3 := h12481c.2.2.2
                              linarith only [h0, hlam, p12481_1]
                            · have p12481_0 := h12481c.1
                              have p12481_1 := h12481c.2.1
                              have p12481_2 := h12481c.2.2.1
                              have p12481_3 := h12481c.2.2.2
                              linarith only [hlam, p12481_0]
                            · have p12481_0 := h12481c.1
                              have p12481_1 := h12481c.2.1
                              have p12481_2 := h12481c.2.2.1
                              have p12481_3 := h12481c.2.2.2
                              linarith only [h9268, hlam, p12481_0]
                            · have p12481_0 := h12481c.1
                              have p12481_1 := h12481c.2.1
                              have p12481_2 := h12481c.2.2.1
                              have p12481_3 := h12481c.2.2.2
                              linarith only [h10760, hlam, p12481_0]
                            · have p12481_0 := h12481c.1
                              have p12481_1 := h12481c.2.1
                              have p12481_2 := h12481c.2.2.1
                              have p12481_3 := h12481c.2.2.2
                              linarith only [h11236, hlam, p12481_0]
                            · have p12481_0 := h12481c.1
                              have p12481_1 := h12481c.2.1
                              have p12481_2 := h12481c.2.2.1
                              have p12481_3 := h12481c.2.2.2
                              linarith only [h4, hlam, p12481_0]
                            · have p12481_0 := h12481c.1
                              have p12481_1 := h12481c.2.1
                              have p12481_2 := h12481c.2.2.1
                              have p12481_3 := h12481c.2.2.2
                              rcases p12481_3 (m.d 0 2) (by simp) with h12505 | h12505
                              · rcases p12481_3 (m.d 1 2) (by simp) with h12506 | h12506
                                · linarith only [h12506, hlam, p12481_0]
                                · rcases p12481_3 (m.d 2 3) (by simp) with h12508 | h12508
                                  · rcases p12481_3 (m.d 2 4) (by simp) with h12509 | h12509
                                    · linarith only [h12449, h12509, hlam]
                                    · linarith only [h10760, h12509, hlam]
                                  · linarith only [h12508, hlam, p12481_0]
                              · linarith only [h0, h12505, hlam]
                            · have p12481_0 := h12481c.1
                              have p12481_1 := h12481c.2.1
                              have p12481_2 := h12481c.2.2.1
                              have p12481_3 := h12481c.2.2.2
                              linarith only [hlam, p12481_0]
                            · have p12481_0 := h12481c.1
                              have p12481_1 := h12481c.2.1
                              have p12481_2 := h12481c.2.2.1
                              have p12481_3 := h12481c.2.2.2
                              linarith only [h11248, h12449, h9268, hc12, hc23, hlam, hphi, p12481_1]
                            · have p12481_0 := h12481c.1
                              have p12481_1 := h12481c.2.1
                              have p12481_2 := h12481c.2.2.1
                              have p12481_3 := h12481c.2.2.2
                              linarith only [h0, h11236, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12481_1]
                            · have p12481_0 := h12481c.1
                              have p12481_1 := h12481c.2.1
                              have p12481_2 := h12481c.2.2.1
                              have p12481_3 := h12481c.2.2.2
                              linarith only [h5, hlam, p12481_0]
                            · have p12481_0 := h12481c.1
                              have p12481_1 := h12481c.2.1
                              have p12481_2 := h12481c.2.2.1
                              have p12481_3 := h12481c.2.2.2
                              linarith only [h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p12481_1]
                            · have p12481_0 := h12481c.1
                              have p12481_1 := h12481c.2.1
                              have p12481_2 := h12481c.2.2.1
                              have p12481_3 := h12481c.2.2.2
                              linarith only [h12449, hlam, p12481_0]
                            · have p12481_0 := h12481c.1
                              have p12481_1 := h12481c.2.1
                              have p12481_2 := h12481c.2.2.1
                              have p12481_3 := h12481c.2.2.2
                              linarith only [hlam, p12481_0]
                            · have p12481_0 := h12481c.1
                              have p12481_1 := h12481c.2.1
                              have p12481_2 := h12481c.2.2.1
                              have p12481_3 := h12481c.2.2.2
                              linarith only [h12451, hlam, p12481_0]
                            · have p12481_0 := h12481c.1
                              have p12481_1 := h12481c.2.1
                              have p12481_2 := h12481c.2.2.1
                              have p12481_3 := h12481c.2.2.2
                              linarith only [h6, hlam, p12481_0]
                            · have p12481_0 := h12481c.1
                              have p12481_1 := h12481c.2.1
                              have p12481_2 := h12481c.2.2.1
                              have p12481_3 := h12481c.2.2.2
                              rcases p12481_3 (m.d 0 2) (by simp) with h12523 | h12523
                              · rcases p12481_3 (m.d 1 2) (by simp) with h12524 | h12524
                                · linarith only [h12524, hlam, p12481_0]
                                · rcases p12481_3 (m.d 2 3) (by simp) with h12526 | h12526
                                  · rcases p12481_3 (m.d 2 4) (by simp) with h12527 | h12527
                                    · linarith only [h12451, h12527, hlam]
                                    · linarith only [h10760, h12527, hlam]
                                  · linarith only [h12526, h9268, hlam]
                              · linarith only [h0, h12523, hlam]
                            · have p12481_0 := h12481c.1
                              have p12481_1 := h12481c.2.1
                              have p12481_2 := h12481c.2.2.1
                              have p12481_3 := h12481c.2.2.2
                              linarith only [h12450, hlam, p12481_0]
                            · have p12481_0 := h12481c.1
                              have p12481_1 := h12481c.2.1
                              have p12481_2 := h12481c.2.2.1
                              have p12481_3 := h12481c.2.2.2
                              linarith only [h10760, hc12, hc25, hlam, hphi, p12481_1]
                            · have p12481_0 := h12481c.1
                              have p12481_1 := h12481c.2.1
                              have p12481_2 := h12481c.2.2.1
                              have p12481_3 := h12481c.2.2.2
                              linarith only [hlam, p12481_0]
                          · rcases h2bigk with h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c | h12535c
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [hlam, p12535_0]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h11248, h12449, h4, h9268, hlam, p12535_2]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h11248, h12449, h9268, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12535_1]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              rcases p12535_3 (m.d 0 2) (by simp) with h12539 | h12539
                              · rcases p12535_3 (m.d 1 2) (by simp) with h12540 | h12540
                                · linarith only [h0, h12540, hlam]
                                · rcases p12535_3 (m.d 2 3) (by simp) with h12542 | h12542
                                  · linarith only [h12542, h4, hlam]
                                  · linarith only [h12449, h12542, hlam]
                              · linarith only [h12539, hlam, p12535_0]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              rcases p12535_3 (m.d 0 2) (by simp) with h12546 | h12546
                              · rcases p12535_3 (m.d 1 2) (by simp) with h12547 | h12547
                                · linarith only [h0, h12547, hlam]
                                · rcases p12535_3 (m.d 2 3) (by simp) with h12549 | h12549
                                  · linarith only [h12549, h4, hlam]
                                  · linarith only [h12450, h12549, hlam]
                              · linarith only [h12546, hlam, p12535_0]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h0, hlam, p12535_1]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [hlam, p12535_0]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h9268, hlam, p12535_0]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h10760, hlam, p12535_0]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h11236, hlam, p12535_0]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h4, hlam, p12535_0]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              rcases p12535_3 (m.d 0 2) (by simp) with h12559 | h12559
                              · rcases p12535_3 (m.d 1 2) (by simp) with h12560 | h12560
                                · linarith only [h12560, hlam, p12535_0]
                                · rcases p12535_3 (m.d 2 3) (by simp) with h12562 | h12562
                                  · rcases p12535_3 (m.d 2 4) (by simp) with h12563 | h12563
                                    · linarith only [h12449, h12563, hlam]
                                    · linarith only [h10760, h12563, hlam]
                                  · linarith only [h12562, hlam, p12535_0]
                              · linarith only [h0, h12559, hlam]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [hlam, p12535_0]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h11248, h12449, h9268, hc12, hc23, hlam, hphi, p12535_1]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h0, h11248, h12450, h12453, h4, h9268, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12535_1]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h5, hlam, p12535_0]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p12535_1]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h12449, hlam, p12535_0]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [hlam, p12535_0]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h12451, hlam, p12535_0]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h6, hlam, p12535_0]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              rcases p12535_3 (m.d 0 2) (by simp) with h12577 | h12577
                              · rcases p12535_3 (m.d 1 2) (by simp) with h12578 | h12578
                                · linarith only [h12578, hlam, p12535_0]
                                · rcases p12535_3 (m.d 2 3) (by simp) with h12580 | h12580
                                  · rcases p12535_3 (m.d 2 4) (by simp) with h12581 | h12581
                                    · linarith only [h12451, h12581, hlam]
                                    · linarith only [h10760, h12581, hlam]
                                  · linarith only [h12580, h9268, hlam]
                              · linarith only [h0, h12577, hlam]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h12450, hlam, p12535_0]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [h10760, hc12, hc25, hlam, hphi, p12535_1]
                            · have p12535_0 := h12535c.1
                              have p12535_1 := h12535c.2.1
                              have p12535_2 := h12535c.2.2.1
                              have p12535_3 := h12535c.2.2.2
                              linarith only [hlam, p12535_0]
                          · rcases h2bigk with h12589c | h12589c | h12589c | h12589c | h12589c | h12589c | h12589c | h12589c | h12589c | h12589c | h12589c | h12589c | h12589c | h12589c | h12589c | h12589c | h12589c | h12589c | h12589c | h12589c | h12589c | h12589c | h12589c | h12589c | h12589c
                            · have p12589_0 := h12589c.1
                              have p12589_1 := h12589c.2.1
                              have p12589_2 := h12589c.2.2.1
                              have p12589_3 := h12589c.2.2.2
                              linarith only [hlam, p12589_0]
                            · have p12589_0 := h12589c.1
                              have p12589_1 := h12589c.2.1
                              have p12589_2 := h12589c.2.2.1
                              have p12589_3 := h12589c.2.2.2
                              linarith only [h11248, h12449, h4, h9268, hlam, p12589_2]
                            · have p12589_0 := h12589c.1
                              have p12589_1 := h12589c.2.1
                              have p12589_2 := h12589c.2.2.1
                              have p12589_3 := h12589c.2.2.2
                              linarith only [h11248, h12449, h9268, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12589_1]
                            · have p12589_0 := h12589c.1
                              have p12589_1 := h12589c.2.1
                              have p12589_2 := h12589c.2.2.1
                              have p12589_3 := h12589c.2.2.2
                              rcases p12589_3 (m.d 0 2) (by simp) with h12593 | h12593
                              · rcases p12589_3 (m.d 1 2) (by simp) with h12594 | h12594
                                · linarith only [h0, h12594, hlam]
                                · rcases p12589_3 (m.d 2 3) (by simp) with h12596 | h12596
                                  · linarith only [h12596, h4, hlam]
                                  · linarith only [h12449, h12596, hlam]
                              · linarith only [h12593, hlam, p12589_0]
                            · have p12589_0 := h12589c.1
                              have p12589_1 := h12589c.2.1
                              have p12589_2 := h12589c.2.2.1
                              have p12589_3 := h12589c.2.2.2
                              rcases p12589_3 (m.d 0 2) (by simp) with h12600 | h12600
                              · rcases p12589_3 (m.d 1 2) (by simp) with h12601 | h12601
                                · linarith only [h0, h12601, hlam]
                                · rcases p12589_3 (m.d 2 3) (by simp) with h12603 | h12603
                                  · linarith only [h12603, h4, hlam]
                                  · linarith only [h12450, h12603, hlam]
                              · linarith only [h12600, hlam, p12589_0]
                            · have p12589_0 := h12589c.1
                              have p12589_1 := h12589c.2.1
                              have p12589_2 := h12589c.2.2.1
                              have p12589_3 := h12589c.2.2.2
                              linarith only [h0, hlam, p12589_1]
                            · have p12589_0 := h12589c.1
                              have p12589_1 := h12589c.2.1
                              have p12589_2 := h12589c.2.2.1
                              have p12589_3 := h12589c.2.2.2
                              linarith only [hlam, p12589_0]
                            · have p12589_0 := h12589c.1
                              have p12589_1 := h12589c.2.1
                              have p12589_2 := h12589c.2.2.1
                              have p12589_3 := h12589c.2.2.2
                              linarith only [h9268, hlam, p12589_0]
                            · have p12589_0 := h12589c.1
                              have p12589_1 := h12589c.2.1
                              have p12589_2 := h12589c.2.2.1
                              have p12589_3 := h12589c.2.2.2
                              linarith only [h10760, hlam, p12589_0]
                            · have p12589_0 := h12589c.1
                              have p12589_1 := h12589c.2.1
                              have p12589_2 := h12589c.2.2.1
                              have p12589_3 := h12589c.2.2.2
                              linarith only [h11236, hlam, p12589_0]
                            · have p12589_0 := h12589c.1
                              have p12589_1 := h12589c.2.1
                              have p12589_2 := h12589c.2.2.1
                              have p12589_3 := h12589c.2.2.2
                              linarith only [h4, hlam, p12589_0]
                            · have p12589_0 := h12589c.1
                              have p12589_1 := h12589c.2.1
                              have p12589_2 := h12589c.2.2.1
                              have p12589_3 := h12589c.2.2.2
                              rcases p12589_3 (m.d 0 2) (by simp) with h12613 | h12613
                              · rcases p12589_3 (m.d 1 2) (by simp) with h12614 | h12614
                                · linarith only [h12614, hlam, p12589_0]
                                · rcases p12589_3 (m.d 2 3) (by simp) with h12616 | h12616
                                  · rcases p12589_3 (m.d 2 4) (by simp) with h12617 | h12617
                                    · linarith only [h12449, h12617, hlam]
                                    · linarith only [h10760, h12617, hlam]
                                  · linarith only [h12616, hlam, p12589_0]
                              · linarith only [h0, h12613, hlam]
                            · have p12589_0 := h12589c.1
                              have p12589_1 := h12589c.2.1
                              have p12589_2 := h12589c.2.2.1
                              have p12589_3 := h12589c.2.2.2
                              linarith only [hlam, p12589_0]
                            · have p12589_0 := h12589c.1
                              have p12589_1 := h12589c.2.1
                              have p12589_2 := h12589c.2.2.1
                              have p12589_3 := h12589c.2.2.2
                              linarith only [h11248, h12449, h9268, hc12, hc23, hlam, hphi, p12589_1]
                            · have p12589_0 := h12589c.1
                              have p12589_1 := h12589c.2.1
                              have p12589_2 := h12589c.2.2.1
                              have p12589_3 := h12589c.2.2.2
                              linarith only [h0, h11248, h12450, h12453, h4, h9268, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12589_1]
                            · have p12589_0 := h12589c.1
                              have p12589_1 := h12589c.2.1
                              have p12589_2 := h12589c.2.2.1
                              have p12589_3 := h12589c.2.2.2
                              linarith only [h5, hlam, p12589_0]
                            · have p12589_0 := h12589c.1
                              have p12589_1 := h12589c.2.1
                              have p12589_2 := h12589c.2.2.1
                              have p12589_3 := h12589c.2.2.2
                              linarith only [h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p12589_1]
                            · have p12589_0 := h12589c.1
                              have p12589_1 := h12589c.2.1
                              have p12589_2 := h12589c.2.2.1
                              have p12589_3 := h12589c.2.2.2
                              linarith only [h12449, hlam, p12589_0]
                            · have p12589_0 := h12589c.1
                              have p12589_1 := h12589c.2.1
                              have p12589_2 := h12589c.2.2.1
                              have p12589_3 := h12589c.2.2.2
                              linarith only [hlam, p12589_0]
                            · have p12589_0 := h12589c.1
                              have p12589_1 := h12589c.2.1
                              have p12589_2 := h12589c.2.2.1
                              have p12589_3 := h12589c.2.2.2
                              linarith only [h12451, hlam, p12589_0]
                            · have p12589_0 := h12589c.1
                              have p12589_1 := h12589c.2.1
                              have p12589_2 := h12589c.2.2.1
                              have p12589_3 := h12589c.2.2.2
                              linarith only [h6, hlam, p12589_0]
                            · have p12589_0 := h12589c.1
                              have p12589_1 := h12589c.2.1
                              have p12589_2 := h12589c.2.2.1
                              have p12589_3 := h12589c.2.2.2
                              rcases p12589_3 (m.d 0 2) (by simp) with h12631 | h12631
                              · rcases p12589_3 (m.d 1 2) (by simp) with h12632 | h12632
                                · linarith only [h12632, hlam, p12589_0]
                                · rcases p12589_3 (m.d 2 3) (by simp) with h12634 | h12634
                                  · rcases p12589_3 (m.d 2 4) (by simp) with h12635 | h12635
                                    · linarith only [h12451, h12635, hlam]
                                    · linarith only [h10760, h12635, hlam]
                                  · linarith only [h12634, h9268, hlam]
                              · linarith only [h0, h12631, hlam]
                            · have p12589_0 := h12589c.1
                              have p12589_1 := h12589c.2.1
                              have p12589_2 := h12589c.2.2.1
                              have p12589_3 := h12589c.2.2.2
                              linarith only [h12450, hlam, p12589_0]
                            · have p12589_0 := h12589c.1
                              have p12589_1 := h12589c.2.1
                              have p12589_2 := h12589c.2.2.1
                              have p12589_3 := h12589c.2.2.2
                              linarith only [h10760, hc12, hc25, hlam, hphi, p12589_1]
                            · have p12589_0 := h12589c.1
                              have p12589_1 := h12589c.2.1
                              have p12589_2 := h12589c.2.2.1
                              have p12589_3 := h12589c.2.2.2
                              linarith only [hlam, p12589_0]
                          · rcases h2bigk with h12643c | h12643c | h12643c | h12643c | h12643c | h12643c | h12643c | h12643c | h12643c | h12643c | h12643c | h12643c | h12643c | h12643c | h12643c | h12643c | h12643c | h12643c | h12643c | h12643c | h12643c | h12643c | h12643c | h12643c | h12643c
                            · have p12643_0 := h12643c.1
                              have p12643_1 := h12643c.2.1
                              have p12643_2 := h12643c.2.2.1
                              have p12643_3 := h12643c.2.2.2
                              linarith only [hlam, p12643_0]
                            · have p12643_0 := h12643c.1
                              have p12643_1 := h12643c.2.1
                              have p12643_2 := h12643c.2.2.1
                              have p12643_3 := h12643c.2.2.2
                              linarith only [h11248, h12449, h4, h9268, hlam, p12643_2]
                            · have p12643_0 := h12643c.1
                              have p12643_1 := h12643c.2.1
                              have p12643_2 := h12643c.2.2.1
                              have p12643_3 := h12643c.2.2.2
                              linarith only [h11248, h12449, h9268, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12643_1]
                            · have p12643_0 := h12643c.1
                              have p12643_1 := h12643c.2.1
                              have p12643_2 := h12643c.2.2.1
                              have p12643_3 := h12643c.2.2.2
                              rcases p12643_3 (m.d 0 2) (by simp) with h12647 | h12647
                              · rcases p12643_3 (m.d 1 2) (by simp) with h12648 | h12648
                                · linarith only [h0, h12648, hlam]
                                · rcases p12643_3 (m.d 2 3) (by simp) with h12650 | h12650
                                  · linarith only [h12650, h4, hlam]
                                  · linarith only [h12449, h12650, hlam]
                              · linarith only [h12647, hlam, p12643_0]
                            · have p12643_0 := h12643c.1
                              have p12643_1 := h12643c.2.1
                              have p12643_2 := h12643c.2.2.1
                              have p12643_3 := h12643c.2.2.2
                              rcases p12643_3 (m.d 0 2) (by simp) with h12654 | h12654
                              · rcases p12643_3 (m.d 1 2) (by simp) with h12655 | h12655
                                · linarith only [h0, h12655, hlam]
                                · rcases p12643_3 (m.d 2 3) (by simp) with h12657 | h12657
                                  · linarith only [h12657, h4, hlam]
                                  · linarith only [h12450, h12657, hlam]
                              · linarith only [h12654, hlam, p12643_0]
                            · have p12643_0 := h12643c.1
                              have p12643_1 := h12643c.2.1
                              have p12643_2 := h12643c.2.2.1
                              have p12643_3 := h12643c.2.2.2
                              linarith only [h0, hlam, p12643_1]
                            · have p12643_0 := h12643c.1
                              have p12643_1 := h12643c.2.1
                              have p12643_2 := h12643c.2.2.1
                              have p12643_3 := h12643c.2.2.2
                              linarith only [hlam, p12643_0]
                            · have p12643_0 := h12643c.1
                              have p12643_1 := h12643c.2.1
                              have p12643_2 := h12643c.2.2.1
                              have p12643_3 := h12643c.2.2.2
                              linarith only [h9268, hlam, p12643_0]
                            · have p12643_0 := h12643c.1
                              have p12643_1 := h12643c.2.1
                              have p12643_2 := h12643c.2.2.1
                              have p12643_3 := h12643c.2.2.2
                              linarith only [h10760, hlam, p12643_0]
                            · have p12643_0 := h12643c.1
                              have p12643_1 := h12643c.2.1
                              have p12643_2 := h12643c.2.2.1
                              have p12643_3 := h12643c.2.2.2
                              linarith only [h11236, hlam, p12643_0]
                            · have p12643_0 := h12643c.1
                              have p12643_1 := h12643c.2.1
                              have p12643_2 := h12643c.2.2.1
                              have p12643_3 := h12643c.2.2.2
                              linarith only [h4, hlam, p12643_0]
                            · have p12643_0 := h12643c.1
                              have p12643_1 := h12643c.2.1
                              have p12643_2 := h12643c.2.2.1
                              have p12643_3 := h12643c.2.2.2
                              rcases p12643_3 (m.d 0 2) (by simp) with h12667 | h12667
                              · rcases p12643_3 (m.d 1 2) (by simp) with h12668 | h12668
                                · linarith only [h12668, hlam, p12643_0]
                                · rcases p12643_3 (m.d 2 3) (by simp) with h12670 | h12670
                                  · rcases p12643_3 (m.d 2 4) (by simp) with h12671 | h12671
                                    · linarith only [h12449, h12671, hlam]
                                    · linarith only [h10760, h12671, hlam]
                                  · linarith only [h12670, hlam, p12643_0]
                              · linarith only [h0, h12667, hlam]
                            · have p12643_0 := h12643c.1
                              have p12643_1 := h12643c.2.1
                              have p12643_2 := h12643c.2.2.1
                              have p12643_3 := h12643c.2.2.2
                              linarith only [hlam, p12643_0]
                            · have p12643_0 := h12643c.1
                              have p12643_1 := h12643c.2.1
                              have p12643_2 := h12643c.2.2.1
                              have p12643_3 := h12643c.2.2.2
                              linarith only [h11248, h12449, h9268, hc12, hc23, hlam, hphi, p12643_1]
                            · have p12643_0 := h12643c.1
                              have p12643_1 := h12643c.2.1
                              have p12643_2 := h12643c.2.2.1
                              have p12643_3 := h12643c.2.2.2
                              linarith only [h0, h11248, h12450, h12453, h4, h9268, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12643_1]
                            · have p12643_0 := h12643c.1
                              have p12643_1 := h12643c.2.1
                              have p12643_2 := h12643c.2.2.1
                              have p12643_3 := h12643c.2.2.2
                              linarith only [h5, hlam, p12643_0]
                            · have p12643_0 := h12643c.1
                              have p12643_1 := h12643c.2.1
                              have p12643_2 := h12643c.2.2.1
                              have p12643_3 := h12643c.2.2.2
                              linarith only [h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p12643_1]
                            · have p12643_0 := h12643c.1
                              have p12643_1 := h12643c.2.1
                              have p12643_2 := h12643c.2.2.1
                              have p12643_3 := h12643c.2.2.2
                              linarith only [h12449, hlam, p12643_0]
                            · have p12643_0 := h12643c.1
                              have p12643_1 := h12643c.2.1
                              have p12643_2 := h12643c.2.2.1
                              have p12643_3 := h12643c.2.2.2
                              linarith only [hlam, p12643_0]
                            · have p12643_0 := h12643c.1
                              have p12643_1 := h12643c.2.1
                              have p12643_2 := h12643c.2.2.1
                              have p12643_3 := h12643c.2.2.2
                              linarith only [h12451, hlam, p12643_0]
                            · have p12643_0 := h12643c.1
                              have p12643_1 := h12643c.2.1
                              have p12643_2 := h12643c.2.2.1
                              have p12643_3 := h12643c.2.2.2
                              linarith only [h6, hlam, p12643_0]
                            · have p12643_0 := h12643c.1
                              have p12643_1 := h12643c.2.1
                              have p12643_2 := h12643c.2.2.1
                              have p12643_3 := h12643c.2.2.2
                              rcases p12643_3 (m.d 0 2) (by simp) with h12685 | h12685
                              · rcases p12643_3 (m.d 1 2) (by simp) with h12686 | h12686
                                · linarith only [h12686, hlam, p12643_0]
                                · rcases p12643_3 (m.d 2 3) (by simp) with h12688 | h12688
                                  · rcases p12643_3 (m.d 2 4) (by simp) with h12689 | h12689
                                    · linarith only [h12451, h12689, hlam]
                                    · linarith only [h10760, h12689, hlam]
                                  · linarith only [h12688, h9268, hlam]
                              · linarith only [h0, h12685, hlam]
                            · have p12643_0 := h12643c.1
                              have p12643_1 := h12643c.2.1
                              have p12643_2 := h12643c.2.2.1
                              have p12643_3 := h12643c.2.2.2
                              linarith only [h12450, hlam, p12643_0]
                            · have p12643_0 := h12643c.1
                              have p12643_1 := h12643c.2.1
                              have p12643_2 := h12643c.2.2.1
                              have p12643_3 := h12643c.2.2.2
                              linarith only [h10760, hc12, hc25, hlam, hphi, p12643_1]
                            · have p12643_0 := h12643c.1
                              have p12643_1 := h12643c.2.1
                              have p12643_2 := h12643c.2.2.1
                              have p12643_3 := h12643c.2.2.2
                              linarith only [hlam, p12643_0]
                · linarith only [h12470, hlam, p12455_0]
              · have p12455_0 := h12455c.1
                have p12455_1 := h12455c.2.1
                have p12455_2 := h12455c.2.2.1
                have p12455_3 := h12455c.2.2.2
                linarith only [h0, hlam, p12455_0]
              · have p12455_0 := h12455c.1
                have p12455_1 := h12455c.2.1
                have p12455_2 := h12455c.2.2.1
                have p12455_3 := h12455c.2.2.2
                linarith only [hlam, p12455_0]
              · have p12455_0 := h12455c.1
                have p12455_1 := h12455c.2.1
                have p12455_2 := h12455c.2.2.1
                have p12455_3 := h12455c.2.2.2
                linarith only [h9268, hlam, p12455_1]
              · have p12455_0 := h12455c.1
                have p12455_1 := h12455c.2.1
                have p12455_2 := h12455c.2.2.1
                have p12455_3 := h12455c.2.2.2
                linarith only [h10760, hlam, p12455_1]
              · have p12455_0 := h12455c.1
                have p12455_1 := h12455c.2.1
                have p12455_2 := h12455c.2.2.1
                have p12455_3 := h12455c.2.2.2
                linarith only [h11236, hlam, p12455_1]
              · have p12455_0 := h12455c.1
                have p12455_1 := h12455c.2.1
                have p12455_2 := h12455c.2.2.1
                have p12455_3 := h12455c.2.2.2
                linarith only [h1, hlam, p12455_0]
              · have p12455_0 := h12455c.1
                have p12455_1 := h12455c.2.1
                have p12455_2 := h12455c.2.2.1
                have p12455_3 := h12455c.2.2.2
                linarith only [h11248, hc12, hc34, hlam, hphi, ht23, p12455_1]
              · have p12455_0 := h12455c.1
                have p12455_1 := h12455c.2.1
                have p12455_2 := h12455c.2.2.1
                have p12455_3 := h12455c.2.2.2
                linarith only [hlam, p12455_0]
              · have p12455_0 := h12455c.1
                have p12455_1 := h12455c.2.1
                have p12455_2 := h12455c.2.2.1
                have p12455_3 := h12455c.2.2.2
                linarith only [h11248, hlam, p12455_0]
              · have p12455_0 := h12455c.1
                have p12455_1 := h12455c.2.1
                have p12455_2 := h12455c.2.2.1
                have p12455_3 := h12455c.2.2.2
                linarith only [h12443, hlam, p12455_1]
              · have p12455_0 := h12455c.1
                have p12455_1 := h12455c.2.1
                have p12455_2 := h12455c.2.2.1
                have p12455_3 := h12455c.2.2.2
                linarith only [h2, hlam, p12455_0]
              · have p12455_0 := h12455c.1
                have p12455_1 := h12455c.2.1
                have p12455_2 := h12455c.2.2.1
                have p12455_3 := h12455c.2.2.2
                linarith only [h2, h9, hc12, hc45, hlam, hphi, ht23, ht34, p12455_1]
              · have p12455_0 := h12455c.1
                have p12455_1 := h12455c.2.1
                have p12455_2 := h12455c.2.2.1
                have p12455_3 := h12455c.2.2.2
                linarith only [h10760, h5, h9, hc13, hc45, hlam, hphi, ht34, p12455_1]
              · have p12455_0 := h12455c.1
                have p12455_1 := h12455c.2.1
                have p12455_2 := h12455c.2.2.1
                have p12455_3 := h12455c.2.2.2
                linarith only [hlam, p12455_0]
              · have p12455_0 := h12455c.1
                have p12455_1 := h12455c.2.1
                have p12455_2 := h12455c.2.2.1
                have p12455_3 := h12455c.2.2.2
                linarith only [h12447, hlam, p12455_1]
              · have p12455_0 := h12455c.1
                have p12455_1 := h12455c.2.1
                have p12455_2 := h12455c.2.2.1
                have p12455_3 := h12455c.2.2.2
                linarith only [h3, hlam, p12455_0]
              · have p12455_0 := h12455c.1
                have p12455_1 := h12455c.2.1
                have p12455_2 := h12455c.2.2.1
                have p12455_3 := h12455c.2.2.2
                linarith only [h0, h12443, h12450, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12455_1]
              · have p12455_0 := h12455c.1
                have p12455_1 := h12455c.2.1
                have p12455_2 := h12455c.2.2.1
                have p12455_3 := h12455c.2.2.2
                linarith only [h0, h12443, h12450, h4, h9268, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12455_1]
              · have p12455_0 := h12455c.1
                have p12455_1 := h12455c.2.1
                have p12455_2 := h12455c.2.2.1
                have p12455_3 := h12455c.2.2.2
                linarith only [h0, h12443, h12450, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p12455_1]
              · have p12455_0 := h12455c.1
                have p12455_1 := h12455c.2.1
                have p12455_2 := h12455c.2.2.1
                have p12455_3 := h12455c.2.2.2
                linarith only [hlam, p12455_0]
        · linarith only [h11248, h12449, h12450, h9268, hc12, hc35, hlam, hphi, ht23]
      · linarith only [h12449, h7, h9, h9268, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 6904000 in
set_option maxHeartbeats 6904000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h9268 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h10760 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h11236 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 3 4 (by decide) (by decide) with h11248 | h11248
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h10760 h11236 h11248
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s17_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h9268 h10760 h11236 h11248

end R2N4
