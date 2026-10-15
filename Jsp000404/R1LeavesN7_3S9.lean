import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_3S6
import Jsp000404.R1LeavesN7_3S7
import Jsp000404.R1LeavesN7_3S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11192000 in
set_option maxHeartbeats 11192000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s8_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
    (h9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h3976 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h4749 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 5 (by decide) (by decide) with h4997 | h4997
  · rcases m.htr 1 3 4 (by decide) (by decide) with h4998 | h4998
    · rcases m.htr 1 3 5 (by decide) (by decide) with h4999 | h4999
      · rcases m.htr 1 4 5 (by decide) (by decide) with h5000 | h5000
        · linarith only [h4749, h4997, h5, h5000, h9, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
        · linarith only [h4749, h4997, h5000, hlam]
      · linarith only [h4749, h4997, h4998, h4999, h5, h9, hc34, hc45, hlam, hphi]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h5004 | h5004
      · rcases m.htr 1 4 5 (by decide) (by decide) with h5005 | h5005
        · linarith only [h3976, h4997, h4998, h5005, h7, h9, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
        · linarith only [h4749, h4997, h5005, hlam]
      · linarith only [h3976, h4997, h5004, hlam]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h5009 | h5009
    · rcases m.htr 1 3 5 (by decide) (by decide) with h5010 | h5010
      · rcases m.htr 1 4 5 (by decide) (by decide) with h5011 | h5011
        · linarith only [h2, h5011, h9, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h5013 | h5013
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5014 | h5014
            · rcases m.htr 2 4 5 (by decide) (by decide) with h5015 | h5015
              · linarith only [h5, h5015, h9, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h5017 | h5017
                · linarith only [h4749, h5, h5017, h9, hc12, hc34, hlam, hphi, ht23]
                · rcases h1bigk with h5019c | h5019c | h5019c | h5019c | h5019c | h5019c | h5019c | h5019c | h5019c | h5019c | h5019c | h5019c | h5019c | h5019c | h5019c | h5019c | h5019c | h5019c | h5019c | h5019c | h5019c | h5019c | h5019c | h5019c | h5019c
                  · have p5019_0 := h5019c.1
                    have p5019_1 := h5019c.2.1
                    have p5019_2 := h5019c.2.2.1
                    have p5019_3 := h5019c.2.2.2
                    linarith only [hlam, p5019_0]
                  · have p5019_0 := h5019c.1
                    have p5019_1 := h5019c.2.1
                    have p5019_2 := h5019c.2.2.1
                    have p5019_3 := h5019c.2.2.2
                    rcases p5019_3 (m.d 0 1) (by simp) with h5021 | h5021
                    · rcases p5019_3 (m.d 1 2) (by simp) with h5022 | h5022
                      · linarith only [h5022, hlam, p5019_0]
                      · rcases p5019_3 (m.d 1 3) (by simp) with h5024 | h5024
                        · linarith only [h1, h5024, hlam]
                        · linarith only [h3976, h5024, hlam]
                    · linarith only [h5021, hlam, p5019_0]
                  · have p5019_0 := h5019c.1
                    have p5019_1 := h5019c.2.1
                    have p5019_2 := h5019c.2.2.1
                    have p5019_3 := h5019c.2.2.2
                    rcases p5019_3 (m.d 0 1) (by simp) with h5028 | h5028
                    · rcases p5019_3 (m.d 1 2) (by simp) with h5029 | h5029
                      · linarith only [h0, h5029, hlam]
                      · rcases p5019_3 (m.d 1 3) (by simp) with h5031 | h5031
                        · linarith only [h5031, hlam, p5019_0]
                        · rcases p5019_3 (m.d 1 4) (by simp) with h5033 | h5033
                          · linarith only [h2, h5033, hlam]
                          · rcases p5019_3 (m.d 1 5) (by simp) with h5035 | h5035
                            · linarith only [h3, h5035, hlam]
                            · rcases h3bigk with h5037c | h5037c | h5037c | h5037c | h5037c | h5037c | h5037c | h5037c | h5037c | h5037c | h5037c | h5037c | h5037c | h5037c | h5037c | h5037c | h5037c | h5037c | h5037c | h5037c | h5037c | h5037c | h5037c | h5037c | h5037c
                              · have p5037_0 := h5037c.1
                                have p5037_1 := h5037c.2.1
                                have p5037_2 := h5037c.2.2.1
                                have p5037_3 := h5037c.2.2.2
                                linarith only [hlam, p5037_0]
                              · have p5037_0 := h5037c.1
                                have p5037_1 := h5037c.2.1
                                have p5037_2 := h5037c.2.2.1
                                have p5037_3 := h5037c.2.2.2
                                rcases p5037_3 (m.d 0 3) (by simp) with h5039 | h5039
                                · rcases p5037_3 (m.d 1 3) (by simp) with h5040 | h5040
                                  · linarith only [h1, h5040, hlam]
                                  · rcases p5037_3 (m.d 2 3) (by simp) with h5042 | h5042
                                    · linarith only [h4, h5042, hlam]
                                    · linarith only [h3976, h5042, hlam]
                                · linarith only [h1, h5039, hlam]
                              · have p5037_0 := h5037c.1
                                have p5037_1 := h5037c.2.1
                                have p5037_2 := h5037c.2.2.1
                                have p5037_3 := h5037c.2.2.2
                                rcases p5037_3 (m.d 0 3) (by simp) with h5046 | h5046
                                · rcases p5037_3 (m.d 1 3) (by simp) with h5047 | h5047
                                  · linarith only [h1, h5047, hlam]
                                  · rcases p5037_3 (m.d 2 3) (by simp) with h5049 | h5049
                                    · linarith only [h4, h5049, hlam]
                                    · rcases p5037_3 (m.d 3 4) (by simp) with h5051 | h5051
                                      · linarith only [h5051, h7, hlam]
                                      · rcases p5037_3 (m.d 3 5) (by simp) with h5053 | h5053
                                        · linarith only [h5053, h8, hlam]
                                        · rcases h5bigk with h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c | h5055c
                                          · have p5055_0 := h5055c.1
                                            have p5055_1 := h5055c.2.1
                                            have p5055_2 := h5055c.2.2.1
                                            have p5055_3 := h5055c.2.2.2
                                            linarith only [hlam, p5055_0]
                                          · have p5055_0 := h5055c.1
                                            have p5055_1 := h5055c.2.1
                                            have p5055_2 := h5055c.2.2.1
                                            have p5055_3 := h5055c.2.2.2
                                            linarith only [h5011, h9, hc14, hc45, hlam, hphi, p5055_1]
                                          · have p5055_0 := h5055c.1
                                            have p5055_1 := h5055c.2.1
                                            have p5055_2 := h5055c.2.2.1
                                            have p5055_3 := h5055c.2.2.2
                                            linarith only [h4749, h5015, h9, hc12, hc45, hlam, hphi, ht23, ht34, p5055_1]
                                          · have p5055_0 := h5055c.1
                                            have p5055_1 := h5055c.2.1
                                            have p5055_2 := h5055c.2.2.1
                                            have p5055_3 := h5055c.2.2.2
                                            linarith only [h5017, h9, hc34, hc45, hlam, hphi, p5055_1]
                                          · have p5055_0 := h5055c.1
                                            have p5055_1 := h5055c.2.1
                                            have p5055_2 := h5055c.2.2.1
                                            have p5055_3 := h5055c.2.2.2
                                            linarith only [h9, hlam, p5055_1]
                                          · have p5055_0 := h5055c.1
                                            have p5055_1 := h5055c.2.1
                                            have p5055_2 := h5055c.2.2.1
                                            have p5055_3 := h5055c.2.2.2
                                            linarith only [h3, hlam, p5055_0]
                                          · have p5055_0 := h5055c.1
                                            have p5055_1 := h5055c.2.1
                                            have p5055_2 := h5055c.2.2.1
                                            have p5055_3 := h5055c.2.2.2
                                            linarith only [hlam, p5055_0]
                                          · have p5055_0 := h5055c.1
                                            have p5055_1 := h5055c.2.1
                                            have p5055_2 := h5055c.2.2.1
                                            have p5055_3 := h5055c.2.2.2
                                            linarith only [h4997, hlam, p5055_0]
                                          · have p5055_0 := h5055c.1
                                            have p5055_1 := h5055c.2.1
                                            have p5055_2 := h5055c.2.2.1
                                            have p5055_3 := h5055c.2.2.2
                                            linarith only [h3, h5017, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5055_1]
                                          · have p5055_0 := h5055c.1
                                            have p5055_1 := h5055c.2.1
                                            have p5055_2 := h5055c.2.2.1
                                            have p5055_3 := h5055c.2.2.2
                                            linarith only [h5011, hlam, p5055_1]
                                          · have p5055_0 := h5055c.1
                                            have p5055_1 := h5055c.2.1
                                            have p5055_2 := h5055c.2.2.1
                                            have p5055_3 := h5055c.2.2.2
                                            linarith only [h6, hlam, p5055_1]
                                          · have p5055_0 := h5055c.1
                                            have p5055_1 := h5055c.2.1
                                            have p5055_2 := h5055c.2.2.1
                                            have p5055_3 := h5055c.2.2.2
                                            linarith only [h4, h5014, hc02, hc15, hlam, hphi, ht0b, ht5b, p5037_1, p5055_1]
                                          · have p5055_0 := h5055c.1
                                            have p5055_1 := h5055c.2.1
                                            have p5055_2 := h5055c.2.2.1
                                            have p5055_3 := h5055c.2.2.2
                                            linarith only [hlam, p5055_0]
                                          · have p5055_0 := h5055c.1
                                            have p5055_1 := h5055c.2.1
                                            have p5055_2 := h5055c.2.2.1
                                            have p5055_3 := h5055c.2.2.2
                                            linarith only [h0, h4, h5014, h5017, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5037_1, p5055_1]
                                          · have p5055_0 := h5055c.1
                                            have p5055_1 := h5055c.2.1
                                            have p5055_2 := h5055c.2.2.1
                                            have p5055_3 := h5055c.2.2.2
                                            linarith only [h5015, hlam, p5055_1]
                                          · have p5055_0 := h5055c.1
                                            have p5055_1 := h5055c.2.1
                                            have p5055_2 := h5055c.2.2.1
                                            have p5055_3 := h5055c.2.2.2
                                            linarith only [h8, hlam, p5055_0]
                                          · have p5055_0 := h5055c.1
                                            have p5055_1 := h5055c.2.1
                                            have p5055_2 := h5055c.2.2.1
                                            have p5055_3 := h5055c.2.2.2
                                            linarith only [h5010, hlam, p5055_0]
                                          · have p5055_0 := h5055c.1
                                            have p5055_1 := h5055c.2.1
                                            have p5055_2 := h5055c.2.2.1
                                            have p5055_3 := h5055c.2.2.2
                                            linarith only [h5014, hlam, p5055_0]
                                          · have p5055_0 := h5055c.1
                                            have p5055_1 := h5055c.2.1
                                            have p5055_2 := h5055c.2.2.1
                                            have p5055_3 := h5055c.2.2.2
                                            linarith only [hlam, p5055_0]
                                          · have p5055_0 := h5055c.1
                                            have p5055_1 := h5055c.2.1
                                            have p5055_2 := h5055c.2.2.1
                                            have p5055_3 := h5055c.2.2.2
                                            linarith only [h5017, hlam, p5055_1]
                                          · have p5055_0 := h5055c.1
                                            have p5055_1 := h5055c.2.1
                                            have p5055_2 := h5055c.2.2.1
                                            have p5055_3 := h5055c.2.2.2
                                            linarith only [h3, h4749, h5011, hc12, hc45, hlam, hphi, ht23, ht34, p5055_1]
                                          · have p5055_0 := h5055c.1
                                            have p5055_1 := h5055c.2.1
                                            have p5055_2 := h5055c.2.2.1
                                            have p5055_3 := h5055c.2.2.2
                                            linarith only [h4749, h5011, hc12, hc45, hlam, hphi, ht23, ht34, p5055_1]
                                          · have p5055_0 := h5055c.1
                                            have p5055_1 := h5055c.2.1
                                            have p5055_2 := h5055c.2.2.1
                                            have p5055_3 := h5055c.2.2.2
                                            linarith only [h4749, h5015, hc12, hc45, hlam, hphi, ht23, ht34, p5055_1]
                                          · have p5055_0 := h5055c.1
                                            have p5055_1 := h5055c.2.1
                                            have p5055_2 := h5055c.2.2.1
                                            have p5055_3 := h5055c.2.2.2
                                            linarith only [h5017, hc34, hc45, hlam, hphi, p5055_1]
                                          · have p5055_0 := h5055c.1
                                            have p5055_1 := h5055c.2.1
                                            have p5055_2 := h5055c.2.2.1
                                            have p5055_3 := h5055c.2.2.2
                                            linarith only [hlam, p5055_0]
                                · linarith only [h4, h5046, hlam]
                              · have p5037_0 := h5037c.1
                                have p5037_1 := h5037c.2.1
                                have p5037_2 := h5037c.2.2.1
                                have p5037_3 := h5037c.2.2.2
                                rcases p5037_3 (m.d 0 3) (by simp) with h5082 | h5082
                                · rcases p5037_3 (m.d 1 3) (by simp) with h5083 | h5083
                                  · linarith only [h1, h5083, hlam]
                                  · linarith only [h5009, h5083, hlam]
                                · linarith only [h5082, hlam, p5037_0]
                              · have p5037_0 := h5037c.1
                                have p5037_1 := h5037c.2.1
                                have p5037_2 := h5037c.2.2.1
                                have p5037_3 := h5037c.2.2.2
                                rcases p5037_3 (m.d 0 3) (by simp) with h5087 | h5087
                                · rcases p5037_3 (m.d 1 3) (by simp) with h5088 | h5088
                                  · linarith only [h1, h5088, hlam]
                                  · linarith only [h5010, h5088, hlam]
                                · linarith only [h5087, hlam, p5037_0]
                              · have p5037_0 := h5037c.1
                                have p5037_1 := h5037c.2.1
                                have p5037_2 := h5037c.2.2.1
                                have p5037_3 := h5037c.2.2.2
                                linarith only [h1, hlam, p5037_0]
                              · have p5037_0 := h5037c.1
                                have p5037_1 := h5037c.2.1
                                have p5037_2 := h5037c.2.2.1
                                have p5037_3 := h5037c.2.2.2
                                linarith only [hlam, p5037_0]
                              · have p5037_0 := h5037c.1
                                have p5037_1 := h5037c.2.1
                                have p5037_2 := h5037c.2.2.1
                                have p5037_3 := h5037c.2.2.2
                                linarith only [h3976, hlam, p5037_1]
                              · have p5037_0 := h5037c.1
                                have p5037_1 := h5037c.2.1
                                have p5037_2 := h5037c.2.2.1
                                have p5037_3 := h5037c.2.2.2
                                linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5019_1, p5037_1]
                              · have p5037_0 := h5037c.1
                                have p5037_1 := h5037c.2.1
                                have p5037_2 := h5037c.2.2.1
                                have p5037_3 := h5037c.2.2.2
                                linarith only [hc01, hc35, hlam, hphi, ht0b, ht5b, p5019_1, p5037_1]
                              · have p5037_0 := h5037c.1
                                have p5037_1 := h5037c.2.1
                                have p5037_2 := h5037c.2.2.1
                                have p5037_3 := h5037c.2.2.2
                                linarith only [h4, hlam, p5037_0]
                              · have p5037_0 := h5037c.1
                                have p5037_1 := h5037c.2.1
                                have p5037_2 := h5037c.2.2.1
                                have p5037_3 := h5037c.2.2.2
                                linarith only [h0, h4, hlam, p5019_2, p5037_1]
                              · have p5037_0 := h5037c.1
                                have p5037_1 := h5037c.2.1
                                have p5037_2 := h5037c.2.2.1
                                have p5037_3 := h5037c.2.2.2
                                linarith only [hlam, p5037_0]
                              · have p5037_0 := h5037c.1
                                have p5037_1 := h5037c.2.1
                                have p5037_2 := h5037c.2.2.1
                                have p5037_3 := h5037c.2.2.2
                                rcases p5037_3 (m.d 0 3) (by simp) with h5100 | h5100
                                · rcases p5037_3 (m.d 1 3) (by simp) with h5101 | h5101
                                  · linarith only [h3976, h5101, hlam]
                                  · linarith only [h5009, h5101, hlam]
                                · linarith only [h5100, h7, hlam]
                              · have p5037_0 := h5037c.1
                                have p5037_1 := h5037c.2.1
                                have p5037_2 := h5037c.2.2.1
                                have p5037_3 := h5037c.2.2.2
                                rcases p5037_3 (m.d 0 3) (by simp) with h5105 | h5105
                                · rcases p5037_3 (m.d 1 3) (by simp) with h5106 | h5106
                                  · linarith only [h3976, h5106, hlam]
                                  · linarith only [h5010, h5106, hlam]
                                · linarith only [h5105, h8, hlam]
                              · have p5037_0 := h5037c.1
                                have p5037_1 := h5037c.2.1
                                have p5037_2 := h5037c.2.2.1
                                have p5037_3 := h5037c.2.2.2
                                linarith only [h7, hlam, p5037_0]
                              · have p5037_0 := h5037c.1
                                have p5037_1 := h5037c.2.1
                                have p5037_2 := h5037c.2.2.1
                                have p5037_3 := h5037c.2.2.2
                                linarith only [h5009, hlam, p5037_0]
                              · have p5037_0 := h5037c.1
                                have p5037_1 := h5037c.2.1
                                have p5037_2 := h5037c.2.2.1
                                have p5037_3 := h5037c.2.2.2
                                linarith only [h5013, hlam, p5037_0]
                              · have p5037_0 := h5037c.1
                                have p5037_1 := h5037c.2.1
                                have p5037_2 := h5037c.2.2.1
                                have p5037_3 := h5037c.2.2.2
                                linarith only [hlam, p5037_0]
                              · have p5037_0 := h5037c.1
                                have p5037_1 := h5037c.2.1
                                have p5037_2 := h5037c.2.2.1
                                have p5037_3 := h5037c.2.2.2
                                linarith only [h5017, hlam, p5037_1]
                              · have p5037_0 := h5037c.1
                                have p5037_1 := h5037c.2.1
                                have p5037_2 := h5037c.2.2.1
                                have p5037_3 := h5037c.2.2.2
                                linarith only [h8, hlam, p5037_0]
                              · have p5037_0 := h5037c.1
                                have p5037_1 := h5037c.2.1
                                have p5037_2 := h5037c.2.2.1
                                have p5037_3 := h5037c.2.2.2
                                linarith only [h5010, hlam, p5037_0]
                              · have p5037_0 := h5037c.1
                                have p5037_1 := h5037c.2.1
                                have p5037_2 := h5037c.2.2.1
                                have p5037_3 := h5037c.2.2.2
                                linarith only [h5014, hlam, p5037_0]
                              · have p5037_0 := h5037c.1
                                have p5037_1 := h5037c.2.1
                                have p5037_2 := h5037c.2.2.1
                                have p5037_3 := h5037c.2.2.2
                                linarith only [h5010, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5019_1, p5037_1]
                              · have p5037_0 := h5037c.1
                                have p5037_1 := h5037c.2.1
                                have p5037_2 := h5037c.2.2.1
                                have p5037_3 := h5037c.2.2.2
                                linarith only [hlam, p5037_0]
                    · linarith only [h5028, hlam, p5019_0]
                  · have p5019_0 := h5019c.1
                    have p5019_1 := h5019c.2.1
                    have p5019_2 := h5019c.2.2.1
                    have p5019_3 := h5019c.2.2.2
                    rcases p5019_3 (m.d 0 1) (by simp) with h5121 | h5121
                    · rcases p5019_3 (m.d 1 2) (by simp) with h5122 | h5122
                      · linarith only [h0, h5122, hlam]
                      · rcases p5019_3 (m.d 1 3) (by simp) with h5124 | h5124
                        · linarith only [h1, h5124, hlam]
                        · linarith only [h5009, h5124, hlam]
                    · linarith only [h5121, hlam, p5019_0]
                  · have p5019_0 := h5019c.1
                    have p5019_1 := h5019c.2.1
                    have p5019_2 := h5019c.2.2.1
                    have p5019_3 := h5019c.2.2.2
                    rcases p5019_3 (m.d 0 1) (by simp) with h5128 | h5128
                    · rcases p5019_3 (m.d 1 2) (by simp) with h5129 | h5129
                      · linarith only [h0, h5129, hlam]
                      · rcases p5019_3 (m.d 1 3) (by simp) with h5131 | h5131
                        · linarith only [h1, h5131, hlam]
                        · linarith only [h5010, h5131, hlam]
                    · linarith only [h5128, hlam, p5019_0]
                  · have p5019_0 := h5019c.1
                    have p5019_1 := h5019c.2.1
                    have p5019_2 := h5019c.2.2.1
                    have p5019_3 := h5019c.2.2.2
                    linarith only [h0, hlam, p5019_0]
                  · have p5019_0 := h5019c.1
                    have p5019_1 := h5019c.2.1
                    have p5019_2 := h5019c.2.2.1
                    have p5019_3 := h5019c.2.2.2
                    linarith only [hlam, p5019_0]
                  · have p5019_0 := h5019c.1
                    have p5019_1 := h5019c.2.1
                    have p5019_2 := h5019c.2.2.1
                    have p5019_3 := h5019c.2.2.2
                    linarith only [h3976, hlam, p5019_0]
                  · have p5019_0 := h5019c.1
                    have p5019_1 := h5019c.2.1
                    have p5019_2 := h5019c.2.2.1
                    have p5019_3 := h5019c.2.2.2
                    linarith only [h4749, hlam, p5019_0]
                  · have p5019_0 := h5019c.1
                    have p5019_1 := h5019c.2.1
                    have p5019_2 := h5019c.2.2.1
                    have p5019_3 := h5019c.2.2.2
                    linarith only [h4997, hlam, p5019_0]
                  · have p5019_0 := h5019c.1
                    have p5019_1 := h5019c.2.1
                    have p5019_2 := h5019c.2.2.1
                    have p5019_3 := h5019c.2.2.2
                    linarith only [h1, hlam, p5019_0]
                  · have p5019_0 := h5019c.1
                    have p5019_1 := h5019c.2.1
                    have p5019_2 := h5019c.2.2.1
                    have p5019_3 := h5019c.2.2.2
                    rcases p5019_3 (m.d 0 1) (by simp) with h5141 | h5141
                    · rcases p5019_3 (m.d 1 2) (by simp) with h5142 | h5142
                      · linarith only [h3976, h5142, hlam]
                      · rcases p5019_3 (m.d 1 3) (by simp) with h5144 | h5144
                        · rcases p5019_3 (m.d 1 4) (by simp) with h5145 | h5145
                          · linarith only [h5009, h5145, hlam]
                          · linarith only [h4749, h5145, hlam]
                        · linarith only [h3976, h5144, hlam]
                    · linarith only [h0, h5141, hlam]
                  · have p5019_0 := h5019c.1
                    have p5019_1 := h5019c.2.1
                    have p5019_2 := h5019c.2.2.1
                    have p5019_3 := h5019c.2.2.2
                    linarith only [hlam, p5019_0]
                  · have p5019_0 := h5019c.1
                    have p5019_1 := h5019c.2.1
                    have p5019_2 := h5019c.2.2.1
                    have p5019_3 := h5019c.2.2.2
                    rcases p5019_3 (m.d 0 1) (by simp) with h5151 | h5151
                    · rcases p5019_3 (m.d 1 2) (by simp) with h5152 | h5152
                      · linarith only [h3976, h5152, hlam]
                      · rcases p5019_3 (m.d 1 3) (by simp) with h5154 | h5154
                        · rcases p5019_3 (m.d 1 4) (by simp) with h5155 | h5155
                          · linarith only [h5009, h5155, hlam]
                          · rcases p5019_3 (m.d 1 5) (by simp) with h5157 | h5157
                            · linarith only [h5010, h5157, hlam]
                            · linarith only [h5011, h5157, hlam]
                        · linarith only [h5009, h5154, hlam]
                    · linarith only [h2, h5151, hlam]
                  · have p5019_0 := h5019c.1
                    have p5019_1 := h5019c.2.1
                    have p5019_2 := h5019c.2.2.1
                    have p5019_3 := h5019c.2.2.2
                    rcases p5019_3 (m.d 0 1) (by simp) with h5162 | h5162
                    · rcases p5019_3 (m.d 1 2) (by simp) with h5163 | h5163
                      · linarith only [h3976, h5163, hlam]
                      · rcases p5019_3 (m.d 1 3) (by simp) with h5165 | h5165
                        · rcases p5019_3 (m.d 1 4) (by simp) with h5166 | h5166
                          · linarith only [h5009, h5166, hlam]
                          · rcases p5019_3 (m.d 1 5) (by simp) with h5168 | h5168
                            · linarith only [h5010, h5168, hlam]
                            · rcases h3bigk with h5170c | h5170c | h5170c | h5170c | h5170c | h5170c | h5170c | h5170c | h5170c | h5170c | h5170c | h5170c | h5170c | h5170c | h5170c | h5170c | h5170c | h5170c | h5170c | h5170c | h5170c | h5170c | h5170c | h5170c | h5170c
                              · have p5170_0 := h5170c.1
                                have p5170_1 := h5170c.2.1
                                have p5170_2 := h5170c.2.2.1
                                have p5170_3 := h5170c.2.2.2
                                linarith only [hlam, p5170_0]
                              · have p5170_0 := h5170c.1
                                have p5170_1 := h5170c.2.1
                                have p5170_2 := h5170c.2.2.1
                                have p5170_3 := h5170c.2.2.2
                                linarith only [h5011, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b, p5019_1, p5170_1]
                              · have p5170_0 := h5170c.1
                                have p5170_1 := h5170c.2.1
                                have p5170_2 := h5170c.2.2.1
                                have p5170_3 := h5170c.2.2.2
                                linarith only [h0, h3976, h4, h5011, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p5019_1, p5170_1]
                              · have p5170_0 := h5170c.1
                                have p5170_1 := h5170c.2.1
                                have p5170_2 := h5170c.2.2.1
                                have p5170_3 := h5170c.2.2.2
                                rcases p5170_3 (m.d 0 3) (by simp) with h5174 | h5174
                                · rcases p5170_3 (m.d 1 3) (by simp) with h5175 | h5175
                                  · linarith only [h1, h5175, hlam]
                                  · linarith only [h5009, h5175, hlam]
                                · linarith only [h5174, hlam, p5170_0]
                              · have p5170_0 := h5170c.1
                                have p5170_1 := h5170c.2.1
                                have p5170_2 := h5170c.2.2.1
                                have p5170_3 := h5170c.2.2.2
                                rcases p5170_3 (m.d 0 3) (by simp) with h5179 | h5179
                                · rcases p5170_3 (m.d 1 3) (by simp) with h5180 | h5180
                                  · linarith only [h1, h5180, hlam]
                                  · linarith only [h5010, h5180, hlam]
                                · linarith only [h5179, hlam, p5170_0]
                              · have p5170_0 := h5170c.1
                                have p5170_1 := h5170c.2.1
                                have p5170_2 := h5170c.2.2.1
                                have p5170_3 := h5170c.2.2.2
                                linarith only [h1, hlam, p5170_0]
                              · have p5170_0 := h5170c.1
                                have p5170_1 := h5170c.2.1
                                have p5170_2 := h5170c.2.2.1
                                have p5170_3 := h5170c.2.2.2
                                linarith only [hlam, p5170_0]
                              · have p5170_0 := h5170c.1
                                have p5170_1 := h5170c.2.1
                                have p5170_2 := h5170c.2.2.1
                                have p5170_3 := h5170c.2.2.2
                                linarith only [h3976, hlam, p5170_1]
                              · have p5170_0 := h5170c.1
                                have p5170_1 := h5170c.2.1
                                have p5170_2 := h5170c.2.2.1
                                have p5170_3 := h5170c.2.2.2
                                rcases p5170_3 (m.d 0 3) (by simp) with h5187 | h5187
                                · rcases p5170_3 (m.d 1 3) (by simp) with h5188 | h5188
                                  · rcases p5170_3 (m.d 2 3) (by simp) with h5189 | h5189
                                    · rcases p5170_3 (m.d 3 4) (by simp) with h5190 | h5190
                                      · linarith only [h5190, hlam, p5170_0]
                                      · rcases p5170_3 (m.d 3 5) (by simp) with h5192 | h5192
                                        · linarith only [h5010, h5192, hlam]
                                        · linarith only [h5017, h5192, hlam]
                                    · linarith only [h5013, h5189, hlam]
                                  · linarith only [h5188, hlam, p5170_0]
                                · linarith only [h5187, h7, hlam]
                              · have p5170_0 := h5170c.1
                                have p5170_1 := h5170c.2.1
                                have p5170_2 := h5170c.2.2.1
                                have p5170_3 := h5170c.2.2.2
                                rcases p5170_3 (m.d 0 3) (by simp) with h5198 | h5198
                                · rcases p5170_3 (m.d 1 3) (by simp) with h5199 | h5199
                                  · rcases p5170_3 (m.d 2 3) (by simp) with h5200 | h5200
                                    · rcases p5170_3 (m.d 3 4) (by simp) with h5201 | h5201
                                      · linarith only [h5009, h5201, hlam]
                                      · rcases p5170_3 (m.d 3 5) (by simp) with h5203 | h5203
                                        · linarith only [h5203, hlam, p5170_0]
                                        · rcases h5bigk with h5205c | h5205c | h5205c | h5205c | h5205c | h5205c | h5205c | h5205c | h5205c | h5205c | h5205c | h5205c | h5205c | h5205c | h5205c | h5205c | h5205c | h5205c | h5205c | h5205c | h5205c | h5205c | h5205c | h5205c | h5205c
                                          · have p5205_0 := h5205c.1
                                            have p5205_1 := h5205c.2.1
                                            have p5205_2 := h5205c.2.2.1
                                            have p5205_3 := h5205c.2.2.2
                                            linarith only [hlam, p5205_0]
                                          · have p5205_0 := h5205c.1
                                            have p5205_1 := h5205c.2.1
                                            have p5205_2 := h5205c.2.2.1
                                            have p5205_3 := h5205c.2.2.2
                                            linarith only [h4749, h5011, h9, hc12, hc45, hlam, hphi, ht23, ht34, p5205_1]
                                          · have p5205_0 := h5205c.1
                                            have p5205_1 := h5205c.2.1
                                            have p5205_2 := h5205c.2.2.1
                                            have p5205_3 := h5205c.2.2.2
                                            linarith only [h4997, h9, hc12, hc45, hlam, hphi, ht23, ht34, p5205_1]
                                          · have p5205_0 := h5205c.1
                                            have p5205_1 := h5205c.2.1
                                            have p5205_2 := h5205c.2.2.1
                                            have p5205_3 := h5205c.2.2.2
                                            linarith only [h5017, h9, hc34, hc45, hlam, hphi, p5205_1]
                                          · have p5205_0 := h5205c.1
                                            have p5205_1 := h5205c.2.1
                                            have p5205_2 := h5205c.2.2.1
                                            have p5205_3 := h5205c.2.2.2
                                            linarith only [h9, hlam, p5205_1]
                                          · have p5205_0 := h5205c.1
                                            have p5205_1 := h5205c.2.1
                                            have p5205_2 := h5205c.2.2.1
                                            have p5205_3 := h5205c.2.2.2
                                            linarith only [h3, hlam, p5205_0]
                                          · have p5205_0 := h5205c.1
                                            have p5205_1 := h5205c.2.1
                                            have p5205_2 := h5205c.2.2.1
                                            have p5205_3 := h5205c.2.2.2
                                            linarith only [hlam, p5205_0]
                                          · have p5205_0 := h5205c.1
                                            have p5205_1 := h5205c.2.1
                                            have p5205_2 := h5205c.2.2.1
                                            have p5205_3 := h5205c.2.2.2
                                            linarith only [h4997, hlam, p5205_0]
                                          · have p5205_0 := h5205c.1
                                            have p5205_1 := h5205c.2.1
                                            have p5205_2 := h5205c.2.2.1
                                            have p5205_3 := h5205c.2.2.2
                                            linarith only [h5017, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5019_1, p5205_1]
                                          · have p5205_0 := h5205c.1
                                            have p5205_1 := h5205c.2.1
                                            have p5205_2 := h5205c.2.2.1
                                            have p5205_3 := h5205c.2.2.2
                                            linarith only [h5011, hlam, p5205_1]
                                          · have p5205_0 := h5205c.1
                                            have p5205_1 := h5205c.2.1
                                            have p5205_2 := h5205c.2.2.1
                                            have p5205_3 := h5205c.2.2.2
                                            linarith only [h6, hlam, p5205_1]
                                          · have p5205_0 := h5205c.1
                                            have p5205_1 := h5205c.2.1
                                            have p5205_2 := h5205c.2.2.1
                                            have p5205_3 := h5205c.2.2.2
                                            linarith only [h0, h6, hc01, hc15, hlam, hphi, ht0b, ht5b, p5205_1]
                                          · have p5205_0 := h5205c.1
                                            have p5205_1 := h5205c.2.1
                                            have p5205_2 := h5205c.2.2.1
                                            have p5205_3 := h5205c.2.2.2
                                            linarith only [hlam, p5205_0]
                                          · have p5205_0 := h5205c.1
                                            have p5205_1 := h5205c.2.1
                                            have p5205_2 := h5205c.2.2.1
                                            have p5205_3 := h5205c.2.2.2
                                            linarith only [h0, h4, h5014, h5017, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5205_1]
                                          · have p5205_0 := h5205c.1
                                            have p5205_1 := h5205c.2.1
                                            have p5205_2 := h5205c.2.2.1
                                            have p5205_3 := h5205c.2.2.2
                                            linarith only [h5015, hlam, p5205_1]
                                          · have p5205_0 := h5205c.1
                                            have p5205_1 := h5205c.2.1
                                            have p5205_2 := h5205c.2.2.1
                                            have p5205_3 := h5205c.2.2.2
                                            linarith only [h8, hlam, p5205_0]
                                          · have p5205_0 := h5205c.1
                                            have p5205_1 := h5205c.2.1
                                            have p5205_2 := h5205c.2.2.1
                                            have p5205_3 := h5205c.2.2.2
                                            linarith only [h5010, hlam, p5205_0]
                                          · have p5205_0 := h5205c.1
                                            have p5205_1 := h5205c.2.1
                                            have p5205_2 := h5205c.2.2.1
                                            have p5205_3 := h5205c.2.2.2
                                            linarith only [h5014, hlam, p5205_0]
                                          · have p5205_0 := h5205c.1
                                            have p5205_1 := h5205c.2.1
                                            have p5205_2 := h5205c.2.2.1
                                            have p5205_3 := h5205c.2.2.2
                                            linarith only [hlam, p5205_0]
                                          · have p5205_0 := h5205c.1
                                            have p5205_1 := h5205c.2.1
                                            have p5205_2 := h5205c.2.2.1
                                            have p5205_3 := h5205c.2.2.2
                                            linarith only [h5017, hlam, p5205_1]
                                          · have p5205_0 := h5205c.1
                                            have p5205_1 := h5205c.2.1
                                            have p5205_2 := h5205c.2.2.1
                                            have p5205_3 := h5205c.2.2.2
                                            linarith only [h3, h4749, h5011, hc12, hc45, hlam, hphi, ht23, ht34, p5205_1]
                                          · have p5205_0 := h5205c.1
                                            have p5205_1 := h5205c.2.1
                                            have p5205_2 := h5205c.2.2.1
                                            have p5205_3 := h5205c.2.2.2
                                            linarith only [h4749, h5011, hc12, hc45, hlam, hphi, ht23, ht34, p5205_1]
                                          · have p5205_0 := h5205c.1
                                            have p5205_1 := h5205c.2.1
                                            have p5205_2 := h5205c.2.2.1
                                            have p5205_3 := h5205c.2.2.2
                                            linarith only [h4997, hc12, hc45, hlam, hphi, ht23, ht34, p5205_1]
                                          · have p5205_0 := h5205c.1
                                            have p5205_1 := h5205c.2.1
                                            have p5205_2 := h5205c.2.2.1
                                            have p5205_3 := h5205c.2.2.2
                                            linarith only [h5017, hc34, hc45, hlam, hphi, p5205_1]
                                          · have p5205_0 := h5205c.1
                                            have p5205_1 := h5205c.2.1
                                            have p5205_2 := h5205c.2.2.1
                                            have p5205_3 := h5205c.2.2.2
                                            linarith only [hlam, p5205_0]
                                    · linarith only [h5014, h5200, hlam]
                                  · linarith only [h5199, hlam, p5170_0]
                                · linarith only [h5198, h8, hlam]
                              · have p5170_0 := h5170c.1
                                have p5170_1 := h5170c.2.1
                                have p5170_2 := h5170c.2.2.1
                                have p5170_3 := h5170c.2.2.2
                                linarith only [h4, hlam, p5170_0]
                              · have p5170_0 := h5170c.1
                                have p5170_1 := h5170c.2.1
                                have p5170_2 := h5170c.2.2.1
                                have p5170_3 := h5170c.2.2.2
                                linarith only [h0, h4, h5009, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5170_1]
                              · have p5170_0 := h5170c.1
                                have p5170_1 := h5170c.2.1
                                have p5170_2 := h5170c.2.2.1
                                have p5170_3 := h5170c.2.2.2
                                linarith only [hlam, p5170_0]
                              · have p5170_0 := h5170c.1
                                have p5170_1 := h5170c.2.1
                                have p5170_2 := h5170c.2.2.1
                                have p5170_3 := h5170c.2.2.2
                                rcases p5170_3 (m.d 0 3) (by simp) with h5237 | h5237
                                · rcases p5170_3 (m.d 1 3) (by simp) with h5238 | h5238
                                  · linarith only [h3976, h5238, hlam]
                                  · linarith only [h5009, h5238, hlam]
                                · linarith only [h5237, h7, hlam]
                              · have p5170_0 := h5170c.1
                                have p5170_1 := h5170c.2.1
                                have p5170_2 := h5170c.2.2.1
                                have p5170_3 := h5170c.2.2.2
                                rcases p5170_3 (m.d 0 3) (by simp) with h5242 | h5242
                                · rcases p5170_3 (m.d 1 3) (by simp) with h5243 | h5243
                                  · linarith only [h3976, h5243, hlam]
                                  · linarith only [h5010, h5243, hlam]
                                · linarith only [h5242, h8, hlam]
                              · have p5170_0 := h5170c.1
                                have p5170_1 := h5170c.2.1
                                have p5170_2 := h5170c.2.2.1
                                have p5170_3 := h5170c.2.2.2
                                linarith only [h7, hlam, p5170_0]
                              · have p5170_0 := h5170c.1
                                have p5170_1 := h5170c.2.1
                                have p5170_2 := h5170c.2.2.1
                                have p5170_3 := h5170c.2.2.2
                                linarith only [h5009, hlam, p5170_0]
                              · have p5170_0 := h5170c.1
                                have p5170_1 := h5170c.2.1
                                have p5170_2 := h5170c.2.2.1
                                have p5170_3 := h5170c.2.2.2
                                linarith only [h5013, hlam, p5170_0]
                              · have p5170_0 := h5170c.1
                                have p5170_1 := h5170c.2.1
                                have p5170_2 := h5170c.2.2.1
                                have p5170_3 := h5170c.2.2.2
                                linarith only [hlam, p5170_0]
                              · have p5170_0 := h5170c.1
                                have p5170_1 := h5170c.2.1
                                have p5170_2 := h5170c.2.2.1
                                have p5170_3 := h5170c.2.2.2
                                linarith only [h5017, hlam, p5170_1]
                              · have p5170_0 := h5170c.1
                                have p5170_1 := h5170c.2.1
                                have p5170_2 := h5170c.2.2.1
                                have p5170_3 := h5170c.2.2.2
                                linarith only [h8, hlam, p5170_0]
                              · have p5170_0 := h5170c.1
                                have p5170_1 := h5170c.2.1
                                have p5170_2 := h5170c.2.2.1
                                have p5170_3 := h5170c.2.2.2
                                linarith only [h5010, hlam, p5170_0]
                              · have p5170_0 := h5170c.1
                                have p5170_1 := h5170c.2.1
                                have p5170_2 := h5170c.2.2.1
                                have p5170_3 := h5170c.2.2.2
                                linarith only [h5014, hlam, p5170_0]
                              · have p5170_0 := h5170c.1
                                have p5170_1 := h5170c.2.1
                                have p5170_2 := h5170c.2.2.1
                                have p5170_3 := h5170c.2.2.2
                                linarith only [h1, h5010, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5170_1]
                              · have p5170_0 := h5170c.1
                                have p5170_1 := h5170c.2.1
                                have p5170_2 := h5170c.2.2.1
                                have p5170_3 := h5170c.2.2.2
                                linarith only [hlam, p5170_0]
                        · linarith only [h5010, h5165, hlam]
                    · linarith only [h3, h5162, hlam]
                  · have p5019_0 := h5019c.1
                    have p5019_1 := h5019c.2.1
                    have p5019_2 := h5019c.2.2.1
                    have p5019_3 := h5019c.2.2.2
                    linarith only [h2, hlam, p5019_0]
                  · have p5019_0 := h5019c.1
                    have p5019_1 := h5019c.2.1
                    have p5019_2 := h5019c.2.2.1
                    have p5019_3 := h5019c.2.2.2
                    linarith only [h2, h9, hc12, hc45, hlam, hphi, ht23, ht34, p5019_1]
                  · have p5019_0 := h5019c.1
                    have p5019_1 := h5019c.2.1
                    have p5019_2 := h5019c.2.2.1
                    have p5019_3 := h5019c.2.2.2
                    linarith only [h5009, hlam, p5019_0]
                  · have p5019_0 := h5019c.1
                    have p5019_1 := h5019c.2.1
                    have p5019_2 := h5019c.2.2.1
                    have p5019_3 := h5019c.2.2.2
                    linarith only [hlam, p5019_0]
                  · have p5019_0 := h5019c.1
                    have p5019_1 := h5019c.2.1
                    have p5019_2 := h5019c.2.2.1
                    have p5019_3 := h5019c.2.2.2
                    linarith only [h5011, hlam, p5019_1]
                  · have p5019_0 := h5019c.1
                    have p5019_1 := h5019c.2.1
                    have p5019_2 := h5019c.2.2.1
                    have p5019_3 := h5019c.2.2.2
                    linarith only [h3, hlam, p5019_0]
                  · have p5019_0 := h5019c.1
                    have p5019_1 := h5019c.2.1
                    have p5019_2 := h5019c.2.2.1
                    have p5019_3 := h5019c.2.2.2
                    rcases p5019_3 (m.d 0 1) (by simp) with h5265 | h5265
                    · rcases p5019_3 (m.d 1 2) (by simp) with h5266 | h5266
                      · linarith only [h4997, h5266, hlam]
                      · rcases p5019_3 (m.d 1 3) (by simp) with h5268 | h5268
                        · rcases p5019_3 (m.d 1 4) (by simp) with h5269 | h5269
                          · linarith only [h5011, h5269, hlam]
                          · linarith only [h4749, h5269, hlam]
                        · linarith only [h3976, h5268, hlam]
                    · linarith only [h0, h5265, hlam]
                  · have p5019_0 := h5019c.1
                    have p5019_1 := h5019c.2.1
                    have p5019_2 := h5019c.2.2.1
                    have p5019_3 := h5019c.2.2.2
                    linarith only [h5010, hlam, p5019_0]
                  · have p5019_0 := h5019c.1
                    have p5019_1 := h5019c.2.1
                    have p5019_2 := h5019c.2.2.1
                    have p5019_3 := h5019c.2.2.2
                    rcases p5019_3 (m.d 0 1) (by simp) with h5275 | h5275
                    · rcases p5019_3 (m.d 1 2) (by simp) with h5276 | h5276
                      · linarith only [h4997, h5276, hlam]
                      · rcases p5019_3 (m.d 1 3) (by simp) with h5278 | h5278
                        · rcases p5019_3 (m.d 1 4) (by simp) with h5279 | h5279
                          · linarith only [h5011, h5279, hlam]
                          · rcases p5019_3 (m.d 1 5) (by simp) with h5281 | h5281
                            · rcases h3bigk with h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c | h5282c
                              · have p5282_0 := h5282c.1
                                have p5282_1 := h5282c.2.1
                                have p5282_2 := h5282c.2.2.1
                                have p5282_3 := h5282c.2.2.2
                                linarith only [hlam, p5282_0]
                              · have p5282_0 := h5282c.1
                                have p5282_1 := h5282c.2.1
                                have p5282_2 := h5282c.2.2.1
                                have p5282_3 := h5282c.2.2.2
                                linarith only [h0, h4, h4749, h5010, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5019_1, p5282_1]
                              · have p5282_0 := h5282c.1
                                have p5282_1 := h5282c.2.1
                                have p5282_2 := h5282c.2.2.1
                                have p5282_3 := h5282c.2.2.2
                                linarith only [h0, h3976, h4, h4749, h5010, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5019_1, p5282_1]
                              · have p5282_0 := h5282c.1
                                have p5282_1 := h5282c.2.1
                                have p5282_2 := h5282c.2.2.1
                                have p5282_3 := h5282c.2.2.2
                                rcases p5282_3 (m.d 0 3) (by simp) with h5286 | h5286
                                · rcases p5282_3 (m.d 1 3) (by simp) with h5287 | h5287
                                  · linarith only [h1, h5287, hlam]
                                  · linarith only [h5009, h5287, hlam]
                                · linarith only [h5286, hlam, p5282_0]
                              · have p5282_0 := h5282c.1
                                have p5282_1 := h5282c.2.1
                                have p5282_2 := h5282c.2.2.1
                                have p5282_3 := h5282c.2.2.2
                                rcases p5282_3 (m.d 0 3) (by simp) with h5291 | h5291
                                · rcases p5282_3 (m.d 1 3) (by simp) with h5292 | h5292
                                  · linarith only [h1, h5292, hlam]
                                  · linarith only [h5010, h5292, hlam]
                                · linarith only [h5291, hlam, p5282_0]
                              · have p5282_0 := h5282c.1
                                have p5282_1 := h5282c.2.1
                                have p5282_2 := h5282c.2.2.1
                                have p5282_3 := h5282c.2.2.2
                                linarith only [h1, hlam, p5282_0]
                              · have p5282_0 := h5282c.1
                                have p5282_1 := h5282c.2.1
                                have p5282_2 := h5282c.2.2.1
                                have p5282_3 := h5282c.2.2.2
                                linarith only [hlam, p5282_0]
                              · have p5282_0 := h5282c.1
                                have p5282_1 := h5282c.2.1
                                have p5282_2 := h5282c.2.2.1
                                have p5282_3 := h5282c.2.2.2
                                linarith only [h3976, hlam, p5282_1]
                              · have p5282_0 := h5282c.1
                                have p5282_1 := h5282c.2.1
                                have p5282_2 := h5282c.2.2.1
                                have p5282_3 := h5282c.2.2.2
                                rcases p5282_3 (m.d 0 3) (by simp) with h5299 | h5299
                                · rcases p5282_3 (m.d 1 3) (by simp) with h5300 | h5300
                                  · rcases p5282_3 (m.d 2 3) (by simp) with h5301 | h5301
                                    · rcases p5282_3 (m.d 3 4) (by simp) with h5302 | h5302
                                      · linarith only [h5302, hlam, p5282_0]
                                      · rcases p5282_3 (m.d 3 5) (by simp) with h5304 | h5304
                                        · linarith only [h5010, h5304, hlam]
                                        · linarith only [h5017, h5304, hlam]
                                    · linarith only [h5013, h5301, hlam]
                                  · linarith only [h5300, hlam, p5282_0]
                                · linarith only [h5299, h7, hlam]
                              · have p5282_0 := h5282c.1
                                have p5282_1 := h5282c.2.1
                                have p5282_2 := h5282c.2.2.1
                                have p5282_3 := h5282c.2.2.2
                                rcases p5282_3 (m.d 0 3) (by simp) with h5310 | h5310
                                · rcases p5282_3 (m.d 1 3) (by simp) with h5311 | h5311
                                  · rcases p5282_3 (m.d 2 3) (by simp) with h5312 | h5312
                                    · rcases p5282_3 (m.d 3 4) (by simp) with h5313 | h5313
                                      · linarith only [h5009, h5313, hlam]
                                      · rcases p5282_3 (m.d 3 5) (by simp) with h5315 | h5315
                                        · linarith only [h5315, hlam, p5282_0]
                                        · rcases h5bigk with h5317c | h5317c | h5317c | h5317c | h5317c | h5317c | h5317c | h5317c | h5317c | h5317c | h5317c | h5317c | h5317c | h5317c | h5317c | h5317c | h5317c | h5317c | h5317c | h5317c | h5317c | h5317c | h5317c | h5317c | h5317c
                                          · have p5317_0 := h5317c.1
                                            have p5317_1 := h5317c.2.1
                                            have p5317_2 := h5317c.2.2.1
                                            have p5317_3 := h5317c.2.2.2
                                            linarith only [hlam, p5317_0]
                                          · have p5317_0 := h5317c.1
                                            have p5317_1 := h5317c.2.1
                                            have p5317_2 := h5317c.2.2.1
                                            have p5317_3 := h5317c.2.2.2
                                            linarith only [h4749, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5019_1, p5317_1]
                                          · have p5317_0 := h5317c.1
                                            have p5317_1 := h5317c.2.1
                                            have p5317_2 := h5317c.2.2.1
                                            have p5317_3 := h5317c.2.2.2
                                            linarith only [h0, h4749, h4997, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5019_1, p5317_1]
                                          · have p5317_0 := h5317c.1
                                            have p5317_1 := h5317c.2.1
                                            have p5317_2 := h5317c.2.2.1
                                            have p5317_3 := h5317c.2.2.2
                                            linarith only [h5017, h9, hc34, hc45, hlam, hphi, p5317_1]
                                          · have p5317_0 := h5317c.1
                                            have p5317_1 := h5317c.2.1
                                            have p5317_2 := h5317c.2.2.1
                                            have p5317_3 := h5317c.2.2.2
                                            linarith only [h9, hlam, p5317_1]
                                          · have p5317_0 := h5317c.1
                                            have p5317_1 := h5317c.2.1
                                            have p5317_2 := h5317c.2.2.1
                                            have p5317_3 := h5317c.2.2.2
                                            linarith only [h3, hlam, p5317_0]
                                          · have p5317_0 := h5317c.1
                                            have p5317_1 := h5317c.2.1
                                            have p5317_2 := h5317c.2.2.1
                                            have p5317_3 := h5317c.2.2.2
                                            linarith only [hlam, p5317_0]
                                          · have p5317_0 := h5317c.1
                                            have p5317_1 := h5317c.2.1
                                            have p5317_2 := h5317c.2.2.1
                                            have p5317_3 := h5317c.2.2.2
                                            linarith only [h4997, hlam, p5317_0]
                                          · have p5317_0 := h5317c.1
                                            have p5317_1 := h5317c.2.1
                                            have p5317_2 := h5317c.2.2.1
                                            have p5317_3 := h5317c.2.2.2
                                            linarith only [h1, h5010, h5017, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5317_1]
                                          · have p5317_0 := h5317c.1
                                            have p5317_1 := h5317c.2.1
                                            have p5317_2 := h5317c.2.2.1
                                            have p5317_3 := h5317c.2.2.2
                                            linarith only [h5011, hlam, p5317_1]
                                          · have p5317_0 := h5317c.1
                                            have p5317_1 := h5317c.2.1
                                            have p5317_2 := h5317c.2.2.1
                                            have p5317_3 := h5317c.2.2.2
                                            linarith only [h6, hlam, p5317_1]
                                          · have p5317_0 := h5317c.1
                                            have p5317_1 := h5317c.2.1
                                            have p5317_2 := h5317c.2.2.1
                                            have p5317_3 := h5317c.2.2.2
                                            linarith only [h0, h6, hc01, hc15, hlam, hphi, ht0b, ht5b, p5317_1]
                                          · have p5317_0 := h5317c.1
                                            have p5317_1 := h5317c.2.1
                                            have p5317_2 := h5317c.2.2.1
                                            have p5317_3 := h5317c.2.2.2
                                            linarith only [hlam, p5317_0]
                                          · have p5317_0 := h5317c.1
                                            have p5317_1 := h5317c.2.1
                                            have p5317_2 := h5317c.2.2.1
                                            have p5317_3 := h5317c.2.2.2
                                            linarith only [h0, h4, h5014, h5017, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5317_1]
                                          · have p5317_0 := h5317c.1
                                            have p5317_1 := h5317c.2.1
                                            have p5317_2 := h5317c.2.2.1
                                            have p5317_3 := h5317c.2.2.2
                                            linarith only [h5015, hlam, p5317_1]
                                          · have p5317_0 := h5317c.1
                                            have p5317_1 := h5317c.2.1
                                            have p5317_2 := h5317c.2.2.1
                                            have p5317_3 := h5317c.2.2.2
                                            linarith only [h8, hlam, p5317_0]
                                          · have p5317_0 := h5317c.1
                                            have p5317_1 := h5317c.2.1
                                            have p5317_2 := h5317c.2.2.1
                                            have p5317_3 := h5317c.2.2.2
                                            linarith only [h5010, hlam, p5317_0]
                                          · have p5317_0 := h5317c.1
                                            have p5317_1 := h5317c.2.1
                                            have p5317_2 := h5317c.2.2.1
                                            have p5317_3 := h5317c.2.2.2
                                            linarith only [h5014, hlam, p5317_0]
                                          · have p5317_0 := h5317c.1
                                            have p5317_1 := h5317c.2.1
                                            have p5317_2 := h5317c.2.2.1
                                            have p5317_3 := h5317c.2.2.2
                                            linarith only [hlam, p5317_0]
                                          · have p5317_0 := h5317c.1
                                            have p5317_1 := h5317c.2.1
                                            have p5317_2 := h5317c.2.2.1
                                            have p5317_3 := h5317c.2.2.2
                                            linarith only [h5017, hlam, p5317_1]
                                          · have p5317_0 := h5317c.1
                                            have p5317_1 := h5317c.2.1
                                            have p5317_2 := h5317c.2.2.1
                                            have p5317_3 := h5317c.2.2.2
                                            linarith only [h3, h4749, hc12, hc45, hlam, hphi, ht23, ht34, p5019_1, p5317_1]
                                          · have p5317_0 := h5317c.1
                                            have p5317_1 := h5317c.2.1
                                            have p5317_2 := h5317c.2.2.1
                                            have p5317_3 := h5317c.2.2.2
                                            linarith only [h4749, hc12, hc45, hlam, hphi, ht23, ht34, p5019_1, p5317_1]
                                          · have p5317_0 := h5317c.1
                                            have p5317_1 := h5317c.2.1
                                            have p5317_2 := h5317c.2.2.1
                                            have p5317_3 := h5317c.2.2.2
                                            linarith only [h4749, h4997, hc12, hc45, hlam, hphi, ht23, ht34, p5019_1, p5317_1]
                                          · have p5317_0 := h5317c.1
                                            have p5317_1 := h5317c.2.1
                                            have p5317_2 := h5317c.2.2.1
                                            have p5317_3 := h5317c.2.2.2
                                            linarith only [h5017, hc34, hc45, hlam, hphi, p5317_1]
                                          · have p5317_0 := h5317c.1
                                            have p5317_1 := h5317c.2.1
                                            have p5317_2 := h5317c.2.2.1
                                            have p5317_3 := h5317c.2.2.2
                                            linarith only [hlam, p5317_0]
                                    · linarith only [h5014, h5312, hlam]
                                  · linarith only [h5311, hlam, p5282_0]
                                · linarith only [h5310, h8, hlam]
                              · have p5282_0 := h5282c.1
                                have p5282_1 := h5282c.2.1
                                have p5282_2 := h5282c.2.2.1
                                have p5282_3 := h5282c.2.2.2
                                linarith only [h4, hlam, p5282_0]
                              · have p5282_0 := h5282c.1
                                have p5282_1 := h5282c.2.1
                                have p5282_2 := h5282c.2.2.1
                                have p5282_3 := h5282c.2.2.2
                                linarith only [h0, h4, h5009, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5282_1]
                              · have p5282_0 := h5282c.1
                                have p5282_1 := h5282c.2.1
                                have p5282_2 := h5282c.2.2.1
                                have p5282_3 := h5282c.2.2.2
                                linarith only [hlam, p5282_0]
                              · have p5282_0 := h5282c.1
                                have p5282_1 := h5282c.2.1
                                have p5282_2 := h5282c.2.2.1
                                have p5282_3 := h5282c.2.2.2
                                rcases p5282_3 (m.d 0 3) (by simp) with h5349 | h5349
                                · rcases p5282_3 (m.d 1 3) (by simp) with h5350 | h5350
                                  · linarith only [h3976, h5350, hlam]
                                  · linarith only [h5009, h5350, hlam]
                                · linarith only [h5349, h7, hlam]
                              · have p5282_0 := h5282c.1
                                have p5282_1 := h5282c.2.1
                                have p5282_2 := h5282c.2.2.1
                                have p5282_3 := h5282c.2.2.2
                                rcases p5282_3 (m.d 0 3) (by simp) with h5354 | h5354
                                · rcases p5282_3 (m.d 1 3) (by simp) with h5355 | h5355
                                  · linarith only [h3976, h5355, hlam]
                                  · linarith only [h5010, h5355, hlam]
                                · linarith only [h5354, h8, hlam]
                              · have p5282_0 := h5282c.1
                                have p5282_1 := h5282c.2.1
                                have p5282_2 := h5282c.2.2.1
                                have p5282_3 := h5282c.2.2.2
                                linarith only [h7, hlam, p5282_0]
                              · have p5282_0 := h5282c.1
                                have p5282_1 := h5282c.2.1
                                have p5282_2 := h5282c.2.2.1
                                have p5282_3 := h5282c.2.2.2
                                linarith only [h5009, hlam, p5282_0]
                              · have p5282_0 := h5282c.1
                                have p5282_1 := h5282c.2.1
                                have p5282_2 := h5282c.2.2.1
                                have p5282_3 := h5282c.2.2.2
                                linarith only [h5013, hlam, p5282_0]
                              · have p5282_0 := h5282c.1
                                have p5282_1 := h5282c.2.1
                                have p5282_2 := h5282c.2.2.1
                                have p5282_3 := h5282c.2.2.2
                                linarith only [hlam, p5282_0]
                              · have p5282_0 := h5282c.1
                                have p5282_1 := h5282c.2.1
                                have p5282_2 := h5282c.2.2.1
                                have p5282_3 := h5282c.2.2.2
                                linarith only [h5017, hlam, p5282_1]
                              · have p5282_0 := h5282c.1
                                have p5282_1 := h5282c.2.1
                                have p5282_2 := h5282c.2.2.1
                                have p5282_3 := h5282c.2.2.2
                                linarith only [h8, hlam, p5282_0]
                              · have p5282_0 := h5282c.1
                                have p5282_1 := h5282c.2.1
                                have p5282_2 := h5282c.2.2.1
                                have p5282_3 := h5282c.2.2.2
                                linarith only [h5010, hlam, p5282_0]
                              · have p5282_0 := h5282c.1
                                have p5282_1 := h5282c.2.1
                                have p5282_2 := h5282c.2.2.1
                                have p5282_3 := h5282c.2.2.2
                                linarith only [h5014, hlam, p5282_0]
                              · have p5282_0 := h5282c.1
                                have p5282_1 := h5282c.2.1
                                have p5282_2 := h5282c.2.2.1
                                have p5282_3 := h5282c.2.2.2
                                linarith only [h1, h5010, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5282_1]
                              · have p5282_0 := h5282c.1
                                have p5282_1 := h5282c.2.1
                                have p5282_2 := h5282c.2.2.1
                                have p5282_3 := h5282c.2.2.2
                                linarith only [hlam, p5282_0]
                            · linarith only [h5011, h5281, hlam]
                        · linarith only [h5009, h5278, hlam]
                    · linarith only [h2, h5275, hlam]
                  · have p5019_0 := h5019c.1
                    have p5019_1 := h5019c.2.1
                    have p5019_2 := h5019c.2.2.1
                    have p5019_3 := h5019c.2.2.2
                    linarith only [hlam, p5019_0]
            · linarith only [h3976, h5010, h5014, hlam]
          · linarith only [h3976, h5013, h7, h9, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h5375 | h5375
        · linarith only [h2, h5375, h9, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h5377 | h5377
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5378 | h5378
            · linarith only [h0, h4, h5009, h5010, h5378, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h5380 | h5380
              · linarith only [h5377, h5378, h5380, h8, h9, hc03, hc04, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h5382 | h5382
                · linarith only [h4749, h5377, h5378, h5382, h8, h9, hc12, hc34, hlam, hphi, ht23]
                · rcases h1bigk with h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c
                  · have p5384_0 := h5384c.1
                    have p5384_1 := h5384c.2.1
                    have p5384_2 := h5384c.2.2.1
                    have p5384_3 := h5384c.2.2.2
                    linarith only [hlam, p5384_0]
                  · have p5384_0 := h5384c.1
                    have p5384_1 := h5384c.2.1
                    have p5384_2 := h5384c.2.2.1
                    have p5384_3 := h5384c.2.2.2
                    linarith only [h0, h4, h4749, h5377, h5378, h8, hlam, p5384_2]
                  · have p5384_0 := h5384c.1
                    have p5384_1 := h5384c.2.1
                    have p5384_2 := h5384c.2.2.1
                    have p5384_3 := h5384c.2.2.2
                    rcases p5384_3 (m.d 0 1) (by simp) with h5387 | h5387
                    · rcases p5384_3 (m.d 1 2) (by simp) with h5388 | h5388
                      · linarith only [h0, h5388, hlam]
                      · rcases p5384_3 (m.d 1 3) (by simp) with h5390 | h5390
                        · linarith only [h5390, hlam, p5384_0]
                        · rcases p5384_3 (m.d 1 4) (by simp) with h5392 | h5392
                          · linarith only [h2, h5392, hlam]
                          · rcases p5384_3 (m.d 1 5) (by simp) with h5394 | h5394
                            · linarith only [h3, h5394, hlam]
                            · linarith only [h5010, h5394, hlam]
                    · linarith only [h5387, hlam, p5384_0]
                  · have p5384_0 := h5384c.1
                    have p5384_1 := h5384c.2.1
                    have p5384_2 := h5384c.2.2.1
                    have p5384_3 := h5384c.2.2.2
                    rcases p5384_3 (m.d 0 1) (by simp) with h5398 | h5398
                    · rcases p5384_3 (m.d 1 2) (by simp) with h5399 | h5399
                      · linarith only [h0, h5399, hlam]
                      · rcases p5384_3 (m.d 1 3) (by simp) with h5401 | h5401
                        · linarith only [h1, h5401, hlam]
                        · linarith only [h5009, h5401, hlam]
                    · linarith only [h5398, hlam, p5384_0]
                  · have p5384_0 := h5384c.1
                    have p5384_1 := h5384c.2.1
                    have p5384_2 := h5384c.2.2.1
                    have p5384_3 := h5384c.2.2.2
                    rcases p5384_3 (m.d 0 1) (by simp) with h5405 | h5405
                    · rcases p5384_3 (m.d 1 2) (by simp) with h5406 | h5406
                      · linarith only [h0, h5406, hlam]
                      · rcases p5384_3 (m.d 1 3) (by simp) with h5408 | h5408
                        · linarith only [h1, h5408, hlam]
                        · rcases p5384_3 (m.d 1 4) (by simp) with h5410 | h5410
                          · linarith only [h2, h5410, hlam]
                          · rcases p5384_3 (m.d 1 5) (by simp) with h5412 | h5412
                            · linarith only [h5412, hlam, p5384_0]
                            · rcases h3bigk with h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c
                              · have p5414_0 := h5414c.1
                                have p5414_1 := h5414c.2.1
                                have p5414_2 := h5414c.2.2.1
                                have p5414_3 := h5414c.2.2.2
                                linarith only [hlam, p5414_0]
                              · have p5414_0 := h5414c.1
                                have p5414_1 := h5414c.2.1
                                have p5414_2 := h5414c.2.2.1
                                have p5414_3 := h5414c.2.2.2
                                rcases p5414_3 (m.d 0 3) (by simp) with h5416 | h5416
                                · rcases p5414_3 (m.d 1 3) (by simp) with h5417 | h5417
                                  · linarith only [h1, h5417, hlam]
                                  · rcases p5414_3 (m.d 2 3) (by simp) with h5419 | h5419
                                    · linarith only [h4, h5419, hlam]
                                    · linarith only [h3976, h5419, hlam]
                                · linarith only [h1, h5416, hlam]
                              · have p5414_0 := h5414c.1
                                have p5414_1 := h5414c.2.1
                                have p5414_2 := h5414c.2.2.1
                                have p5414_3 := h5414c.2.2.2
                                rcases p5414_3 (m.d 0 3) (by simp) with h5423 | h5423
                                · rcases p5414_3 (m.d 1 3) (by simp) with h5424 | h5424
                                  · linarith only [h1, h5424, hlam]
                                  · rcases p5414_3 (m.d 2 3) (by simp) with h5426 | h5426
                                    · linarith only [h4, h5426, hlam]
                                    · rcases p5414_3 (m.d 3 4) (by simp) with h5428 | h5428
                                      · linarith only [h5428, h7, hlam]
                                      · rcases p5414_3 (m.d 3 5) (by simp) with h5430 | h5430
                                        · linarith only [h5430, h8, hlam]
                                        · linarith only [h5378, h5430, hlam]
                                · linarith only [h4, h5423, hlam]
                              · have p5414_0 := h5414c.1
                                have p5414_1 := h5414c.2.1
                                have p5414_2 := h5414c.2.2.1
                                have p5414_3 := h5414c.2.2.2
                                linarith only [h3976, h5009, h5378, h8, hlam, p5414_2]
                              · have p5414_0 := h5414c.1
                                have p5414_1 := h5414c.2.1
                                have p5414_2 := h5414c.2.2.1
                                have p5414_3 := h5414c.2.2.2
                                linarith only [h0, h4, h4749, h5377, h5378, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5414_1]
                              · have p5414_0 := h5414c.1
                                have p5414_1 := h5414c.2.1
                                have p5414_2 := h5414c.2.2.1
                                have p5414_3 := h5414c.2.2.2
                                linarith only [h1, hlam, p5414_0]
                              · have p5414_0 := h5414c.1
                                have p5414_1 := h5414c.2.1
                                have p5414_2 := h5414c.2.2.1
                                have p5414_3 := h5414c.2.2.2
                                linarith only [hlam, p5414_0]
                              · have p5414_0 := h5414c.1
                                have p5414_1 := h5414c.2.1
                                have p5414_2 := h5414c.2.2.1
                                have p5414_3 := h5414c.2.2.2
                                linarith only [h3976, hlam, p5414_1]
                              · have p5414_0 := h5414c.1
                                have p5414_1 := h5414c.2.1
                                have p5414_2 := h5414c.2.2.1
                                have p5414_3 := h5414c.2.2.2
                                linarith only [h0, h3976, h4, h5378, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5414_1]
                              · have p5414_0 := h5414c.1
                                have p5414_1 := h5414c.2.1
                                have p5414_2 := h5414c.2.2.1
                                have p5414_3 := h5414c.2.2.2
                                linarith only [h5010, hlam, p5414_0]
                              · have p5414_0 := h5414c.1
                                have p5414_1 := h5414c.2.1
                                have p5414_2 := h5414c.2.2.1
                                have p5414_3 := h5414c.2.2.2
                                linarith only [h4, hlam, p5414_0]
                              · have p5414_0 := h5414c.1
                                have p5414_1 := h5414c.2.1
                                have p5414_2 := h5414c.2.2.1
                                have p5414_3 := h5414c.2.2.2
                                linarith only [h5378, hc13, hc35, hlam, hphi, p5414_1]
                              · have p5414_0 := h5414c.1
                                have p5414_1 := h5414c.2.1
                                have p5414_2 := h5414c.2.2.1
                                have p5414_3 := h5414c.2.2.2
                                linarith only [hlam, p5414_0]
                              · have p5414_0 := h5414c.1
                                have p5414_1 := h5414c.2.1
                                have p5414_2 := h5414c.2.2.1
                                have p5414_3 := h5414c.2.2.2
                                linarith only [h0, h4, h5378, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5414_1]
                              · have p5414_0 := h5414c.1
                                have p5414_1 := h5414c.2.1
                                have p5414_2 := h5414c.2.2.1
                                have p5414_3 := h5414c.2.2.2
                                linarith only [h5378, hlam, p5414_0]
                              · have p5414_0 := h5414c.1
                                have p5414_1 := h5414c.2.1
                                have p5414_2 := h5414c.2.2.1
                                have p5414_3 := h5414c.2.2.2
                                linarith only [h7, hlam, p5414_0]
                              · have p5414_0 := h5414c.1
                                have p5414_1 := h5414c.2.1
                                have p5414_2 := h5414c.2.2.1
                                have p5414_3 := h5414c.2.2.2
                                linarith only [h5009, hlam, p5414_0]
                              · have p5414_0 := h5414c.1
                                have p5414_1 := h5414c.2.1
                                have p5414_2 := h5414c.2.2.1
                                have p5414_3 := h5414c.2.2.2
                                linarith only [h5377, hlam, p5414_0]
                              · have p5414_0 := h5414c.1
                                have p5414_1 := h5414c.2.1
                                have p5414_2 := h5414c.2.2.1
                                have p5414_3 := h5414c.2.2.2
                                linarith only [hlam, p5414_0]
                              · have p5414_0 := h5414c.1
                                have p5414_1 := h5414c.2.1
                                have p5414_2 := h5414c.2.2.1
                                have p5414_3 := h5414c.2.2.2
                                linarith only [h5382, hlam, p5414_1]
                              · have p5414_0 := h5414c.1
                                have p5414_1 := h5414c.2.1
                                have p5414_2 := h5414c.2.2.1
                                have p5414_3 := h5414c.2.2.2
                                linarith only [h8, hlam, p5414_0]
                              · have p5414_0 := h5414c.1
                                have p5414_1 := h5414c.2.1
                                have p5414_2 := h5414c.2.2.1
                                have p5414_3 := h5414c.2.2.2
                                linarith only [h0, h4, h5009, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5414_1]
                              · have p5414_0 := h5414c.1
                                have p5414_1 := h5414c.2.1
                                have p5414_2 := h5414c.2.2.1
                                have p5414_3 := h5414c.2.2.2
                                linarith only [h0, h3976, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5414_1]
                              · have p5414_0 := h5414c.1
                                have p5414_1 := h5414c.2.1
                                have p5414_2 := h5414c.2.2.1
                                have p5414_3 := h5414c.2.2.2
                                rcases p5414_3 (m.d 0 3) (by simp) with h5454 | h5454
                                · rcases p5414_3 (m.d 1 3) (by simp) with h5455 | h5455
                                  · linarith only [h5010, h5455, hlam]
                                  · linarith only [h5009, h5455, hlam]
                                · linarith only [h5454, h7, hlam]
                              · have p5414_0 := h5414c.1
                                have p5414_1 := h5414c.2.1
                                have p5414_2 := h5414c.2.2.1
                                have p5414_3 := h5414c.2.2.2
                                linarith only [hlam, p5414_0]
                    · linarith only [h5405, hlam, p5384_0]
                  · have p5384_0 := h5384c.1
                    have p5384_1 := h5384c.2.1
                    have p5384_2 := h5384c.2.2.1
                    have p5384_3 := h5384c.2.2.2
                    linarith only [h0, hlam, p5384_0]
                  · have p5384_0 := h5384c.1
                    have p5384_1 := h5384c.2.1
                    have p5384_2 := h5384c.2.2.1
                    have p5384_3 := h5384c.2.2.2
                    linarith only [hlam, p5384_0]
                  · have p5384_0 := h5384c.1
                    have p5384_1 := h5384c.2.1
                    have p5384_2 := h5384c.2.2.1
                    have p5384_3 := h5384c.2.2.2
                    linarith only [h3976, hlam, p5384_0]
                  · have p5384_0 := h5384c.1
                    have p5384_1 := h5384c.2.1
                    have p5384_2 := h5384c.2.2.1
                    have p5384_3 := h5384c.2.2.2
                    linarith only [h4749, hlam, p5384_0]
                  · have p5384_0 := h5384c.1
                    have p5384_1 := h5384c.2.1
                    have p5384_2 := h5384c.2.2.1
                    have p5384_3 := h5384c.2.2.2
                    linarith only [h4997, hlam, p5384_0]
                  · have p5384_0 := h5384c.1
                    have p5384_1 := h5384c.2.1
                    have p5384_2 := h5384c.2.2.1
                    have p5384_3 := h5384c.2.2.2
                    linarith only [h1, hlam, p5384_0]
                  · have p5384_0 := h5384c.1
                    have p5384_1 := h5384c.2.1
                    have p5384_2 := h5384c.2.2.1
                    have p5384_3 := h5384c.2.2.2
                    linarith only [h0, h4, h5010, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5384_1]
                  · have p5384_0 := h5384c.1
                    have p5384_1 := h5384c.2.1
                    have p5384_2 := h5384c.2.2.1
                    have p5384_3 := h5384c.2.2.2
                    linarith only [hlam, p5384_0]
                  · have p5384_0 := h5384c.1
                    have p5384_1 := h5384c.2.1
                    have p5384_2 := h5384c.2.2.1
                    have p5384_3 := h5384c.2.2.2
                    linarith only [h0, h4, h4749, h5010, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5384_1]
                  · have p5384_0 := h5384c.1
                    have p5384_1 := h5384c.2.1
                    have p5384_2 := h5384c.2.2.1
                    have p5384_3 := h5384c.2.2.2
                    linarith only [h5010, hlam, p5384_1]
                  · have p5384_0 := h5384c.1
                    have p5384_1 := h5384c.2.1
                    have p5384_2 := h5384c.2.2.1
                    have p5384_3 := h5384c.2.2.2
                    linarith only [h2, hlam, p5384_0]
                  · have p5384_0 := h5384c.1
                    have p5384_1 := h5384c.2.1
                    have p5384_2 := h5384c.2.2.1
                    have p5384_3 := h5384c.2.2.2
                    linarith only [h2, h9, hc12, hc45, hlam, hphi, ht23, ht34, p5384_1]
                  · have p5384_0 := h5384c.1
                    have p5384_1 := h5384c.2.1
                    have p5384_2 := h5384c.2.2.1
                    have p5384_3 := h5384c.2.2.2
                    linarith only [h5009, hlam, p5384_0]
                  · have p5384_0 := h5384c.1
                    have p5384_1 := h5384c.2.1
                    have p5384_2 := h5384c.2.2.1
                    have p5384_3 := h5384c.2.2.2
                    linarith only [hlam, p5384_0]
                  · have p5384_0 := h5384c.1
                    have p5384_1 := h5384c.2.1
                    have p5384_2 := h5384c.2.2.1
                    have p5384_3 := h5384c.2.2.2
                    linarith only [h5375, hlam, p5384_1]
                  · have p5384_0 := h5384c.1
                    have p5384_1 := h5384c.2.1
                    have p5384_2 := h5384c.2.2.1
                    have p5384_3 := h5384c.2.2.2
                    linarith only [h3, hlam, p5384_0]
                  · have p5384_0 := h5384c.1
                    have p5384_1 := h5384c.2.1
                    have p5384_2 := h5384c.2.2.1
                    have p5384_3 := h5384c.2.2.2
                    rcases p5384_3 (m.d 0 1) (by simp) with h5477 | h5477
                    · rcases p5384_3 (m.d 1 2) (by simp) with h5478 | h5478
                      · linarith only [h4997, h5478, hlam]
                      · rcases p5384_3 (m.d 1 3) (by simp) with h5480 | h5480
                        · linarith only [h5010, h5480, hlam]
                        · linarith only [h3976, h5480, hlam]
                    · linarith only [h0, h5477, hlam]
                  · have p5384_0 := h5384c.1
                    have p5384_1 := h5384c.2.1
                    have p5384_2 := h5384c.2.2.1
                    have p5384_3 := h5384c.2.2.2
                    linarith only [h0, h4, h4997, h5009, h5378, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5384_1]
                  · have p5384_0 := h5384c.1
                    have p5384_1 := h5384c.2.1
                    have p5384_2 := h5384c.2.2.1
                    have p5384_3 := h5384c.2.2.2
                    rcases p5384_3 (m.d 0 1) (by simp) with h5485 | h5485
                    · rcases p5384_3 (m.d 1 2) (by simp) with h5486 | h5486
                      · linarith only [h4997, h5486, hlam]
                      · rcases p5384_3 (m.d 1 3) (by simp) with h5488 | h5488
                        · linarith only [h5010, h5488, hlam]
                        · linarith only [h5009, h5488, hlam]
                    · linarith only [h2, h5485, hlam]
                  · have p5384_0 := h5384c.1
                    have p5384_1 := h5384c.2.1
                    have p5384_2 := h5384c.2.2.1
                    have p5384_3 := h5384c.2.2.2
                    linarith only [hlam, p5384_0]
          · linarith only [h1, h3976, h5009, h5377, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h5494 | h5494
      · rcases m.htr 1 4 5 (by decide) (by decide) with h5495 | h5495
        · linarith only [h2, h5495, h9, hlam]
        · linarith only [h5009, h5494, h5495, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h5498 | h5498
        · linarith only [h2, h5009, h5498, h7, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h5500 | h5500
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5501 | h5501
            · rcases m.htr 2 4 5 (by decide) (by decide) with h5502 | h5502
              · linarith only [h5, h5502, h9, hlam]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h5504 | h5504
                · linarith only [h5, h5500, h5504, h9, hlam]
                · rcases h1bigk with h5506c | h5506c | h5506c | h5506c | h5506c | h5506c | h5506c | h5506c | h5506c | h5506c | h5506c | h5506c | h5506c | h5506c | h5506c | h5506c | h5506c | h5506c | h5506c | h5506c | h5506c | h5506c | h5506c | h5506c | h5506c
                  · have p5506_0 := h5506c.1
                    have p5506_1 := h5506c.2.1
                    have p5506_2 := h5506c.2.2.1
                    have p5506_3 := h5506c.2.2.2
                    linarith only [hlam, p5506_0]
                  · have p5506_0 := h5506c.1
                    have p5506_1 := h5506c.2.1
                    have p5506_2 := h5506c.2.2.1
                    have p5506_3 := h5506c.2.2.2
                    linarith only [h0, h3976, h4, h5009, h5500, hlam, p5506_2]
                  · have p5506_0 := h5506c.1
                    have p5506_1 := h5506c.2.1
                    have p5506_2 := h5506c.2.2.1
                    have p5506_3 := h5506c.2.2.2
                    linarith only [h0, h4, h5009, h5500, hlam, p5506_2]
                  · have p5506_0 := h5506c.1
                    have p5506_1 := h5506c.2.1
                    have p5506_2 := h5506c.2.2.1
                    have p5506_3 := h5506c.2.2.2
                    rcases p5506_3 (m.d 0 1) (by simp) with h5510 | h5510
                    · rcases p5506_3 (m.d 1 2) (by simp) with h5511 | h5511
                      · linarith only [h0, h5511, hlam]
                      · rcases p5506_3 (m.d 1 3) (by simp) with h5513 | h5513
                        · linarith only [h1, h5513, hlam]
                        · rcases p5506_3 (m.d 1 4) (by simp) with h5515 | h5515
                          · linarith only [h5515, hlam, p5506_0]
                          · rcases p5506_3 (m.d 1 5) (by simp) with h5517 | h5517
                            · linarith only [h3, h5517, hlam]
                            · linarith only [h5498, h5517, hlam]
                    · linarith only [h5510, hlam, p5506_0]
                  · have p5506_0 := h5506c.1
                    have p5506_1 := h5506c.2.1
                    have p5506_2 := h5506c.2.2.1
                    have p5506_3 := h5506c.2.2.2
                    rcases p5506_3 (m.d 0 1) (by simp) with h5521 | h5521
                    · rcases p5506_3 (m.d 1 2) (by simp) with h5522 | h5522
                      · linarith only [h0, h5522, hlam]
                      · rcases p5506_3 (m.d 1 3) (by simp) with h5524 | h5524
                        · linarith only [h1, h5524, hlam]
                        · rcases p5506_3 (m.d 1 4) (by simp) with h5526 | h5526
                          · linarith only [h2, h5526, hlam]
                          · rcases p5506_3 (m.d 1 5) (by simp) with h5528 | h5528
                            · linarith only [h5528, hlam, p5506_0]
                            · rcases h3bigk with h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c
                              · have p5530_0 := h5530c.1
                                have p5530_1 := h5530c.2.1
                                have p5530_2 := h5530c.2.2.1
                                have p5530_3 := h5530c.2.2.2
                                linarith only [hlam, p5530_0]
                              · have p5530_0 := h5530c.1
                                have p5530_1 := h5530c.2.1
                                have p5530_2 := h5530c.2.2.1
                                have p5530_3 := h5530c.2.2.2
                                rcases p5530_3 (m.d 0 3) (by simp) with h5532 | h5532
                                · rcases p5530_3 (m.d 1 3) (by simp) with h5533 | h5533
                                  · linarith only [h1, h5533, hlam]
                                  · rcases p5530_3 (m.d 2 3) (by simp) with h5535 | h5535
                                    · linarith only [h4, h5535, hlam]
                                    · linarith only [h3976, h5535, hlam]
                                · linarith only [h1, h5532, hlam]
                              · have p5530_0 := h5530c.1
                                have p5530_1 := h5530c.2.1
                                have p5530_2 := h5530c.2.2.1
                                have p5530_3 := h5530c.2.2.2
                                linarith only [h3976, h5009, h5501, h5504, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5530_1]
                              · have p5530_0 := h5530c.1
                                have p5530_1 := h5530c.2.1
                                have p5530_2 := h5530c.2.2.1
                                have p5530_3 := h5530c.2.2.2
                                rcases p5530_3 (m.d 0 3) (by simp) with h5540 | h5540
                                · rcases p5530_3 (m.d 1 3) (by simp) with h5541 | h5541
                                  · linarith only [h1, h5541, hlam]
                                  · rcases p5530_3 (m.d 2 3) (by simp) with h5543 | h5543
                                    · linarith only [h4, h5543, hlam]
                                    · linarith only [h5500, h5543, hlam]
                                · linarith only [h5540, hlam, p5530_0]
                              · have p5530_0 := h5530c.1
                                have p5530_1 := h5530c.2.1
                                have p5530_2 := h5530c.2.2.1
                                have p5530_3 := h5530c.2.2.2
                                rcases p5530_3 (m.d 0 3) (by simp) with h5547 | h5547
                                · rcases p5530_3 (m.d 1 3) (by simp) with h5548 | h5548
                                  · linarith only [h1, h5548, hlam]
                                  · rcases p5530_3 (m.d 2 3) (by simp) with h5550 | h5550
                                    · linarith only [h4, h5550, hlam]
                                    · linarith only [h5501, h5550, hlam]
                                · linarith only [h5547, hlam, p5530_0]
                              · have p5530_0 := h5530c.1
                                have p5530_1 := h5530c.2.1
                                have p5530_2 := h5530c.2.2.1
                                have p5530_3 := h5530c.2.2.2
                                linarith only [h1, hlam, p5530_0]
                              · have p5530_0 := h5530c.1
                                have p5530_1 := h5530c.2.1
                                have p5530_2 := h5530c.2.2.1
                                have p5530_3 := h5530c.2.2.2
                                linarith only [hlam, p5530_0]
                              · have p5530_0 := h5530c.1
                                have p5530_1 := h5530c.2.1
                                have p5530_2 := h5530c.2.2.1
                                have p5530_3 := h5530c.2.2.2
                                linarith only [h3976, hlam, p5530_1]
                              · have p5530_0 := h5530c.1
                                have p5530_1 := h5530c.2.1
                                have p5530_2 := h5530c.2.2.1
                                have p5530_3 := h5530c.2.2.2
                                linarith only [h5009, hlam, p5530_0]
                              · have p5530_0 := h5530c.1
                                have p5530_1 := h5530c.2.1
                                have p5530_2 := h5530c.2.2.1
                                have p5530_3 := h5530c.2.2.2
                                linarith only [h5494, hlam, p5530_0]
                              · have p5530_0 := h5530c.1
                                have p5530_1 := h5530c.2.1
                                have p5530_2 := h5530c.2.2.1
                                have p5530_3 := h5530c.2.2.2
                                linarith only [h4, hlam, p5530_0]
                              · have p5530_0 := h5530c.1
                                have p5530_1 := h5530c.2.1
                                have p5530_2 := h5530c.2.2.1
                                have p5530_3 := h5530c.2.2.2
                                rcases p5530_3 (m.d 0 3) (by simp) with h5560 | h5560
                                · rcases p5530_3 (m.d 1 3) (by simp) with h5561 | h5561
                                  · linarith only [h3976, h5561, hlam]
                                  · rcases p5530_3 (m.d 2 3) (by simp) with h5563 | h5563
                                    · rcases p5530_3 (m.d 3 4) (by simp) with h5564 | h5564
                                      · linarith only [h5500, h5564, hlam]
                                      · linarith only [h5009, h5564, hlam]
                                    · linarith only [h3976, h5563, hlam]
                                · linarith only [h1, h5560, hlam]
                              · have p5530_0 := h5530c.1
                                have p5530_1 := h5530c.2.1
                                have p5530_2 := h5530c.2.2.1
                                have p5530_3 := h5530c.2.2.2
                                linarith only [hlam, p5530_0]
                              · have p5530_0 := h5530c.1
                                have p5530_1 := h5530c.2.1
                                have p5530_2 := h5530c.2.2.1
                                have p5530_3 := h5530c.2.2.2
                                linarith only [h3976, h5009, hc12, hc23, hlam, hphi, p5530_1]
                              · have p5530_0 := h5530c.1
                                have p5530_1 := h5530c.2.1
                                have p5530_2 := h5530c.2.2.1
                                have p5530_3 := h5530c.2.2.2
                                linarith only [h0, h3976, h4, h5009, h5504, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5530_1]
                              · have p5530_0 := h5530c.1
                                have p5530_1 := h5530c.2.1
                                have p5530_2 := h5530c.2.2.1
                                have p5530_3 := h5530c.2.2.2
                                linarith only [h7, hlam, p5530_0]
                              · have p5530_0 := h5530c.1
                                have p5530_1 := h5530c.2.1
                                have p5530_2 := h5530c.2.2.1
                                have p5530_3 := h5530c.2.2.2
                                linarith only [h3976, h5, h5500, h9, hc12, hc45, hlam, hphi, ht23, ht34, p5530_1]
                              · have p5530_0 := h5530c.1
                                have p5530_1 := h5530c.2.1
                                have p5530_2 := h5530c.2.2.1
                                have p5530_3 := h5530c.2.2.2
                                linarith only [h5500, hlam, p5530_0]
                              · have p5530_0 := h5530c.1
                                have p5530_1 := h5530c.2.1
                                have p5530_2 := h5530c.2.2.1
                                have p5530_3 := h5530c.2.2.2
                                linarith only [hlam, p5530_0]
                              · have p5530_0 := h5530c.1
                                have p5530_1 := h5530c.2.1
                                have p5530_2 := h5530c.2.2.1
                                have p5530_3 := h5530c.2.2.2
                                linarith only [h5504, hlam, p5530_1]
                              · have p5530_0 := h5530c.1
                                have p5530_1 := h5530c.2.1
                                have p5530_2 := h5530c.2.2.1
                                have p5530_3 := h5530c.2.2.2
                                linarith only [h8, hlam, p5530_0]
                              · have p5530_0 := h5530c.1
                                have p5530_1 := h5530c.2.1
                                have p5530_2 := h5530c.2.2.1
                                have p5530_3 := h5530c.2.2.2
                                linarith only [h0, h3976, h4, h5501, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5530_1]
                              · have p5530_0 := h5530c.1
                                have p5530_1 := h5530c.2.1
                                have p5530_2 := h5530c.2.2.1
                                have p5530_3 := h5530c.2.2.2
                                linarith only [h5501, hlam, p5530_0]
                              · have p5530_0 := h5530c.1
                                have p5530_1 := h5530c.2.1
                                have p5530_2 := h5530c.2.2.1
                                have p5530_3 := h5530c.2.2.2
                                linarith only [h0, h4, h5501, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5530_1]
                              · have p5530_0 := h5530c.1
                                have p5530_1 := h5530c.2.1
                                have p5530_2 := h5530c.2.2.1
                                have p5530_3 := h5530c.2.2.2
                                linarith only [hlam, p5530_0]
                    · linarith only [h5521, hlam, p5506_0]
                  · have p5506_0 := h5506c.1
                    have p5506_1 := h5506c.2.1
                    have p5506_2 := h5506c.2.2.1
                    have p5506_3 := h5506c.2.2.2
                    linarith only [h0, hlam, p5506_0]
                  · have p5506_0 := h5506c.1
                    have p5506_1 := h5506c.2.1
                    have p5506_2 := h5506c.2.2.1
                    have p5506_3 := h5506c.2.2.2
                    linarith only [hlam, p5506_0]
                  · have p5506_0 := h5506c.1
                    have p5506_1 := h5506c.2.1
                    have p5506_2 := h5506c.2.2.1
                    have p5506_3 := h5506c.2.2.2
                    linarith only [h3976, hlam, p5506_0]
                  · have p5506_0 := h5506c.1
                    have p5506_1 := h5506c.2.1
                    have p5506_2 := h5506c.2.2.1
                    have p5506_3 := h5506c.2.2.2
                    linarith only [h4749, hlam, p5506_0]
                  · have p5506_0 := h5506c.1
                    have p5506_1 := h5506c.2.1
                    have p5506_2 := h5506c.2.2.1
                    have p5506_3 := h5506c.2.2.2
                    linarith only [h4997, hlam, p5506_0]
                  · have p5506_0 := h5506c.1
                    have p5506_1 := h5506c.2.1
                    have p5506_2 := h5506c.2.2.1
                    have p5506_3 := h5506c.2.2.2
                    linarith only [h1, hlam, p5506_0]
                  · have p5506_0 := h5506c.1
                    have p5506_1 := h5506c.2.1
                    have p5506_2 := h5506c.2.2.1
                    have p5506_3 := h5506c.2.2.2
                    linarith only [h5009, hc12, hc34, hlam, hphi, ht23, p5506_1]
                  · have p5506_0 := h5506c.1
                    have p5506_1 := h5506c.2.1
                    have p5506_2 := h5506c.2.2.1
                    have p5506_3 := h5506c.2.2.2
                    linarith only [hlam, p5506_0]
                  · have p5506_0 := h5506c.1
                    have p5506_1 := h5506c.2.1
                    have p5506_2 := h5506c.2.2.1
                    have p5506_3 := h5506c.2.2.2
                    linarith only [h5009, hlam, p5506_1]
                  · have p5506_0 := h5506c.1
                    have p5506_1 := h5506c.2.1
                    have p5506_2 := h5506c.2.2.1
                    have p5506_3 := h5506c.2.2.2
                    linarith only [h5494, hlam, p5506_1]
                  · have p5506_0 := h5506c.1
                    have p5506_1 := h5506c.2.1
                    have p5506_2 := h5506c.2.2.1
                    have p5506_3 := h5506c.2.2.2
                    linarith only [h2, hlam, p5506_0]
                  · have p5506_0 := h5506c.1
                    have p5506_1 := h5506c.2.1
                    have p5506_2 := h5506c.2.2.1
                    have p5506_3 := h5506c.2.2.2
                    linarith only [h2, h9, hc12, hc45, hlam, hphi, ht23, ht34, p5506_1]
                  · have p5506_0 := h5506c.1
                    have p5506_1 := h5506c.2.1
                    have p5506_2 := h5506c.2.2.1
                    have p5506_3 := h5506c.2.2.2
                    linarith only [h4749, h5, h9, hc13, hc45, hlam, hphi, ht34, p5506_1]
                  · have p5506_0 := h5506c.1
                    have p5506_1 := h5506c.2.1
                    have p5506_2 := h5506c.2.2.1
                    have p5506_3 := h5506c.2.2.2
                    linarith only [hlam, p5506_0]
                  · have p5506_0 := h5506c.1
                    have p5506_1 := h5506c.2.1
                    have p5506_2 := h5506c.2.2.1
                    have p5506_3 := h5506c.2.2.2
                    linarith only [h5498, hlam, p5506_1]
                  · have p5506_0 := h5506c.1
                    have p5506_1 := h5506c.2.1
                    have p5506_2 := h5506c.2.2.1
                    have p5506_3 := h5506c.2.2.2
                    linarith only [h3, hlam, p5506_0]
                  · have p5506_0 := h5506c.1
                    have p5506_1 := h5506c.2.1
                    have p5506_2 := h5506c.2.2.1
                    have p5506_3 := h5506c.2.2.2
                    linarith only [h0, h4, h5494, h5501, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5506_1]
                  · have p5506_0 := h5506c.1
                    have p5506_1 := h5506c.2.1
                    have p5506_2 := h5506c.2.2.1
                    have p5506_3 := h5506c.2.2.2
                    linarith only [h0, h3976, h4, h5494, h5501, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5506_1]
                  · have p5506_0 := h5506c.1
                    have p5506_1 := h5506c.2.1
                    have p5506_2 := h5506c.2.2.1
                    have p5506_3 := h5506c.2.2.2
                    linarith only [h0, h4, h5494, h5501, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p5506_1]
                  · have p5506_0 := h5506c.1
                    have p5506_1 := h5506c.2.1
                    have p5506_2 := h5506c.2.2.1
                    have p5506_3 := h5506c.2.2.2
                    linarith only [hlam, p5506_0]
            · linarith only [h3976, h5009, h5500, h5501, hc12, hc35, hlam, hphi, ht23]
          · linarith only [h3976, h5500, h7, h9, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 11192000 in
set_option maxHeartbeats 11192000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s8_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
    (h9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h3976 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 4 (by decide) (by decide) with h4749 | h4749
  · exact r1l7_11_13_25_L_I_L_I_H_I_s8_x1_x1_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h3976 h4749
  · exact r1l7_11_13_25_L_I_L_I_H_I_s8_x1_x1_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h3976 h4749

set_option maxHeartbeats 11192000 in
set_option maxHeartbeats 11192000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s8_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
    (h9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 3 (by decide) (by decide) with h3976 | h3976
  · exact r1l7_11_13_25_L_I_L_I_H_I_s8_x1_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h3976
  · exact r1l7_11_13_25_L_I_L_I_H_I_s8_x1_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h3976

set_option maxHeartbeats 11192000 in
set_option maxHeartbeats 11192000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s8 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
  · exact r1l7_11_13_25_L_I_L_I_H_I_s8_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9
  · exact r1l7_11_13_25_L_I_L_I_H_I_s8_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9

end R2N4
