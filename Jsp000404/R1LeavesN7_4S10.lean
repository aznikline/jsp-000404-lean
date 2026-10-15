import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_4S7
import Jsp000404.R1LeavesN7_4S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 12030000 in
set_option maxHeartbeats 12030000 in
theorem r1l7_11_23_L_I_H_I_s5_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4375 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 0 4 5 (by decide) (by decide) with h4725 | h4725
  · exact r1l7_11_23_L_I_H_I_s5_x1_x1_x0 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg5 h6 h4375 h4725
  · exact r1l7_11_23_L_I_H_I_s5_x1_x1_x1 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg5 h6 h4375 h4725

set_option maxHeartbeats 12030000 in
set_option maxHeartbeats 12030000 in
theorem r1l7_11_23_L_I_H_I_s5_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 0 3 5 (by decide) (by decide) with h4375 | h4375
  · exact r1l7_11_23_L_I_H_I_s5_x1_x0 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg5 h6 h4375
  · exact r1l7_11_23_L_I_H_I_s5_x1_x1 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg5 h6 h4375

set_option maxHeartbeats 12030000 in
set_option maxHeartbeats 12030000 in
theorem r1l7_11_23_L_I_H_I_s5 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
  · exact r1l7_11_23_L_I_H_I_s5_x0 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg5 h6
  · exact r1l7_11_23_L_I_H_I_s5_x1 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg5 h6

set_option maxHeartbeats 12718000 in
set_option maxHeartbeats 12718000 in
theorem r1l7_11_23_L_I_H_I_s4 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_11_23_L_I_H_I_s5 m hb1 hb3 h0 h1 h2 h3 h4 h5
  · rcases m.htr 0 3 4 (by decide) (by decide) with h6021 | h6021
    · linarith only [h4, h5, h6021, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h6023 | h6023
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6024 | h6024
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6025 | h6025
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6026 | h6026
            · linarith only [h0, h4, h5, h6023, h6026, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6028 | h6028
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6029 | h6029
                · linarith only [h1, h6021, h6029, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6031 | h6031
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6032 | h6032
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6033 | h6033
                      · linarith only [h0, h1, h6021, h6025, h6031, h6033, hc02, hc35, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6035 | h6035
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6036 | h6036
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h6037 | h6037
                            · rcases h1bigk with h6038c | h6038c | h6038c | h6038c | h6038c | h6038c | h6038c | h6038c | h6038c | h6038c | h6038c | h6038c | h6038c | h6038c | h6038c | h6038c | h6038c | h6038c | h6038c | h6038c | h6038c | h6038c | h6038c | h6038c | h6038c
                              · have p6038_0 := h6038c.1
                                have p6038_1 := h6038c.2.1
                                have p6038_2 := h6038c.2.2.1
                                have p6038_3 := h6038c.2.2.2
                                linarith only [hlam, p6038_0]
                              · have p6038_0 := h6038c.1
                                have p6038_1 := h6038c.2.1
                                have p6038_2 := h6038c.2.2.1
                                have p6038_3 := h6038c.2.2.2
                                linarith only [h6025, h6035, h6037, hc01, hc45, hlam, hphi, ht0b, ht5b, p6038_1]
                              · have p6038_0 := h6038c.1
                                have p6038_1 := h6038c.2.1
                                have p6038_2 := h6038c.2.2.1
                                have p6038_3 := h6038c.2.2.2
                                rcases p6038_3 (m.d 0 1) (by simp) with h6041 | h6041
                                · rcases p6038_3 (m.d 1 2) (by simp) with h6042 | h6042
                                  · linarith only [h0, h6042, hlam]
                                  · linarith only [h6025, h6042, hlam]
                                · linarith only [h6041, hlam, p6038_0]
                              · have p6038_0 := h6038c.1
                                have p6038_1 := h6038c.2.1
                                have p6038_2 := h6038c.2.2.1
                                have p6038_3 := h6038c.2.2.2
                                linarith only [h6025, h6026, h6035, h6037, hc01, hc45, hlam, hphi, ht0b, ht5b, p6038_1]
                              · have p6038_0 := h6038c.1
                                have p6038_1 := h6038c.2.1
                                have p6038_2 := h6038c.2.2.1
                                have p6038_3 := h6038c.2.2.2
                                rcases p6038_3 (m.d 0 1) (by simp) with h6047 | h6047
                                · rcases p6038_3 (m.d 1 2) (by simp) with h6048 | h6048
                                  · linarith only [h0, h6048, hlam]
                                  · linarith only [h6028, h6048, hlam]
                                · linarith only [h6047, hlam, p6038_0]
                              · have p6038_0 := h6038c.1
                                have p6038_1 := h6038c.2.1
                                have p6038_2 := h6038c.2.2.1
                                have p6038_3 := h6038c.2.2.2
                                linarith only [h0, hlam, p6038_0]
                              · have p6038_0 := h6038c.1
                                have p6038_1 := h6038c.2.1
                                have p6038_2 := h6038c.2.2.1
                                have p6038_3 := h6038c.2.2.2
                                linarith only [hlam, p6038_0]
                              · have p6038_0 := h6038c.1
                                have p6038_1 := h6038c.2.1
                                have p6038_2 := h6038c.2.2.1
                                have p6038_3 := h6038c.2.2.2
                                linarith only [h0, h6025, h6035, h6037, hc01, hc45, hlam, hphi, ht0b, ht5b, p6038_1]
                              · have p6038_0 := h6038c.1
                                have p6038_1 := h6038c.2.1
                                have p6038_2 := h6038c.2.2.1
                                have p6038_3 := h6038c.2.2.2
                                linarith only [h6026, hlam, p6038_0]
                              · have p6038_0 := h6038c.1
                                have p6038_1 := h6038c.2.1
                                have p6038_2 := h6038c.2.2.1
                                have p6038_3 := h6038c.2.2.2
                                rcases p6038_3 (m.d 0 1) (by simp) with h6056 | h6056
                                · rcases p6038_3 (m.d 1 2) (by simp) with h6057 | h6057
                                  · rcases p6038_3 (m.d 1 3) (by simp) with h6058 | h6058
                                    · linarith only [h6025, h6058, hlam]
                                    · linarith only [h6031, h6058, hlam]
                                  · linarith only [h6028, h6057, hlam]
                                · linarith only [h3, h6056, hlam]
                              · have p6038_0 := h6038c.1
                                have p6038_1 := h6038c.2.1
                                have p6038_2 := h6038c.2.2.1
                                have p6038_3 := h6038c.2.2.2
                                linarith only [h1, hlam, p6038_0]
                              · have p6038_0 := h6038c.1
                                have p6038_1 := h6038c.2.1
                                have p6038_2 := h6038c.2.2.1
                                have p6038_3 := h6038c.2.2.2
                                linarith only [h6025, hlam, p6038_1]
                              · have p6038_0 := h6038c.1
                                have p6038_1 := h6038c.2.1
                                have p6038_2 := h6038c.2.2.1
                                have p6038_3 := h6038c.2.2.2
                                linarith only [hlam, p6038_0]
                              · have p6038_0 := h6038c.1
                                have p6038_1 := h6038c.2.1
                                have p6038_2 := h6038c.2.2.1
                                have p6038_3 := h6038c.2.2.2
                                linarith only [h6029, hlam, p6038_1]
                              · have p6038_0 := h6038c.1
                                have p6038_1 := h6038c.2.1
                                have p6038_2 := h6038c.2.2.1
                                have p6038_3 := h6038c.2.2.2
                                rcases p6038_3 (m.d 0 1) (by simp) with h6067 | h6067
                                · rcases p6038_3 (m.d 1 2) (by simp) with h6068 | h6068
                                  · rcases p6038_3 (m.d 1 3) (by simp) with h6069 | h6069
                                    · rcases p6038_3 (m.d 1 4) (by simp) with h6070 | h6070
                                      · rcases p6038_3 (m.d 1 5) (by simp) with h6071 | h6071
                                        · linarith only [h6031, h6071, hlam]
                                        · rcases h3bigk with h6073c | h6073c | h6073c | h6073c | h6073c | h6073c | h6073c | h6073c | h6073c | h6073c | h6073c | h6073c | h6073c | h6073c | h6073c | h6073c | h6073c | h6073c | h6073c | h6073c | h6073c | h6073c | h6073c | h6073c | h6073c
                                          · have p6073_0 := h6073c.1
                                            have p6073_1 := h6073c.2.1
                                            have p6073_2 := h6073c.2.2.1
                                            have p6073_3 := h6073c.2.2.2
                                            linarith only [hlam, p6073_0]
                                          · have p6073_0 := h6073c.1
                                            have p6073_1 := h6073c.2.1
                                            have p6073_2 := h6073c.2.2.1
                                            have p6073_3 := h6073c.2.2.2
                                            linarith only [h6028, h6035, h6037, hc03, hc45, hlam, hphi, ht0b, ht5b, p6038_1, p6073_1]
                                          · have p6073_0 := h6073c.1
                                            have p6073_1 := h6073c.2.1
                                            have p6073_2 := h6073c.2.2.1
                                            have p6073_3 := h6073c.2.2.2
                                            linarith only [h4, h5, h6033, h6035, h6037, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6073_1]
                                          · have p6073_0 := h6073c.1
                                            have p6073_1 := h6073c.2.1
                                            have p6073_2 := h6073c.2.2.1
                                            have p6073_3 := h6073c.2.2.2
                                            linarith only [h6021, hlam, p6073_0]
                                          · have p6073_0 := h6073c.1
                                            have p6073_1 := h6073c.2.1
                                            have p6073_2 := h6073c.2.2.1
                                            have p6073_3 := h6073c.2.2.2
                                            linarith only [h4, h5, h6033, h6037, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6073_1]
                                          · have p6073_0 := h6073c.1
                                            have p6073_1 := h6073c.2.1
                                            have p6073_2 := h6073c.2.2.1
                                            have p6073_3 := h6073c.2.2.2
                                            linarith only [h1, hlam, p6073_0]
                                          · have p6073_0 := h6073c.1
                                            have p6073_1 := h6073c.2.1
                                            have p6073_2 := h6073c.2.2.1
                                            have p6073_3 := h6073c.2.2.2
                                            linarith only [hlam, p6073_0]
                                          · have p6073_0 := h6073c.1
                                            have p6073_1 := h6073c.2.1
                                            have p6073_2 := h6073c.2.2.1
                                            have p6073_3 := h6073c.2.2.2
                                            linarith only [h6035, h6037, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p6073_1]
                                          · have p6073_0 := h6073c.1
                                            have p6073_1 := h6073c.2.1
                                            have p6073_2 := h6073c.2.2.1
                                            have p6073_3 := h6073c.2.2.2
                                            linarith only [h6029, hlam, p6073_0]
                                          · have p6073_0 := h6073c.1
                                            have p6073_1 := h6073c.2.1
                                            have p6073_2 := h6073c.2.2.1
                                            have p6073_3 := h6073c.2.2.2
                                            linarith only [h1, h4, h5, h6033, h6037, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6073_1]
                                          · have p6073_0 := h6073c.1
                                            have p6073_1 := h6073c.2.1
                                            have p6073_2 := h6073c.2.2.1
                                            have p6073_3 := h6073c.2.2.2
                                            linarith only [h4, hlam, p6073_0]
                                          · have p6073_0 := h6073c.1
                                            have p6073_1 := h6073c.2.1
                                            have p6073_2 := h6073c.2.2.1
                                            have p6073_3 := h6073c.2.2.2
                                            linarith only [h6025, hlam, p6073_0]
                                          · have p6073_0 := h6073c.1
                                            have p6073_1 := h6073c.2.1
                                            have p6073_2 := h6073c.2.2.1
                                            have p6073_3 := h6073c.2.2.2
                                            linarith only [hlam, p6073_0]
                                          · have p6073_0 := h6073c.1
                                            have p6073_1 := h6073c.2.1
                                            have p6073_2 := h6073c.2.2.1
                                            have p6073_3 := h6073c.2.2.2
                                            linarith only [h6033, hlam, p6073_0]
                                          · have p6073_0 := h6073c.1
                                            have p6073_1 := h6073c.2.1
                                            have p6073_2 := h6073c.2.2.1
                                            have p6073_3 := h6073c.2.2.2
                                            linarith only [h4, h5, h6033, h6037, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6073_1]
                                          · have p6073_0 := h6073c.1
                                            have p6073_1 := h6073c.2.1
                                            have p6073_2 := h6073c.2.2.1
                                            have p6073_3 := h6073c.2.2.2
                                            linarith only [hc03, hc34, hlam, hphi, p6073_1]
                                          · have p6073_0 := h6073c.1
                                            have p6073_1 := h6073c.2.1
                                            have p6073_2 := h6073c.2.2.1
                                            have p6073_3 := h6073c.2.2.2
                                            linarith only [h6025, hc23, hc34, hlam, hphi, p6073_1]
                                          · have p6073_0 := h6073c.1
                                            have p6073_1 := h6073c.2.1
                                            have p6073_2 := h6073c.2.2.1
                                            have p6073_3 := h6073c.2.2.2
                                            linarith only [hc23, hc34, hlam, hphi, p6073_1]
                                          · have p6073_0 := h6073c.1
                                            have p6073_1 := h6073c.2.1
                                            have p6073_2 := h6073c.2.2.1
                                            have p6073_3 := h6073c.2.2.2
                                            linarith only [hlam, p6073_0]
                                          · have p6073_0 := h6073c.1
                                            have p6073_1 := h6073c.2.1
                                            have p6073_2 := h6073c.2.2.1
                                            have p6073_3 := h6073c.2.2.2
                                            rcases p6073_3 (m.d 0 3) (by simp) with h6093 | h6093
                                            · linarith only [h6021, h6093, hlam]
                                            · linarith only [h6023, h6093, hlam]
                                          · have p6073_0 := h6073c.1
                                            have p6073_1 := h6073c.2.1
                                            have p6073_2 := h6073c.2.2.1
                                            have p6073_3 := h6073c.2.2.2
                                            linarith only [h6023, hlam, p6073_0]
                                          · have p6073_0 := h6073c.1
                                            have p6073_1 := h6073c.2.1
                                            have p6073_2 := h6073c.2.2.1
                                            have p6073_3 := h6073c.2.2.2
                                            linarith only [h6031, hlam, p6073_0]
                                          · have p6073_0 := h6073c.1
                                            have p6073_1 := h6073c.2.1
                                            have p6073_2 := h6073c.2.2.1
                                            have p6073_3 := h6073c.2.2.2
                                            linarith only [h6035, hlam, p6073_0]
                                          · have p6073_0 := h6073c.1
                                            have p6073_1 := h6073c.2.1
                                            have p6073_2 := h6073c.2.2.1
                                            have p6073_3 := h6073c.2.2.2
                                            linarith only [h6037, hlam, p6073_0]
                                          · have p6073_0 := h6073c.1
                                            have p6073_1 := h6073c.2.1
                                            have p6073_2 := h6073c.2.2.1
                                            have p6073_3 := h6073c.2.2.2
                                            linarith only [hlam, p6073_0]
                                      · linarith only [h6032, h6070, hlam]
                                    · linarith only [h6031, h6069, hlam]
                                  · linarith only [h6028, h6068, hlam]
                                · linarith only [h3, h6067, hlam]
                              · have p6038_0 := h6038c.1
                                have p6038_1 := h6038c.2.1
                                have p6038_2 := h6038c.2.2.1
                                have p6038_3 := h6038c.2.2.2
                                linarith only [h2, hlam, p6038_0]
                              · have p6038_0 := h6038c.1
                                have p6038_1 := h6038c.2.1
                                have p6038_2 := h6038c.2.2.1
                                have p6038_3 := h6038c.2.2.2
                                linarith only [h2, h6025, h6035, h6037, hc01, hc45, hlam, hphi, ht0b, ht5b, p6038_1]
                              · have p6038_0 := h6038c.1
                                have p6038_1 := h6038c.2.1
                                have p6038_2 := h6038c.2.2.1
                                have p6038_3 := h6038c.2.2.2
                                linarith only [h2, h6025, h6035, h6037, hc01, hc45, hlam, hphi, ht0b, ht5b, p6038_1]
                              · have p6038_0 := h6038c.1
                                have p6038_1 := h6038c.2.1
                                have p6038_2 := h6038c.2.2.1
                                have p6038_3 := h6038c.2.2.2
                                linarith only [hlam, p6038_0]
                              · have p6038_0 := h6038c.1
                                have p6038_1 := h6038c.2.1
                                have p6038_2 := h6038c.2.2.1
                                have p6038_3 := h6038c.2.2.2
                                rcases p6038_3 (m.d 0 1) (by simp) with h6109 | h6109
                                · rcases p6038_3 (m.d 1 2) (by simp) with h6110 | h6110
                                  · linarith only [h6026, h6110, hlam]
                                  · linarith only [h6028, h6110, hlam]
                                · linarith only [h3, h6109, hlam]
                              · have p6038_0 := h6038c.1
                                have p6038_1 := h6038c.2.1
                                have p6038_2 := h6038c.2.2.1
                                have p6038_3 := h6038c.2.2.2
                                linarith only [h3, hlam, p6038_0]
                              · have p6038_0 := h6038c.1
                                have p6038_1 := h6038c.2.1
                                have p6038_2 := h6038c.2.2.1
                                have p6038_3 := h6038c.2.2.2
                                linarith only [h6028, hlam, p6038_1]
                              · have p6038_0 := h6038c.1
                                have p6038_1 := h6038c.2.1
                                have p6038_2 := h6038c.2.2.1
                                have p6038_3 := h6038c.2.2.2
                                linarith only [h6031, hlam, p6038_0]
                              · have p6038_0 := h6038c.1
                                have p6038_1 := h6038c.2.1
                                have p6038_2 := h6038c.2.2.1
                                have p6038_3 := h6038c.2.2.2
                                linarith only [h6032, hlam, p6038_0]
                              · have p6038_0 := h6038c.1
                                have p6038_1 := h6038c.2.1
                                have p6038_2 := h6038c.2.2.1
                                have p6038_3 := h6038c.2.2.2
                                linarith only [hlam, p6038_0]
                            · linarith only [h0, h5, h6025, h6033, h6035, h6037, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h0, h3, h5, h6023, h6025, h6032, h6035, h6036, hc03, hc35, hlam, hphi, ht0b, ht5b]
                        · linarith only [h4, h5, h6023, h6033, h6035, hc23, hc34, hlam, hphi]
                    · linarith only [h6021, h6023, h6024, h6025, h6026, h6032, hc23, hc34, hlam, hphi]
                  · linarith only [h6021, h6023, h6031, hc13, hc34, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6124 | h6124
                · linarith only [h1, h6021, h6023, h6124, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6126 | h6126
                  · linarith only [h6025, h6028, h6126, hlam]
                  · linarith only [h6021, h6023, h6126, hc13, hc34, hlam, hphi]
          · linarith only [h4, h5, h6025, hc12, hc24, hlam, hphi]
        · linarith only [h4, h5, h6023, h6024, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6131 | h6131
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6132 | h6132
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6133 | h6133
            · linarith only [h0, h5, h6133, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6135 | h6135
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6136 | h6136
                · linarith only [h1, h4, h5, h6021, h6136, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6138 | h6138
                  · linarith only [h1, h6023, h6138, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6140 | h6140
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6141 | h6141
                      · linarith only [h4, h5, h6021, h6141, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6143 | h6143
                        · linarith only [h3, h6023, h6132, h6138, h6143, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6145 | h6145
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h6146 | h6146
                            · rcases h1bigk with h6147c | h6147c | h6147c | h6147c | h6147c | h6147c | h6147c | h6147c | h6147c | h6147c | h6147c | h6147c | h6147c | h6147c | h6147c | h6147c | h6147c | h6147c | h6147c | h6147c | h6147c | h6147c | h6147c | h6147c | h6147c
                              · have p6147_0 := h6147c.1
                                have p6147_1 := h6147c.2.1
                                have p6147_2 := h6147c.2.2.1
                                have p6147_3 := h6147c.2.2.2
                                linarith only [hlam, p6147_0]
                              · have p6147_0 := h6147c.1
                                have p6147_1 := h6147c.2.1
                                have p6147_2 := h6147c.2.2.1
                                have p6147_3 := h6147c.2.2.2
                                rcases p6147_3 (m.d 0 1) (by simp) with h6149 | h6149
                                · rcases p6147_3 (m.d 1 2) (by simp) with h6150 | h6150
                                  · linarith only [h6150, hlam, p6147_0]
                                  · rcases p6147_3 (m.d 1 3) (by simp) with h6152 | h6152
                                    · linarith only [h1, h6152, hlam]
                                    · rcases p6147_3 (m.d 1 4) (by simp) with h6154 | h6154
                                      · linarith only [h2, h6154, hlam]
                                      · linarith only [h6133, h6154, hlam]
                                · linarith only [h6149, hlam, p6147_0]
                              · have p6147_0 := h6147c.1
                                have p6147_1 := h6147c.2.1
                                have p6147_2 := h6147c.2.2.1
                                have p6147_3 := h6147c.2.2.2
                                rcases p6147_3 (m.d 0 1) (by simp) with h6158 | h6158
                                · rcases p6147_3 (m.d 1 2) (by simp) with h6159 | h6159
                                  · linarith only [h0, h6159, hlam]
                                  · linarith only [h6132, h6159, hlam]
                                · linarith only [h6158, hlam, p6147_0]
                              · have p6147_0 := h6147c.1
                                have p6147_1 := h6147c.2.1
                                have p6147_2 := h6147c.2.2.1
                                have p6147_3 := h6147c.2.2.2
                                rcases p6147_3 (m.d 0 1) (by simp) with h6163 | h6163
                                · rcases p6147_3 (m.d 1 2) (by simp) with h6164 | h6164
                                  · linarith only [h0, h6164, hlam]
                                  · rcases p6147_3 (m.d 1 3) (by simp) with h6166 | h6166
                                    · linarith only [h1, h6166, hlam]
                                    · rcases p6147_3 (m.d 1 4) (by simp) with h6168 | h6168
                                      · linarith only [h6168, hlam, p6147_0]
                                      · rcases p6147_3 (m.d 1 5) (by simp) with h6170 | h6170
                                        · linarith only [h3, h6170, hlam]
                                        · rcases h3bigk with h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c | h6172c
                                          · have p6172_0 := h6172c.1
                                            have p6172_1 := h6172c.2.1
                                            have p6172_2 := h6172c.2.2.1
                                            have p6172_3 := h6172c.2.2.2
                                            linarith only [hlam, p6172_0]
                                          · have p6172_0 := h6172c.1
                                            have p6172_1 := h6172c.2.1
                                            have p6172_2 := h6172c.2.2.1
                                            have p6172_3 := h6172c.2.2.2
                                            linarith only [h6023, h6132, hc23, hc35, hlam, hphi, p6172_1]
                                          · have p6172_0 := h6172c.1
                                            have p6172_1 := h6172c.2.1
                                            have p6172_2 := h6172c.2.2.1
                                            have p6172_3 := h6172c.2.2.2
                                            linarith only [h4, h5, h6141, hc23, hc34, hlam, hphi, p6172_1]
                                          · have p6172_0 := h6172c.1
                                            have p6172_1 := h6172c.2.1
                                            have p6172_2 := h6172c.2.2.1
                                            have p6172_3 := h6172c.2.2.2
                                            linarith only [h6021, hlam, p6172_0]
                                          · have p6172_0 := h6172c.1
                                            have p6172_1 := h6172c.2.1
                                            have p6172_2 := h6172c.2.2.1
                                            have p6172_3 := h6172c.2.2.2
                                            linarith only [h6023, hlam, p6172_0]
                                          · have p6172_0 := h6172c.1
                                            have p6172_1 := h6172c.2.1
                                            have p6172_2 := h6172c.2.2.1
                                            have p6172_3 := h6172c.2.2.2
                                            linarith only [h1, hlam, p6172_0]
                                          · have p6172_0 := h6172c.1
                                            have p6172_1 := h6172c.2.1
                                            have p6172_2 := h6172c.2.2.1
                                            have p6172_3 := h6172c.2.2.2
                                            linarith only [hlam, p6172_0]
                                          · have p6172_0 := h6172c.1
                                            have p6172_1 := h6172c.2.1
                                            have p6172_2 := h6172c.2.2.1
                                            have p6172_3 := h6172c.2.2.2
                                            linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6172_1]
                                          · have p6172_0 := h6172c.1
                                            have p6172_1 := h6172c.2.1
                                            have p6172_2 := h6172c.2.2.1
                                            have p6172_3 := h6172c.2.2.2
                                            linarith only [h6136, hlam, p6172_0]
                                          · have p6172_0 := h6172c.1
                                            have p6172_1 := h6172c.2.1
                                            have p6172_2 := h6172c.2.2.1
                                            have p6172_3 := h6172c.2.2.2
                                            linarith only [h6138, hlam, p6172_0]
                                          · have p6172_0 := h6172c.1
                                            have p6172_1 := h6172c.2.1
                                            have p6172_2 := h6172c.2.2.1
                                            have p6172_3 := h6172c.2.2.2
                                            linarith only [h4, hlam, p6172_0]
                                          · have p6172_0 := h6172c.1
                                            have p6172_1 := h6172c.2.1
                                            have p6172_2 := h6172c.2.2.1
                                            have p6172_3 := h6172c.2.2.2
                                            linarith only [h6132, hlam, p6172_0]
                                          · have p6172_0 := h6172c.1
                                            have p6172_1 := h6172c.2.1
                                            have p6172_2 := h6172c.2.2.1
                                            have p6172_3 := h6172c.2.2.2
                                            linarith only [hlam, p6172_0]
                                          · have p6172_0 := h6172c.1
                                            have p6172_1 := h6172c.2.1
                                            have p6172_2 := h6172c.2.2.1
                                            have p6172_3 := h6172c.2.2.2
                                            linarith only [h6141, hlam, p6172_0]
                                          · have p6172_0 := h6172c.1
                                            have p6172_1 := h6172c.2.1
                                            have p6172_2 := h6172c.2.2.1
                                            have p6172_3 := h6172c.2.2.2
                                            linarith only [h6143, hlam, p6172_0]
                                          · have p6172_0 := h6172c.1
                                            have p6172_1 := h6172c.2.1
                                            have p6172_2 := h6172c.2.2.1
                                            have p6172_3 := h6172c.2.2.2
                                            linarith only [hc03, hc34, hlam, hphi, p6172_1]
                                          · have p6172_0 := h6172c.1
                                            have p6172_1 := h6172c.2.1
                                            have p6172_2 := h6172c.2.2.1
                                            have p6172_3 := h6172c.2.2.2
                                            linarith only [h6132, hc23, hc34, hlam, hphi, p6172_1]
                                          · have p6172_0 := h6172c.1
                                            have p6172_1 := h6172c.2.1
                                            have p6172_2 := h6172c.2.2.1
                                            have p6172_3 := h6172c.2.2.2
                                            linarith only [hc23, hc34, hlam, hphi, p6172_1]
                                          · have p6172_0 := h6172c.1
                                            have p6172_1 := h6172c.2.1
                                            have p6172_2 := h6172c.2.2.1
                                            have p6172_3 := h6172c.2.2.2
                                            linarith only [hlam, p6172_0]
                                          · have p6172_0 := h6172c.1
                                            have p6172_1 := h6172c.2.1
                                            have p6172_2 := h6172c.2.2.1
                                            have p6172_3 := h6172c.2.2.2
                                            linarith only [h1, h6023, h6132, hc23, hc34, hlam, hphi, p6172_1]
                                          · have p6172_0 := h6172c.1
                                            have p6172_1 := h6172c.2.1
                                            have p6172_2 := h6172c.2.2.1
                                            have p6172_3 := h6172c.2.2.2
                                            linarith only [h1, h6132, hc23, hc35, hlam, hphi, p6172_1]
                                          · have p6172_0 := h6172c.1
                                            have p6172_1 := h6172c.2.1
                                            have p6172_2 := h6172c.2.2.1
                                            have p6172_3 := h6172c.2.2.2
                                            linarith only [h6132, hc23, hc35, hlam, hphi, p6172_1]
                                          · have p6172_0 := h6172c.1
                                            have p6172_1 := h6172c.2.1
                                            have p6172_2 := h6172c.2.2.1
                                            have p6172_3 := h6172c.2.2.2
                                            linarith only [hc23, hc35, hlam, hphi, p6172_1]
                                          · have p6172_0 := h6172c.1
                                            have p6172_1 := h6172c.2.1
                                            have p6172_2 := h6172c.2.2.1
                                            have p6172_3 := h6172c.2.2.2
                                            linarith only [h6146, hlam, p6172_0]
                                          · have p6172_0 := h6172c.1
                                            have p6172_1 := h6172c.2.1
                                            have p6172_2 := h6172c.2.2.1
                                            have p6172_3 := h6172c.2.2.2
                                            linarith only [hlam, p6172_0]
                                · linarith only [h6163, hlam, p6147_0]
                              · have p6147_0 := h6147c.1
                                have p6147_1 := h6147c.2.1
                                have p6147_2 := h6147c.2.2.1
                                have p6147_3 := h6147c.2.2.2
                                rcases p6147_3 (m.d 0 1) (by simp) with h6199 | h6199
                                · rcases p6147_3 (m.d 1 2) (by simp) with h6200 | h6200
                                  · linarith only [h0, h6200, hlam]
                                  · linarith only [h6135, h6200, hlam]
                                · linarith only [h6199, hlam, p6147_0]
                              · have p6147_0 := h6147c.1
                                have p6147_1 := h6147c.2.1
                                have p6147_2 := h6147c.2.2.1
                                have p6147_3 := h6147c.2.2.2
                                linarith only [h0, hlam, p6147_0]
                              · have p6147_0 := h6147c.1
                                have p6147_1 := h6147c.2.1
                                have p6147_2 := h6147c.2.2.1
                                have p6147_3 := h6147c.2.2.2
                                linarith only [hlam, p6147_0]
                              · have p6147_0 := h6147c.1
                                have p6147_1 := h6147c.2.1
                                have p6147_2 := h6147c.2.2.1
                                have p6147_3 := h6147c.2.2.2
                                linarith only [h0, h5, h6132, h6141, hc23, hc34, hlam, hphi, p6147_1]
                              · have p6147_0 := h6147c.1
                                have p6147_1 := h6147c.2.1
                                have p6147_2 := h6147c.2.2.1
                                have p6147_3 := h6147c.2.2.2
                                linarith only [h6133, hlam, p6147_0]
                              · have p6147_0 := h6147c.1
                                have p6147_1 := h6147c.2.1
                                have p6147_2 := h6147c.2.2.1
                                have p6147_3 := h6147c.2.2.2
                                linarith only [h0, h5, h6135, h6141, h6143, hc23, hc34, hlam, hphi, p6147_1]
                              · have p6147_0 := h6147c.1
                                have p6147_1 := h6147c.2.1
                                have p6147_2 := h6147c.2.2.1
                                have p6147_3 := h6147c.2.2.2
                                linarith only [h1, hlam, p6147_0]
                              · have p6147_0 := h6147c.1
                                have p6147_1 := h6147c.2.1
                                have p6147_2 := h6147c.2.2.1
                                have p6147_3 := h6147c.2.2.2
                                linarith only [h6132, hlam, p6147_1]
                              · have p6147_0 := h6147c.1
                                have p6147_1 := h6147c.2.1
                                have p6147_2 := h6147c.2.2.1
                                have p6147_3 := h6147c.2.2.2
                                linarith only [hlam, p6147_0]
                              · have p6147_0 := h6147c.1
                                have p6147_1 := h6147c.2.1
                                have p6147_2 := h6147c.2.2.1
                                have p6147_3 := h6147c.2.2.2
                                linarith only [h6136, hlam, p6147_1]
                              · have p6147_0 := h6147c.1
                                have p6147_1 := h6147c.2.1
                                have p6147_2 := h6147c.2.2.1
                                have p6147_3 := h6147c.2.2.2
                                linarith only [h6138, hlam, p6147_1]
                              · have p6147_0 := h6147c.1
                                have p6147_1 := h6147c.2.1
                                have p6147_2 := h6147c.2.2.1
                                have p6147_3 := h6147c.2.2.2
                                linarith only [h2, hlam, p6147_0]
                              · have p6147_0 := h6147c.1
                                have p6147_1 := h6147c.2.1
                                have p6147_2 := h6147c.2.2.1
                                have p6147_3 := h6147c.2.2.2
                                linarith only [h2, h6132, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6147_1]
                              · have p6147_0 := h6147c.1
                                have p6147_1 := h6147c.2.1
                                have p6147_2 := h6147c.2.2.1
                                have p6147_3 := h6147c.2.2.2
                                rcases p6147_3 (m.d 0 1) (by simp) with h6216 | h6216
                                · rcases p6147_3 (m.d 1 2) (by simp) with h6217 | h6217
                                  · linarith only [h6133, h6217, hlam]
                                  · linarith only [h6132, h6217, hlam]
                                · linarith only [h1, h6216, hlam]
                              · have p6147_0 := h6147c.1
                                have p6147_1 := h6147c.2.1
                                have p6147_2 := h6147c.2.2.1
                                have p6147_3 := h6147c.2.2.2
                                linarith only [hlam, p6147_0]
                              · have p6147_0 := h6147c.1
                                have p6147_1 := h6147c.2.1
                                have p6147_2 := h6147c.2.2.1
                                have p6147_3 := h6147c.2.2.2
                                rcases p6147_3 (m.d 0 1) (by simp) with h6222 | h6222
                                · rcases p6147_3 (m.d 1 2) (by simp) with h6223 | h6223
                                  · linarith only [h6133, h6223, hlam]
                                  · linarith only [h6135, h6223, hlam]
                                · linarith only [h3, h6222, hlam]
                              · have p6147_0 := h6147c.1
                                have p6147_1 := h6147c.2.1
                                have p6147_2 := h6147c.2.2.1
                                have p6147_3 := h6147c.2.2.2
                                linarith only [h3, hlam, p6147_0]
                              · have p6147_0 := h6147c.1
                                have p6147_1 := h6147c.2.1
                                have p6147_2 := h6147c.2.2.1
                                have p6147_3 := h6147c.2.2.2
                                linarith only [h6135, hlam, p6147_1]
                              · have p6147_0 := h6147c.1
                                have p6147_1 := h6147c.2.1
                                have p6147_2 := h6147c.2.2.1
                                have p6147_3 := h6147c.2.2.2
                                linarith only [h0, h5, h6132, h6135, h6141, hc23, hc34, hlam, hphi, p6147_1]
                              · have p6147_0 := h6147c.1
                                have p6147_1 := h6147c.2.1
                                have p6147_2 := h6147c.2.2.1
                                have p6147_3 := h6147c.2.2.2
                                linarith only [h6140, hlam, p6147_0]
                              · have p6147_0 := h6147c.1
                                have p6147_1 := h6147c.2.1
                                have p6147_2 := h6147c.2.2.1
                                have p6147_3 := h6147c.2.2.2
                                linarith only [hlam, p6147_0]
                            · linarith only [h4, h5, h6141, h6146, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h0, h5, h6135, h6140, h6145, hlam]
                    · linarith only [h6021, h6131, h6132, h6133, h6140, hc23, hc34, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6235 | h6235
                · linarith only [h1, h4, h5, h6021, h6235, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6237 | h6237
                  · linarith only [h1, h6023, h6237, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6239 | h6239
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6240 | h6240
                      · linarith only [h3, h4, h5, h6021, h6131, h6135, h6240, hc12, hc24, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6242 | h6242
                        · linarith only [h3, h6023, h6132, h6135, h6242, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6244 | h6244
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h6245 | h6245
                            · rcases h1bigk with h6246c | h6246c | h6246c | h6246c | h6246c | h6246c | h6246c | h6246c | h6246c | h6246c | h6246c | h6246c | h6246c | h6246c | h6246c | h6246c | h6246c | h6246c | h6246c | h6246c | h6246c | h6246c | h6246c | h6246c | h6246c
                              · have p6246_0 := h6246c.1
                                have p6246_1 := h6246c.2.1
                                have p6246_2 := h6246c.2.2.1
                                have p6246_3 := h6246c.2.2.2
                                linarith only [hlam, p6246_0]
                              · have p6246_0 := h6246c.1
                                have p6246_1 := h6246c.2.1
                                have p6246_2 := h6246c.2.2.1
                                have p6246_3 := h6246c.2.2.2
                                rcases p6246_3 (m.d 0 1) (by simp) with h6248 | h6248
                                · rcases p6246_3 (m.d 1 2) (by simp) with h6249 | h6249
                                  · linarith only [h6249, hlam, p6246_0]
                                  · rcases p6246_3 (m.d 1 3) (by simp) with h6251 | h6251
                                    · linarith only [h1, h6251, hlam]
                                    · rcases p6246_3 (m.d 1 4) (by simp) with h6253 | h6253
                                      · linarith only [h2, h6253, hlam]
                                      · linarith only [h6133, h6253, hlam]
                                · linarith only [h6248, hlam, p6246_0]
                              · have p6246_0 := h6246c.1
                                have p6246_1 := h6246c.2.1
                                have p6246_2 := h6246c.2.2.1
                                have p6246_3 := h6246c.2.2.2
                                rcases p6246_3 (m.d 0 1) (by simp) with h6257 | h6257
                                · rcases p6246_3 (m.d 1 2) (by simp) with h6258 | h6258
                                  · linarith only [h0, h6258, hlam]
                                  · linarith only [h6132, h6258, hlam]
                                · linarith only [h6257, hlam, p6246_0]
                              · have p6246_0 := h6246c.1
                                have p6246_1 := h6246c.2.1
                                have p6246_2 := h6246c.2.2.1
                                have p6246_3 := h6246c.2.2.2
                                rcases p6246_3 (m.d 0 1) (by simp) with h6262 | h6262
                                · rcases p6246_3 (m.d 1 2) (by simp) with h6263 | h6263
                                  · linarith only [h0, h6263, hlam]
                                  · rcases p6246_3 (m.d 1 3) (by simp) with h6265 | h6265
                                    · linarith only [h1, h6265, hlam]
                                    · rcases p6246_3 (m.d 1 4) (by simp) with h6267 | h6267
                                      · linarith only [h6267, hlam, p6246_0]
                                      · rcases p6246_3 (m.d 1 5) (by simp) with h6269 | h6269
                                        · linarith only [h3, h6269, hlam]
                                        · rcases h3bigk with h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c | h6271c
                                          · have p6271_0 := h6271c.1
                                            have p6271_1 := h6271c.2.1
                                            have p6271_2 := h6271c.2.2.1
                                            have p6271_3 := h6271c.2.2.2
                                            linarith only [hlam, p6271_0]
                                          · have p6271_0 := h6271c.1
                                            have p6271_1 := h6271c.2.1
                                            have p6271_2 := h6271c.2.2.1
                                            have p6271_3 := h6271c.2.2.2
                                            linarith only [h4, h5, h6132, h6240, hc23, hc34, hlam, hphi, p6271_1]
                                          · have p6271_0 := h6271c.1
                                            have p6271_1 := h6271c.2.1
                                            have p6271_2 := h6271c.2.2.1
                                            have p6271_3 := h6271c.2.2.2
                                            linarith only [h4, h5, h6240, hc23, hc34, hlam, hphi, p6271_1]
                                          · have p6271_0 := h6271c.1
                                            have p6271_1 := h6271c.2.1
                                            have p6271_2 := h6271c.2.2.1
                                            have p6271_3 := h6271c.2.2.2
                                            linarith only [h6021, hlam, p6271_0]
                                          · have p6271_0 := h6271c.1
                                            have p6271_1 := h6271c.2.1
                                            have p6271_2 := h6271c.2.2.1
                                            have p6271_3 := h6271c.2.2.2
                                            linarith only [h6023, hlam, p6271_0]
                                          · have p6271_0 := h6271c.1
                                            have p6271_1 := h6271c.2.1
                                            have p6271_2 := h6271c.2.2.1
                                            have p6271_3 := h6271c.2.2.2
                                            linarith only [h1, hlam, p6271_0]
                                          · have p6271_0 := h6271c.1
                                            have p6271_1 := h6271c.2.1
                                            have p6271_2 := h6271c.2.2.1
                                            have p6271_3 := h6271c.2.2.2
                                            linarith only [hlam, p6271_0]
                                          · have p6271_0 := h6271c.1
                                            have p6271_1 := h6271c.2.1
                                            have p6271_2 := h6271c.2.2.1
                                            have p6271_3 := h6271c.2.2.2
                                            linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6271_1]
                                          · have p6271_0 := h6271c.1
                                            have p6271_1 := h6271c.2.1
                                            have p6271_2 := h6271c.2.2.1
                                            have p6271_3 := h6271c.2.2.2
                                            linarith only [h6235, hlam, p6271_0]
                                          · have p6271_0 := h6271c.1
                                            have p6271_1 := h6271c.2.1
                                            have p6271_2 := h6271c.2.2.1
                                            have p6271_3 := h6271c.2.2.2
                                            linarith only [h6237, hlam, p6271_0]
                                          · have p6271_0 := h6271c.1
                                            have p6271_1 := h6271c.2.1
                                            have p6271_2 := h6271c.2.2.1
                                            have p6271_3 := h6271c.2.2.2
                                            linarith only [h4, hlam, p6271_0]
                                          · have p6271_0 := h6271c.1
                                            have p6271_1 := h6271c.2.1
                                            have p6271_2 := h6271c.2.2.1
                                            have p6271_3 := h6271c.2.2.2
                                            linarith only [h6132, hlam, p6271_0]
                                          · have p6271_0 := h6271c.1
                                            have p6271_1 := h6271c.2.1
                                            have p6271_2 := h6271c.2.2.1
                                            have p6271_3 := h6271c.2.2.2
                                            linarith only [hlam, p6271_0]
                                          · have p6271_0 := h6271c.1
                                            have p6271_1 := h6271c.2.1
                                            have p6271_2 := h6271c.2.2.1
                                            have p6271_3 := h6271c.2.2.2
                                            linarith only [h6240, hlam, p6271_0]
                                          · have p6271_0 := h6271c.1
                                            have p6271_1 := h6271c.2.1
                                            have p6271_2 := h6271c.2.2.1
                                            have p6271_3 := h6271c.2.2.2
                                            linarith only [h6242, hlam, p6271_0]
                                          · have p6271_0 := h6271c.1
                                            have p6271_1 := h6271c.2.1
                                            have p6271_2 := h6271c.2.2.1
                                            have p6271_3 := h6271c.2.2.2
                                            linarith only [hc03, hc34, hlam, hphi, p6271_1]
                                          · have p6271_0 := h6271c.1
                                            have p6271_1 := h6271c.2.1
                                            have p6271_2 := h6271c.2.2.1
                                            have p6271_3 := h6271c.2.2.2
                                            linarith only [h6132, hc23, hc34, hlam, hphi, p6271_1]
                                          · have p6271_0 := h6271c.1
                                            have p6271_1 := h6271c.2.1
                                            have p6271_2 := h6271c.2.2.1
                                            have p6271_3 := h6271c.2.2.2
                                            linarith only [hc23, hc34, hlam, hphi, p6271_1]
                                          · have p6271_0 := h6271c.1
                                            have p6271_1 := h6271c.2.1
                                            have p6271_2 := h6271c.2.2.1
                                            have p6271_3 := h6271c.2.2.2
                                            linarith only [hlam, p6271_0]
                                          · have p6271_0 := h6271c.1
                                            have p6271_1 := h6271c.2.1
                                            have p6271_2 := h6271c.2.2.1
                                            have p6271_3 := h6271c.2.2.2
                                            linarith only [h6132, h6135, h6242, hc23, hc34, hlam, hphi, p6271_1]
                                          · have p6271_0 := h6271c.1
                                            have p6271_1 := h6271c.2.1
                                            have p6271_2 := h6271c.2.2.1
                                            have p6271_3 := h6271c.2.2.2
                                            linarith only [h1, h6132, hc23, hc35, hlam, hphi, p6271_1]
                                          · have p6271_0 := h6271c.1
                                            have p6271_1 := h6271c.2.1
                                            have p6271_2 := h6271c.2.2.1
                                            have p6271_3 := h6271c.2.2.2
                                            linarith only [h6132, hc23, hc35, hlam, hphi, p6271_1]
                                          · have p6271_0 := h6271c.1
                                            have p6271_1 := h6271c.2.1
                                            have p6271_2 := h6271c.2.2.1
                                            have p6271_3 := h6271c.2.2.2
                                            linarith only [hc23, hc35, hlam, hphi, p6271_1]
                                          · have p6271_0 := h6271c.1
                                            have p6271_1 := h6271c.2.1
                                            have p6271_2 := h6271c.2.2.1
                                            have p6271_3 := h6271c.2.2.2
                                            linarith only [h6245, hlam, p6271_0]
                                          · have p6271_0 := h6271c.1
                                            have p6271_1 := h6271c.2.1
                                            have p6271_2 := h6271c.2.2.1
                                            have p6271_3 := h6271c.2.2.2
                                            linarith only [hlam, p6271_0]
                                · linarith only [h6262, hlam, p6246_0]
                              · have p6246_0 := h6246c.1
                                have p6246_1 := h6246c.2.1
                                have p6246_2 := h6246c.2.2.1
                                have p6246_3 := h6246c.2.2.2
                                rcases p6246_3 (m.d 0 1) (by simp) with h6298 | h6298
                                · rcases p6246_3 (m.d 1 2) (by simp) with h6299 | h6299
                                  · linarith only [h0, h6299, hlam]
                                  · rcases p6246_3 (m.d 1 3) (by simp) with h6301 | h6301
                                    · linarith only [h1, h6301, hlam]
                                    · rcases p6246_3 (m.d 1 4) (by simp) with h6303 | h6303
                                      · linarith only [h2, h6303, hlam]
                                      · linarith only [h6239, h6303, hlam]
                                · linarith only [h6298, hlam, p6246_0]
                              · have p6246_0 := h6246c.1
                                have p6246_1 := h6246c.2.1
                                have p6246_2 := h6246c.2.2.1
                                have p6246_3 := h6246c.2.2.2
                                linarith only [h0, hlam, p6246_0]
                              · have p6246_0 := h6246c.1
                                have p6246_1 := h6246c.2.1
                                have p6246_2 := h6246c.2.2.1
                                have p6246_3 := h6246c.2.2.2
                                linarith only [hlam, p6246_0]
                              · have p6246_0 := h6246c.1
                                have p6246_1 := h6246c.2.1
                                have p6246_2 := h6246c.2.2.1
                                have p6246_3 := h6246c.2.2.2
                                linarith only [h0, h5, h6132, h6240, hc23, hc34, hlam, hphi, p6246_1]
                              · have p6246_0 := h6246c.1
                                have p6246_1 := h6246c.2.1
                                have p6246_2 := h6246c.2.2.1
                                have p6246_3 := h6246c.2.2.2
                                linarith only [h6133, hlam, p6246_0]
                              · have p6246_0 := h6246c.1
                                have p6246_1 := h6246c.2.1
                                have p6246_2 := h6246c.2.2.1
                                have p6246_3 := h6246c.2.2.2
                                linarith only [h6135, hlam, p6246_0]
                              · have p6246_0 := h6246c.1
                                have p6246_1 := h6246c.2.1
                                have p6246_2 := h6246c.2.2.1
                                have p6246_3 := h6246c.2.2.2
                                linarith only [h1, hlam, p6246_0]
                              · have p6246_0 := h6246c.1
                                have p6246_1 := h6246c.2.1
                                have p6246_2 := h6246c.2.2.1
                                have p6246_3 := h6246c.2.2.2
                                linarith only [h6132, hlam, p6246_1]
                              · have p6246_0 := h6246c.1
                                have p6246_1 := h6246c.2.1
                                have p6246_2 := h6246c.2.2.1
                                have p6246_3 := h6246c.2.2.2
                                linarith only [hlam, p6246_0]
                              · have p6246_0 := h6246c.1
                                have p6246_1 := h6246c.2.1
                                have p6246_2 := h6246c.2.2.1
                                have p6246_3 := h6246c.2.2.2
                                linarith only [h6235, hlam, p6246_1]
                              · have p6246_0 := h6246c.1
                                have p6246_1 := h6246c.2.1
                                have p6246_2 := h6246c.2.2.1
                                have p6246_3 := h6246c.2.2.2
                                linarith only [h6237, hlam, p6246_1]
                              · have p6246_0 := h6246c.1
                                have p6246_1 := h6246c.2.1
                                have p6246_2 := h6246c.2.2.1
                                have p6246_3 := h6246c.2.2.2
                                linarith only [h2, hlam, p6246_0]
                              · have p6246_0 := h6246c.1
                                have p6246_1 := h6246c.2.1
                                have p6246_2 := h6246c.2.2.1
                                have p6246_3 := h6246c.2.2.2
                                linarith only [h2, h6132, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6246_1]
                              · have p6246_0 := h6246c.1
                                have p6246_1 := h6246c.2.1
                                have p6246_2 := h6246c.2.2.1
                                have p6246_3 := h6246c.2.2.2
                                rcases p6246_3 (m.d 0 1) (by simp) with h6319 | h6319
                                · rcases p6246_3 (m.d 1 2) (by simp) with h6320 | h6320
                                  · linarith only [h6133, h6320, hlam]
                                  · linarith only [h6132, h6320, hlam]
                                · linarith only [h1, h6319, hlam]
                              · have p6246_0 := h6246c.1
                                have p6246_1 := h6246c.2.1
                                have p6246_2 := h6246c.2.2.1
                                have p6246_3 := h6246c.2.2.2
                                linarith only [hlam, p6246_0]
                              · have p6246_0 := h6246c.1
                                have p6246_1 := h6246c.2.1
                                have p6246_2 := h6246c.2.2.1
                                have p6246_3 := h6246c.2.2.2
                                linarith only [h2, h6132, h6135, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6246_1]
                              · have p6246_0 := h6246c.1
                                have p6246_1 := h6246c.2.1
                                have p6246_2 := h6246c.2.2.1
                                have p6246_3 := h6246c.2.2.2
                                linarith only [h3, hlam, p6246_0]
                              · have p6246_0 := h6246c.1
                                have p6246_1 := h6246c.2.1
                                have p6246_2 := h6246c.2.2.1
                                have p6246_3 := h6246c.2.2.2
                                linarith only [h3, h6132, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6246_1]
                              · have p6246_0 := h6246c.1
                                have p6246_1 := h6246c.2.1
                                have p6246_2 := h6246c.2.2.1
                                have p6246_3 := h6246c.2.2.2
                                rcases p6246_3 (m.d 0 1) (by simp) with h6328 | h6328
                                · rcases p6246_3 (m.d 1 2) (by simp) with h6329 | h6329
                                  · linarith only [h6135, h6329, hlam]
                                  · linarith only [h6132, h6329, hlam]
                                · linarith only [h1, h6328, hlam]
                              · have p6246_0 := h6246c.1
                                have p6246_1 := h6246c.2.1
                                have p6246_2 := h6246c.2.2.1
                                have p6246_3 := h6246c.2.2.2
                                linarith only [h6239, hlam, p6246_0]
                              · have p6246_0 := h6246c.1
                                have p6246_1 := h6246c.2.1
                                have p6246_2 := h6246c.2.2.1
                                have p6246_3 := h6246c.2.2.2
                                linarith only [hlam, p6246_0]
                            · linarith only [h0, h5, h6132, h6240, h6245, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h2, h5, h6239, h6244, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h6021, h6131, h6132, h6133, h6239, hc23, hc34, hlam, hphi]
          · linarith only [h4, h5, h6132, hc12, hc24, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6339 | h6339
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6340 | h6340
            · linarith only [h0, h5, h6340, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6342 | h6342
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6343 | h6343
                · linarith only [h1, h4, h5, h6021, h6343, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6345 | h6345
                  · linarith only [h1, h6023, h6345, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6347 | h6347
                    · linarith only [h0, h2, h5, h6131, h6342, h6347, hc01, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h6340, h6342, h6347, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6350 | h6350
                · linarith only [h1, h6021, h6350, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6352 | h6352
                  · linarith only [h1, h6023, h6352, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6354 | h6354
                    · linarith only [h2, h6131, h6354, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6356 | h6356
                      · linarith only [h2, h6021, h6339, h6340, h6356, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6358 | h6358
                        · linarith only [h2, h6023, h6131, h6339, h6340, h6358, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6360 | h6360
                          · linarith only [h2, h6131, h6339, h6340, h6356, h6360, hc23, hc34, hlam, hphi]
                          · linarith only [h0, h5, h6339, h6360, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h4, h5, h6339, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 5858000 in
set_option maxHeartbeats 5858000 in
theorem r1l7_11_23_L_I_H_I_s10_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg6364 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h7232 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7233 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h7234 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7235 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h6364 := hg6364
  linarith only [h0, h4, h7235, hlam]

set_option maxHeartbeats 5858000 in
set_option maxHeartbeats 5858000 in
theorem r1l7_11_23_L_I_H_I_s10_x0_x0_x0_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg6364 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h7232 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7233 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h7234 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7235 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h7237 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h6364 := hg6364
  linarith only [h0, h6364, h7237, hlam]

set_option maxHeartbeats 5858000 in
set_option maxHeartbeats 5858000 in
theorem r1l7_11_23_L_I_H_I_s10_x0_x0_x0_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg6364 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h7232 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7233 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h7234 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7235 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h7237 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h7239 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h6364 := hg6364
  rcases m.htr 1 3 4 (by decide) (by decide) with h7240 | h7240
  · rcases m.htr 1 3 5 (by decide) (by decide) with h7241 | h7241
    · rcases m.htr 1 4 5 (by decide) (by decide) with h7242 | h7242
      · rcases m.htr 2 3 4 (by decide) (by decide) with h7243 | h7243
        · rcases m.htr 2 3 5 (by decide) (by decide) with h7244 | h7244
          · rcases m.htr 2 4 5 (by decide) (by decide) with h7245 | h7245
            · rcases m.htr 3 4 5 (by decide) (by decide) with h7246 | h7246
              · rcases h1bigk with h7247c | h7247c | h7247c | h7247c | h7247c | h7247c | h7247c | h7247c | h7247c | h7247c | h7247c | h7247c | h7247c | h7247c | h7247c | h7247c | h7247c | h7247c | h7247c | h7247c | h7247c | h7247c | h7247c | h7247c | h7247c
                · have p7247_0 := h7247c.1
                  have p7247_1 := h7247c.2.1
                  have p7247_2 := h7247c.2.2.1
                  have p7247_3 := h7247c.2.2.2
                  linarith only [hlam, p7247_0]
                · have p7247_0 := h7247c.1
                  have p7247_1 := h7247c.2.1
                  have p7247_2 := h7247c.2.2.1
                  have p7247_3 := h7247c.2.2.2
                  rcases p7247_3 (m.d 0 1) (by simp) with h7249 | h7249
                  · rcases p7247_3 (m.d 1 2) (by simp) with h7250 | h7250
                    · linarith only [h7250, hlam, p7247_0]
                    · rcases p7247_3 (m.d 1 3) (by simp) with h7252 | h7252
                      · linarith only [h1, h7252, hlam]
                      · linarith only [h7235, h7252, hlam]
                  · linarith only [h7249, hlam, p7247_0]
                · have p7247_0 := h7247c.1
                  have p7247_1 := h7247c.2.1
                  have p7247_2 := h7247c.2.2.1
                  have p7247_3 := h7247c.2.2.2
                  linarith only [h7240, h7246, hc01, hc45, hlam, hphi, ht0b, ht5b, p7247_1]
                · have p7247_0 := h7247c.1
                  have p7247_1 := h7247c.2.1
                  have p7247_2 := h7247c.2.2.1
                  have p7247_3 := h7247c.2.2.2
                  rcases p7247_3 (m.d 0 1) (by simp) with h7257 | h7257
                  · rcases p7247_3 (m.d 1 2) (by simp) with h7258 | h7258
                    · linarith only [h0, h7258, hlam]
                    · rcases p7247_3 (m.d 1 3) (by simp) with h7260 | h7260
                      · linarith only [h1, h7260, hlam]
                      · linarith only [h7240, h7260, hlam]
                  · linarith only [h7257, hlam, p7247_0]
                · have p7247_0 := h7247c.1
                  have p7247_1 := h7247c.2.1
                  have p7247_2 := h7247c.2.2.1
                  have p7247_3 := h7247c.2.2.2
                  rcases p7247_3 (m.d 0 1) (by simp) with h7264 | h7264
                  · rcases p7247_3 (m.d 1 2) (by simp) with h7265 | h7265
                    · linarith only [h0, h7265, hlam]
                    · linarith only [h7239, h7265, hlam]
                  · linarith only [h7264, hlam, p7247_0]
                · have p7247_0 := h7247c.1
                  have p7247_1 := h7247c.2.1
                  have p7247_2 := h7247c.2.2.1
                  have p7247_3 := h7247c.2.2.2
                  linarith only [h0, hlam, p7247_0]
                · have p7247_0 := h7247c.1
                  have p7247_1 := h7247c.2.1
                  have p7247_2 := h7247c.2.2.1
                  have p7247_3 := h7247c.2.2.2
                  linarith only [hlam, p7247_0]
                · have p7247_0 := h7247c.1
                  have p7247_1 := h7247c.2.1
                  have p7247_2 := h7247c.2.2.1
                  have p7247_3 := h7247c.2.2.2
                  linarith only [h7235, hlam, p7247_0]
                · have p7247_0 := h7247c.1
                  have p7247_1 := h7247c.2.1
                  have p7247_2 := h7247c.2.2.1
                  have p7247_3 := h7247c.2.2.2
                  linarith only [h7237, hlam, p7247_0]
                · have p7247_0 := h7247c.1
                  have p7247_1 := h7247c.2.1
                  have p7247_2 := h7247c.2.2.1
                  have p7247_3 := h7247c.2.2.2
                  rcases p7247_3 (m.d 0 1) (by simp) with h7273 | h7273
                  · rcases p7247_3 (m.d 1 2) (by simp) with h7274 | h7274
                    · rcases p7247_3 (m.d 1 3) (by simp) with h7275 | h7275
                      · rcases p7247_3 (m.d 1 4) (by simp) with h7276 | h7276
                        · rcases p7247_3 (m.d 1 5) (by simp) with h7277 | h7277
                          · linarith only [h7239, h7277, hlam]
                          · rcases h3bigk with h7279c | h7279c | h7279c | h7279c | h7279c | h7279c | h7279c | h7279c | h7279c | h7279c | h7279c | h7279c | h7279c | h7279c | h7279c | h7279c | h7279c | h7279c | h7279c | h7279c | h7279c | h7279c | h7279c | h7279c | h7279c
                            · have p7279_0 := h7279c.1
                              have p7279_1 := h7279c.2.1
                              have p7279_2 := h7279c.2.2.1
                              have p7279_3 := h7279c.2.2.2
                              linarith only [hlam, p7279_0]
                            · have p7279_0 := h7279c.1
                              have p7279_1 := h7279c.2.1
                              have p7279_2 := h7279c.2.2.1
                              have p7279_3 := h7279c.2.2.2
                              linarith only [h7237, h7239, h7240, h7244, h7246, hc03, hc45, hlam, hphi, ht0b, ht5b, p7247_1, p7279_1]
                            · have p7279_0 := h7279c.1
                              have p7279_1 := h7279c.2.1
                              have p7279_2 := h7279c.2.2.1
                              have p7279_3 := h7279c.2.2.2
                              linarith only [h4, hlam, p7279_1]
                            · have p7279_0 := h7279c.1
                              have p7279_1 := h7279c.2.1
                              have p7279_2 := h7279c.2.2.1
                              have p7279_3 := h7279c.2.2.2
                              linarith only [h7246, hc03, hc45, hlam, hphi, ht0b, ht5b, p7279_1]
                            · have p7279_0 := h7279c.1
                              have p7279_1 := h7279c.2.1
                              have p7279_2 := h7279c.2.2.1
                              have p7279_3 := h7279c.2.2.2
                              rcases p7279_3 (m.d 0 3) (by simp) with h7284 | h7284
                              · rcases p7279_3 (m.d 1 3) (by simp) with h7285 | h7285
                                · linarith only [h1, h7285, hlam]
                                · linarith only [h7241, h7285, hlam]
                              · linarith only [h7284, hlam, p7279_0]
                            · have p7279_0 := h7279c.1
                              have p7279_1 := h7279c.2.1
                              have p7279_2 := h7279c.2.2.1
                              have p7279_3 := h7279c.2.2.2
                              linarith only [h1, hlam, p7279_0]
                            · have p7279_0 := h7279c.1
                              have p7279_1 := h7279c.2.1
                              have p7279_2 := h7279c.2.2.1
                              have p7279_3 := h7279c.2.2.2
                              linarith only [hlam, p7279_0]
                            · have p7279_0 := h7279c.1
                              have p7279_1 := h7279c.2.1
                              have p7279_2 := h7279c.2.2.1
                              have p7279_3 := h7279c.2.2.2
                              linarith only [h7235, hlam, p7279_1]
                            · have p7279_0 := h7279c.1
                              have p7279_1 := h7279c.2.1
                              have p7279_2 := h7279c.2.2.1
                              have p7279_3 := h7279c.2.2.2
                              linarith only [h7246, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p7279_1]
                            · have p7279_0 := h7279c.1
                              have p7279_1 := h7279c.2.1
                              have p7279_2 := h7279c.2.2.1
                              have p7279_3 := h7279c.2.2.2
                              linarith only [h1, h7246, hc01, hc45, hlam, hphi, ht0b, ht5b, p7279_1]
                            · have p7279_0 := h7279c.1
                              have p7279_1 := h7279c.2.1
                              have p7279_2 := h7279c.2.2.1
                              have p7279_3 := h7279c.2.2.2
                              linarith only [h0, h4, h7239, h7244, h7246, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7247_1, p7279_1]
                            · have p7279_0 := h7279c.1
                              have p7279_1 := h7279c.2.1
                              have p7279_2 := h7279c.2.2.1
                              have p7279_3 := h7279c.2.2.2
                              linarith only [h7235, h7239, h7244, h7246, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7247_1, p7279_1]
                            · have p7279_0 := h7279c.1
                              have p7279_1 := h7279c.2.1
                              have p7279_2 := h7279c.2.2.1
                              have p7279_3 := h7279c.2.2.2
                              linarith only [hlam, p7279_0]
                            · have p7279_0 := h7279c.1
                              have p7279_1 := h7279c.2.1
                              have p7279_2 := h7279c.2.2.1
                              have p7279_3 := h7279c.2.2.2
                              linarith only [h7246, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7279_1]
                            · have p7279_0 := h7279c.1
                              have p7279_1 := h7279c.2.1
                              have p7279_2 := h7279c.2.2.1
                              have p7279_3 := h7279c.2.2.2
                              rcases p7279_3 (m.d 0 3) (by simp) with h7298 | h7298
                              · linarith only [h4, h7298, hlam]
                              · linarith only [h7233, h7298, hlam]
                            · have p7279_0 := h7279c.1
                              have p7279_1 := h7279c.2.1
                              have p7279_2 := h7279c.2.2.1
                              have p7279_3 := h7279c.2.2.2
                              linarith only [h7232, hlam, p7279_0]
                            · have p7279_0 := h7279c.1
                              have p7279_1 := h7279c.2.1
                              have p7279_2 := h7279c.2.2.1
                              have p7279_3 := h7279c.2.2.2
                              linarith only [h7240, hlam, p7279_0]
                            · have p7279_0 := h7279c.1
                              have p7279_1 := h7279c.2.1
                              have p7279_2 := h7279c.2.2.1
                              have p7279_3 := h7279c.2.2.2
                              linarith only [h7243, hlam, p7279_0]
                            · have p7279_0 := h7279c.1
                              have p7279_1 := h7279c.2.1
                              have p7279_2 := h7279c.2.2.1
                              have p7279_3 := h7279c.2.2.2
                              linarith only [hlam, p7279_0]
                            · have p7279_0 := h7279c.1
                              have p7279_1 := h7279c.2.1
                              have p7279_2 := h7279c.2.2.1
                              have p7279_3 := h7279c.2.2.2
                              linarith only [h7232, h7246, hc03, hc45, hlam, hphi, ht0b, ht5b, p7279_1]
                            · have p7279_0 := h7279c.1
                              have p7279_1 := h7279c.2.1
                              have p7279_2 := h7279c.2.2.1
                              have p7279_3 := h7279c.2.2.2
                              linarith only [h7233, hlam, p7279_0]
                            · have p7279_0 := h7279c.1
                              have p7279_1 := h7279c.2.1
                              have p7279_2 := h7279c.2.2.1
                              have p7279_3 := h7279c.2.2.2
                              linarith only [h7241, hlam, p7279_0]
                            · have p7279_0 := h7279c.1
                              have p7279_1 := h7279c.2.1
                              have p7279_2 := h7279c.2.2.1
                              have p7279_3 := h7279c.2.2.2
                              linarith only [h7244, hlam, p7279_0]
                            · have p7279_0 := h7279c.1
                              have p7279_1 := h7279c.2.1
                              have p7279_2 := h7279c.2.2.1
                              have p7279_3 := h7279c.2.2.2
                              linarith only [h7246, hlam, p7279_0]
                            · have p7279_0 := h7279c.1
                              have p7279_1 := h7279c.2.1
                              have p7279_2 := h7279c.2.2.1
                              have p7279_3 := h7279c.2.2.2
                              linarith only [hlam, p7279_0]
                        · linarith only [h7242, h7276, hlam]
                      · linarith only [h7241, h7275, hlam]
                    · linarith only [h7239, h7274, hlam]
                  · linarith only [h3, h7273, hlam]
                · have p7247_0 := h7247c.1
                  have p7247_1 := h7247c.2.1
                  have p7247_2 := h7247c.2.2.1
                  have p7247_3 := h7247c.2.2.2
                  linarith only [h1, hlam, p7247_0]
                · have p7247_0 := h7247c.1
                  have p7247_1 := h7247c.2.1
                  have p7247_2 := h7247c.2.2.1
                  have p7247_3 := h7247c.2.2.2
                  linarith only [h1, h7239, h7244, h7246, hc01, hc45, hlam, hphi, ht0b, ht5b, p7247_1]
                · have p7247_0 := h7247c.1
                  have p7247_1 := h7247c.2.1
                  have p7247_2 := h7247c.2.2.1
                  have p7247_3 := h7247c.2.2.2
                  linarith only [hlam, p7247_0]
                · have p7247_0 := h7247c.1
                  have p7247_1 := h7247c.2.1
                  have p7247_2 := h7247c.2.2.1
                  have p7247_3 := h7247c.2.2.2
                  linarith only [h1, h7237, h7239, h7244, h7246, hc01, hc45, hlam, hphi, ht0b, ht5b, p7247_1]
                · have p7247_0 := h7247c.1
                  have p7247_1 := h7247c.2.1
                  have p7247_2 := h7247c.2.2.1
                  have p7247_3 := h7247c.2.2.2
                  rcases p7247_3 (m.d 0 1) (by simp) with h7319 | h7319
                  · rcases p7247_3 (m.d 1 2) (by simp) with h7320 | h7320
                    · linarith only [h7235, h7320, hlam]
                    · linarith only [h7239, h7320, hlam]
                  · linarith only [h3, h7319, hlam]
                · have p7247_0 := h7247c.1
                  have p7247_1 := h7247c.2.1
                  have p7247_2 := h7247c.2.2.1
                  have p7247_3 := h7247c.2.2.2
                  linarith only [h2, hlam, p7247_0]
                · have p7247_0 := h7247c.1
                  have p7247_1 := h7247c.2.1
                  have p7247_2 := h7247c.2.2.1
                  have p7247_3 := h7247c.2.2.2
                  linarith only [h2, h7239, h7244, h7246, hc01, hc45, hlam, hphi, ht0b, ht5b, p7247_1]
                · have p7247_0 := h7247c.1
                  have p7247_1 := h7247c.2.1
                  have p7247_2 := h7247c.2.2.1
                  have p7247_3 := h7247c.2.2.2
                  linarith only [h7240, hlam, p7247_0]
                · have p7247_0 := h7247c.1
                  have p7247_1 := h7247c.2.1
                  have p7247_2 := h7247c.2.2.1
                  have p7247_3 := h7247c.2.2.2
                  linarith only [hlam, p7247_0]
                · have p7247_0 := h7247c.1
                  have p7247_1 := h7247c.2.1
                  have p7247_2 := h7247c.2.2.1
                  have p7247_3 := h7247c.2.2.2
                  rcases p7247_3 (m.d 0 1) (by simp) with h7328 | h7328
                  · rcases p7247_3 (m.d 1 2) (by simp) with h7329 | h7329
                    · linarith only [h7237, h7329, hlam]
                    · linarith only [h7239, h7329, hlam]
                  · linarith only [h3, h7328, hlam]
                · have p7247_0 := h7247c.1
                  have p7247_1 := h7247c.2.1
                  have p7247_2 := h7247c.2.2.1
                  have p7247_3 := h7247c.2.2.2
                  linarith only [h3, hlam, p7247_0]
                · have p7247_0 := h7247c.1
                  have p7247_1 := h7247c.2.1
                  have p7247_2 := h7247c.2.2.1
                  have p7247_3 := h7247c.2.2.2
                  linarith only [h7239, hlam, p7247_1]
                · have p7247_0 := h7247c.1
                  have p7247_1 := h7247c.2.1
                  have p7247_2 := h7247c.2.2.1
                  have p7247_3 := h7247c.2.2.2
                  linarith only [h7241, hlam, p7247_0]
                · have p7247_0 := h7247c.1
                  have p7247_1 := h7247c.2.1
                  have p7247_2 := h7247c.2.2.1
                  have p7247_3 := h7247c.2.2.2
                  linarith only [h7242, hlam, p7247_0]
                · have p7247_0 := h7247c.1
                  have p7247_1 := h7247c.2.1
                  have p7247_2 := h7247c.2.2.1
                  have p7247_3 := h7247c.2.2.2
                  linarith only [hlam, p7247_0]
              · rcases h1bigk with h7338c | h7338c | h7338c | h7338c | h7338c | h7338c | h7338c | h7338c | h7338c | h7338c | h7338c | h7338c | h7338c | h7338c | h7338c | h7338c | h7338c | h7338c | h7338c | h7338c | h7338c | h7338c | h7338c | h7338c | h7338c
                · have p7338_0 := h7338c.1
                  have p7338_1 := h7338c.2.1
                  have p7338_2 := h7338c.2.2.1
                  have p7338_3 := h7338c.2.2.2
                  linarith only [hlam, p7338_0]
                · have p7338_0 := h7338c.1
                  have p7338_1 := h7338c.2.1
                  have p7338_2 := h7338c.2.2.1
                  have p7338_3 := h7338c.2.2.2
                  linarith only [h7239, h7245, h7246, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7338_1]
                · have p7338_0 := h7338c.1
                  have p7338_1 := h7338c.2.1
                  have p7338_2 := h7338c.2.2.1
                  have p7338_3 := h7338c.2.2.2
                  linarith only [h7240, h7242, h7246, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7338_1]
                · have p7338_0 := h7338c.1
                  have p7338_1 := h7338c.2.1
                  have p7338_2 := h7338c.2.2.1
                  have p7338_3 := h7338c.2.2.2
                  linarith only [h7242, h7246, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7338_1]
                · have p7338_0 := h7338c.1
                  have p7338_1 := h7338c.2.1
                  have p7338_2 := h7338c.2.2.1
                  have p7338_3 := h7338c.2.2.2
                  rcases p7338_3 (m.d 0 1) (by simp) with h7343 | h7343
                  · rcases p7338_3 (m.d 1 2) (by simp) with h7344 | h7344
                    · linarith only [h0, h7344, hlam]
                    · linarith only [h7239, h7344, hlam]
                  · linarith only [h7343, hlam, p7338_0]
                · have p7338_0 := h7338c.1
                  have p7338_1 := h7338c.2.1
                  have p7338_2 := h7338c.2.2.1
                  have p7338_3 := h7338c.2.2.2
                  linarith only [h0, hlam, p7338_0]
                · have p7338_0 := h7338c.1
                  have p7338_1 := h7338c.2.1
                  have p7338_2 := h7338c.2.2.1
                  have p7338_3 := h7338c.2.2.2
                  linarith only [hlam, p7338_0]
                · have p7338_0 := h7338c.1
                  have p7338_1 := h7338c.2.1
                  have p7338_2 := h7338c.2.2.1
                  have p7338_3 := h7338c.2.2.2
                  linarith only [h7235, hlam, p7338_0]
                · have p7338_0 := h7338c.1
                  have p7338_1 := h7338c.2.1
                  have p7338_2 := h7338c.2.2.1
                  have p7338_3 := h7338c.2.2.2
                  linarith only [h7237, hlam, p7338_0]
                · have p7338_0 := h7338c.1
                  have p7338_1 := h7338c.2.1
                  have p7338_2 := h7338c.2.2.1
                  have p7338_3 := h7338c.2.2.2
                  linarith only [h0, h6364, h7239, h7243, h7245, h7246, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7338_1]
                · have p7338_0 := h7338c.1
                  have p7338_1 := h7338c.2.1
                  have p7338_2 := h7338c.2.2.1
                  have p7338_3 := h7338c.2.2.2
                  linarith only [h1, hlam, p7338_0]
                · have p7338_0 := h7338c.1
                  have p7338_1 := h7338c.2.1
                  have p7338_2 := h7338c.2.2.1
                  have p7338_3 := h7338c.2.2.2
                  linarith only [h1, h7239, h7245, h7246, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7338_1]
                · have p7338_0 := h7338c.1
                  have p7338_1 := h7338c.2.1
                  have p7338_2 := h7338c.2.2.1
                  have p7338_3 := h7338c.2.2.2
                  linarith only [hlam, p7338_0]
                · have p7338_0 := h7338c.1
                  have p7338_1 := h7338c.2.1
                  have p7338_2 := h7338c.2.2.1
                  have p7338_3 := h7338c.2.2.2
                  linarith only [h1, h7237, h7239, h7245, h7246, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7338_1]
                · have p7338_0 := h7338c.1
                  have p7338_1 := h7338c.2.1
                  have p7338_2 := h7338c.2.2.1
                  have p7338_3 := h7338c.2.2.2
                  linarith only [h1, h7239, h7245, h7246, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7338_1]
                · have p7338_0 := h7338c.1
                  have p7338_1 := h7338c.2.1
                  have p7338_2 := h7338c.2.2.1
                  have p7338_3 := h7338c.2.2.2
                  linarith only [h2, hlam, p7338_0]
                · have p7338_0 := h7338c.1
                  have p7338_1 := h7338c.2.1
                  have p7338_2 := h7338c.2.2.1
                  have p7338_3 := h7338c.2.2.2
                  linarith only [h7239, h7245, h7246, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7338_1]
                · have p7338_0 := h7338c.1
                  have p7338_1 := h7338c.2.1
                  have p7338_2 := h7338c.2.2.1
                  have p7338_3 := h7338c.2.2.2
                  linarith only [h7240, hlam, p7338_0]
                · have p7338_0 := h7338c.1
                  have p7338_1 := h7338c.2.1
                  have p7338_2 := h7338c.2.2.1
                  have p7338_3 := h7338c.2.2.2
                  linarith only [hlam, p7338_0]
                · have p7338_0 := h7338c.1
                  have p7338_1 := h7338c.2.1
                  have p7338_2 := h7338c.2.2.1
                  have p7338_3 := h7338c.2.2.2
                  linarith only [h1, h7239, h7240, h7245, h7246, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7338_1]
                · have p7338_0 := h7338c.1
                  have p7338_1 := h7338c.2.1
                  have p7338_2 := h7338c.2.2.1
                  have p7338_3 := h7338c.2.2.2
                  linarith only [h3, hlam, p7338_0]
                · have p7338_0 := h7338c.1
                  have p7338_1 := h7338c.2.1
                  have p7338_2 := h7338c.2.2.1
                  have p7338_3 := h7338c.2.2.2
                  linarith only [h7239, hlam, p7338_1]
                · have p7338_0 := h7338c.1
                  have p7338_1 := h7338c.2.1
                  have p7338_2 := h7338c.2.2.1
                  have p7338_3 := h7338c.2.2.2
                  linarith only [h7241, hlam, p7338_0]
                · have p7338_0 := h7338c.1
                  have p7338_1 := h7338c.2.1
                  have p7338_2 := h7338c.2.2.1
                  have p7338_3 := h7338c.2.2.2
                  linarith only [h7242, hlam, p7338_0]
                · have p7338_0 := h7338c.1
                  have p7338_1 := h7338c.2.1
                  have p7338_2 := h7338c.2.2.1
                  have p7338_3 := h7338c.2.2.2
                  linarith only [hlam, p7338_0]
            · linarith only [h6364, h7234, h7245, hlam]
          · linarith only [h4, h7233, h7244, hlam]
        · linarith only [h4, h7232, h7243, hlam]
      · linarith only [h7237, h7239, h7242, hlam]
    · linarith only [h7235, h7239, h7241, hlam]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h7373 | h7373
    · rcases m.htr 1 4 5 (by decide) (by decide) with h7374 | h7374
      · rcases m.htr 2 3 4 (by decide) (by decide) with h7375 | h7375
        · rcases m.htr 2 3 5 (by decide) (by decide) with h7376 | h7376
          · rcases m.htr 2 4 5 (by decide) (by decide) with h7377 | h7377
            · rcases m.htr 3 4 5 (by decide) (by decide) with h7378 | h7378
              · rcases h1bigk with h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c | h7379c
                · have p7379_0 := h7379c.1
                  have p7379_1 := h7379c.2.1
                  have p7379_2 := h7379c.2.2.1
                  have p7379_3 := h7379c.2.2.2
                  linarith only [hlam, p7379_0]
                · have p7379_0 := h7379c.1
                  have p7379_1 := h7379c.2.1
                  have p7379_2 := h7379c.2.2.1
                  have p7379_3 := h7379c.2.2.2
                  rcases p7379_3 (m.d 0 1) (by simp) with h7381 | h7381
                  · rcases p7379_3 (m.d 1 2) (by simp) with h7382 | h7382
                    · linarith only [h7382, hlam, p7379_0]
                    · rcases p7379_3 (m.d 1 3) (by simp) with h7384 | h7384
                      · linarith only [h1, h7384, hlam]
                      · linarith only [h7235, h7384, hlam]
                  · linarith only [h7381, hlam, p7379_0]
                · have p7379_0 := h7379c.1
                  have p7379_1 := h7379c.2.1
                  have p7379_2 := h7379c.2.2.1
                  have p7379_3 := h7379c.2.2.2
                  rcases p7379_3 (m.d 0 1) (by simp) with h7388 | h7388
                  · rcases p7379_3 (m.d 1 2) (by simp) with h7389 | h7389
                    · linarith only [h0, h7389, hlam]
                    · rcases p7379_3 (m.d 1 3) (by simp) with h7391 | h7391
                      · linarith only [h7391, hlam, p7379_0]
                      · rcases p7379_3 (m.d 1 4) (by simp) with h7393 | h7393
                        · linarith only [h2, h7393, hlam]
                        · linarith only [h7240, h7393, hlam]
                  · linarith only [h7388, hlam, p7379_0]
                · have p7379_0 := h7379c.1
                  have p7379_1 := h7379c.2.1
                  have p7379_2 := h7379c.2.2.1
                  have p7379_3 := h7379c.2.2.2
                  rcases p7379_3 (m.d 0 1) (by simp) with h7397 | h7397
                  · rcases p7379_3 (m.d 1 2) (by simp) with h7398 | h7398
                    · linarith only [h0, h7398, hlam]
                    · rcases p7379_3 (m.d 1 3) (by simp) with h7400 | h7400
                      · linarith only [h1, h7400, hlam]
                      · rcases p7379_3 (m.d 1 4) (by simp) with h7402 | h7402
                        · linarith only [h7402, hlam, p7379_0]
                        · rcases p7379_3 (m.d 1 5) (by simp) with h7404 | h7404
                          · linarith only [h3, h7404, hlam]
                          · rcases h3bigk with h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [hlam, p7406_0]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h4, h7235, hc12, hc23, hlam, hphi, p7406_1]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h4, hlam, p7406_1]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h4, h7235, h7240, hc12, hc23, hlam, hphi, p7406_1]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              rcases p7406_3 (m.d 0 3) (by simp) with h7411 | h7411
                              · rcases p7406_3 (m.d 1 3) (by simp) with h7412 | h7412
                                · linarith only [h1, h7412, hlam]
                                · linarith only [h7373, h7412, hlam]
                              · linarith only [h7411, hlam, p7406_0]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h1, hlam, p7406_0]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [hlam, p7406_0]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h7235, hlam, p7406_1]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h7240, hlam, p7406_0]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h7240, h7378, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7406_1]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h0, h4, h7239, h7376, h7378, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7406_1]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h7235, h7239, h7376, h7378, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7406_1]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [hlam, p7406_0]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h7235, h7239, h7240, h7376, h7378, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7406_1]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              rcases p7406_3 (m.d 0 3) (by simp) with h7425 | h7425
                              · linarith only [h4, h7425, hlam]
                              · linarith only [h7233, h7425, hlam]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h7232, hlam, p7406_0]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h7232, h7235, h7239, h7376, h7378, hc03, hc45, hlam, hphi, ht0b, ht5b, p7406_1]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h7375, hlam, p7406_0]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [hlam, p7406_0]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h4, h7232, h7378, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7406_1]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h7233, hlam, p7406_0]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h7373, hlam, p7406_0]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h7376, hlam, p7406_0]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [h7378, hlam, p7406_0]
                            · have p7406_0 := h7406c.1
                              have p7406_1 := h7406c.2.1
                              have p7406_2 := h7406c.2.2.1
                              have p7406_3 := h7406c.2.2.2
                              linarith only [hlam, p7406_0]
                  · linarith only [h7397, hlam, p7379_0]
                · have p7379_0 := h7379c.1
                  have p7379_1 := h7379c.2.1
                  have p7379_2 := h7379c.2.2.1
                  have p7379_3 := h7379c.2.2.2
                  rcases p7379_3 (m.d 0 1) (by simp) with h7439 | h7439
                  · rcases p7379_3 (m.d 1 2) (by simp) with h7440 | h7440
                    · linarith only [h0, h7440, hlam]
                    · linarith only [h7239, h7440, hlam]
                  · linarith only [h7439, hlam, p7379_0]
                · have p7379_0 := h7379c.1
                  have p7379_1 := h7379c.2.1
                  have p7379_2 := h7379c.2.2.1
                  have p7379_3 := h7379c.2.2.2
                  linarith only [h0, hlam, p7379_0]
                · have p7379_0 := h7379c.1
                  have p7379_1 := h7379c.2.1
                  have p7379_2 := h7379c.2.2.1
                  have p7379_3 := h7379c.2.2.2
                  linarith only [hlam, p7379_0]
                · have p7379_0 := h7379c.1
                  have p7379_1 := h7379c.2.1
                  have p7379_2 := h7379c.2.2.1
                  have p7379_3 := h7379c.2.2.2
                  linarith only [h7235, hlam, p7379_0]
                · have p7379_0 := h7379c.1
                  have p7379_1 := h7379c.2.1
                  have p7379_2 := h7379c.2.2.1
                  have p7379_3 := h7379c.2.2.2
                  linarith only [h7237, hlam, p7379_0]
                · have p7379_0 := h7379c.1
                  have p7379_1 := h7379c.2.1
                  have p7379_2 := h7379c.2.2.1
                  have p7379_3 := h7379c.2.2.2
                  linarith only [h4, h7232, h7235, h7239, h7240, h7376, h7378, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7379_1]
                · have p7379_0 := h7379c.1
                  have p7379_1 := h7379c.2.1
                  have p7379_2 := h7379c.2.2.1
                  have p7379_3 := h7379c.2.2.2
                  linarith only [h1, hlam, p7379_0]
                · have p7379_0 := h7379c.1
                  have p7379_1 := h7379c.2.1
                  have p7379_2 := h7379c.2.2.1
                  have p7379_3 := h7379c.2.2.2
                  linarith only [h1, h7239, h7376, h7378, hc01, hc45, hlam, hphi, ht0b, ht5b, p7379_1]
                · have p7379_0 := h7379c.1
                  have p7379_1 := h7379c.2.1
                  have p7379_2 := h7379c.2.2.1
                  have p7379_3 := h7379c.2.2.2
                  linarith only [hlam, p7379_0]
                · have p7379_0 := h7379c.1
                  have p7379_1 := h7379c.2.1
                  have p7379_2 := h7379c.2.2.1
                  have p7379_3 := h7379c.2.2.2
                  linarith only [h7240, hlam, p7379_1]
                · have p7379_0 := h7379c.1
                  have p7379_1 := h7379c.2.1
                  have p7379_2 := h7379c.2.2.1
                  have p7379_3 := h7379c.2.2.2
                  linarith only [h4, h7232, h7239, h7240, h7376, h7378, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7379_1]
                · have p7379_0 := h7379c.1
                  have p7379_1 := h7379c.2.1
                  have p7379_2 := h7379c.2.2.1
                  have p7379_3 := h7379c.2.2.2
                  linarith only [h2, hlam, p7379_0]
                · have p7379_0 := h7379c.1
                  have p7379_1 := h7379c.2.1
                  have p7379_2 := h7379c.2.2.1
                  have p7379_3 := h7379c.2.2.2
                  linarith only [h2, h7239, h7376, h7378, hc01, hc45, hlam, hphi, ht0b, ht5b, p7379_1]
                · have p7379_0 := h7379c.1
                  have p7379_1 := h7379c.2.1
                  have p7379_2 := h7379c.2.2.1
                  have p7379_3 := h7379c.2.2.2
                  linarith only [h4, h7232, h7235, h7239, h7240, h7376, h7378, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7379_1]
                · have p7379_0 := h7379c.1
                  have p7379_1 := h7379c.2.1
                  have p7379_2 := h7379c.2.2.1
                  have p7379_3 := h7379c.2.2.2
                  linarith only [hlam, p7379_0]
                · have p7379_0 := h7379c.1
                  have p7379_1 := h7379c.2.1
                  have p7379_2 := h7379c.2.2.1
                  have p7379_3 := h7379c.2.2.2
                  rcases p7379_3 (m.d 0 1) (by simp) with h7458 | h7458
                  · rcases p7379_3 (m.d 1 2) (by simp) with h7459 | h7459
                    · linarith only [h7237, h7459, hlam]
                    · linarith only [h7239, h7459, hlam]
                  · linarith only [h3, h7458, hlam]
                · have p7379_0 := h7379c.1
                  have p7379_1 := h7379c.2.1
                  have p7379_2 := h7379c.2.2.1
                  have p7379_3 := h7379c.2.2.2
                  linarith only [h3, hlam, p7379_0]
                · have p7379_0 := h7379c.1
                  have p7379_1 := h7379c.2.1
                  have p7379_2 := h7379c.2.2.1
                  have p7379_3 := h7379c.2.2.2
                  linarith only [h7239, hlam, p7379_1]
                · have p7379_0 := h7379c.1
                  have p7379_1 := h7379c.2.1
                  have p7379_2 := h7379c.2.2.1
                  have p7379_3 := h7379c.2.2.2
                  linarith only [h7373, hlam, p7379_0]
                · have p7379_0 := h7379c.1
                  have p7379_1 := h7379c.2.1
                  have p7379_2 := h7379c.2.2.1
                  have p7379_3 := h7379c.2.2.2
                  linarith only [h7374, hlam, p7379_0]
                · have p7379_0 := h7379c.1
                  have p7379_1 := h7379c.2.1
                  have p7379_2 := h7379c.2.2.1
                  have p7379_3 := h7379c.2.2.2
                  linarith only [hlam, p7379_0]
              · linarith only [h7234, h7235, h7239, h7240, h7376, h7378, hc04, hc35, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h6364, h7239, h7374, h7377, hlam]
          · linarith only [h4, h7232, h7235, h7239, h7240, h7376, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
        · linarith only [h4, h7232, h7375, hlam]
      · linarith only [h7235, h7239, h7240, h7374, hlam]
    · linarith only [h7235, h7239, h7373, hlam]

end R2N4
