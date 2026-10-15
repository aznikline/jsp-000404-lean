import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_33S3
import Jsp000404.R1LeavesN7_33S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8870000 in
theorem r1l7_11_13_25_L_I_L_R_H_I (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_13_25_L_I_L_R_H_I_x0 m hb1 hb3 hb5 h0
  · exact r1l7_11_13_25_L_I_L_R_H_I_x1 m hb1 hb3 hb5 h0

set_option maxHeartbeats 8858000 in
set_option maxHeartbeats 8858000 in
theorem r1l7_22_13_15_M_LI_L_I_L_I_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
  · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
    · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
      · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
        · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
          · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
            · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
              · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                        · linarith only [h0, h15, h18, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                        · linarith only [h0, h15, h17, h18, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h21 | h21
                        · linarith only [h17, h21, h3, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · rcases h2bigk with h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c
                          · have p23_0 := h23c.1
                            have p23_1 := h23c.2.1
                            have p23_2 := h23c.2.2.1
                            have p23_3 := h23c.2.2.2
                            linarith only [hlam, p23_0]
                          · have p23_0 := h23c.1
                            have p23_1 := h23c.2.1
                            have p23_2 := h23c.2.2.1
                            have p23_3 := h23c.2.2.2
                            linarith only [hc12, hlam, hphi, p23_1, u2elo0]
                          · have p23_0 := h23c.1
                            have p23_1 := h23c.2.1
                            have p23_2 := h23c.2.2.1
                            have p23_3 := h23c.2.2.2
                            linarith only [h16, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p23_1, u2elo0]
                          · have p23_0 := h23c.1
                            have p23_1 := h23c.2.1
                            have p23_2 := h23c.2.2.1
                            have p23_3 := h23c.2.2.2
                            rcases p23_3 (m.d 0 2) (by simp) with h27 | h27
                            · rcases p23_3 (m.d 1 2) (by simp) with h28 | h28
                              · linarith only [h0, h28, hlam]
                              · linarith only [h10, h28, hlam]
                            · linarith only [h27, hlam, p23_0]
                          · have p23_0 := h23c.1
                            have p23_1 := h23c.2.1
                            have p23_2 := h23c.2.2.1
                            have p23_3 := h23c.2.2.2
                            rcases p23_3 (m.d 0 2) (by simp) with h32 | h32
                            · rcases p23_3 (m.d 1 2) (by simp) with h33 | h33
                              · linarith only [h0, h33, hlam]
                              · linarith only [h11, h33, hlam]
                            · linarith only [h32, hlam, p23_0]
                          · have p23_0 := h23c.1
                            have p23_1 := h23c.2.1
                            have p23_2 := h23c.2.2.1
                            have p23_3 := h23c.2.2.2
                            linarith only [h0, hlam, p23_1]
                          · have p23_0 := h23c.1
                            have p23_1 := h23c.2.1
                            have p23_2 := h23c.2.2.1
                            have p23_3 := h23c.2.2.2
                            linarith only [hlam, p23_0]
                          · have p23_0 := h23c.1
                            have p23_1 := h23c.2.1
                            have p23_2 := h23c.2.2.1
                            have p23_3 := h23c.2.2.2
                            linarith only [h16, h21, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p23_1, u2elo1]
                          · have p23_0 := h23c.1
                            have p23_1 := h23c.2.1
                            have p23_2 := h23c.2.2.1
                            have p23_3 := h23c.2.2.2
                            rcases p23_3 (m.d 0 2) (by simp) with h40 | h40
                            · rcases p23_3 (m.d 1 2) (by simp) with h41 | h41
                              · rcases p23_3 (m.d 2 3) (by simp) with h42 | h42
                                · linarith only [h42, h9, hlam]
                                · linarith only [h15, h42, hlam]
                              · linarith only [h41, hlam, p23_0]
                            · linarith only [h4, h40, hlam]
                          · have p23_0 := h23c.1
                            have p23_1 := h23c.2.1
                            have p23_2 := h23c.2.2.1
                            have p23_3 := h23c.2.2.2
                            rcases p23_3 (m.d 0 2) (by simp) with h47 | h47
                            · rcases p23_3 (m.d 1 2) (by simp) with h48 | h48
                              · rcases p23_3 (m.d 2 3) (by simp) with h49 | h49
                                · linarith only [h49, h9, hlam]
                                · linarith only [h16, h49, hlam]
                              · linarith only [h48, hlam, p23_0]
                            · linarith only [h47, h5, hlam]
                          · have p23_0 := h23c.1
                            have p23_1 := h23c.2.1
                            have p23_2 := h23c.2.2.1
                            have p23_3 := h23c.2.2.2
                            linarith only [h3, hlam, p23_0]
                          · have p23_0 := h23c.1
                            have p23_1 := h23c.2.1
                            have p23_2 := h23c.2.2.1
                            have p23_3 := h23c.2.2.2
                            linarith only [h9, hlam, p23_0]
                          · have p23_0 := h23c.1
                            have p23_1 := h23c.2.1
                            have p23_2 := h23c.2.2.1
                            have p23_3 := h23c.2.2.2
                            linarith only [hlam, p23_0]
                          · have p23_0 := h23c.1
                            have p23_1 := h23c.2.1
                            have p23_2 := h23c.2.2.1
                            have p23_3 := h23c.2.2.2
                            linarith only [h15, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p23_1, u2elo0]
                          · have p23_0 := h23c.1
                            have p23_1 := h23c.2.1
                            have p23_2 := h23c.2.2.1
                            have p23_3 := h23c.2.2.2
                            linarith only [h0, h9, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p23_1, u2elo0]
                          · have p23_0 := h23c.1
                            have p23_1 := h23c.2.1
                            have p23_2 := h23c.2.2.1
                            have p23_3 := h23c.2.2.2
                            linarith only [h4, hlam, p23_0]
                          · have p23_0 := h23c.1
                            have p23_1 := h23c.2.1
                            have p23_2 := h23c.2.2.1
                            have p23_3 := h23c.2.2.2
                            linarith only [h10, hlam, p23_0]
                          · have p23_0 := h23c.1
                            have p23_1 := h23c.2.1
                            have p23_2 := h23c.2.2.1
                            have p23_3 := h23c.2.2.2
                            linarith only [h15, hlam, p23_0]
                          · have p23_0 := h23c.1
                            have p23_1 := h23c.2.1
                            have p23_2 := h23c.2.2.1
                            have p23_3 := h23c.2.2.2
                            linarith only [hlam, p23_0]
                          · have p23_0 := h23c.1
                            have p23_1 := h23c.2.1
                            have p23_2 := h23c.2.2.1
                            have p23_3 := h23c.2.2.2
                            linarith only [h17, hlam, p23_0]
                          · have p23_0 := h23c.1
                            have p23_1 := h23c.2.1
                            have p23_2 := h23c.2.2.1
                            have p23_3 := h23c.2.2.2
                            linarith only [h5, hlam, p23_0]
                          · have p23_0 := h23c.1
                            have p23_1 := h23c.2.1
                            have p23_2 := h23c.2.2.1
                            have p23_3 := h23c.2.2.2
                            linarith only [h11, hlam, p23_0]
                          · have p23_0 := h23c.1
                            have p23_1 := h23c.2.1
                            have p23_2 := h23c.2.2.1
                            have p23_3 := h23c.2.2.2
                            linarith only [h16, hlam, p23_0]
                          · have p23_0 := h23c.1
                            have p23_1 := h23c.2.1
                            have p23_2 := h23c.2.2.1
                            have p23_3 := h23c.2.2.2
                            linarith only [h15, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p23_1, u2elo0]
                          · have p23_0 := h23c.1
                            have p23_1 := h23c.2.1
                            have p23_2 := h23c.2.2.1
                            have p23_3 := h23c.2.2.2
                            linarith only [hlam, p23_0]
                    · linarith only [h1, h13, h15, h16, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h70 | h70
                    · linarith only [h15, h3, h6, h70, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h72 | h72
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h73 | h73
                        · rcases h2bigk with h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c | h74c
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [hc12, hlam, hphi, p74_1, u2elo0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            rcases p74_3 (m.d 0 2) (by simp) with h77 | h77
                            · rcases p74_3 (m.d 1 2) (by simp) with h78 | h78
                              · linarith only [h0, h78, hlam]
                              · linarith only [h78, h9, hlam]
                            · linarith only [h77, hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h72, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p74_1, u2elo0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            rcases p74_3 (m.d 0 2) (by simp) with h83 | h83
                            · rcases p74_3 (m.d 1 2) (by simp) with h84 | h84
                              · linarith only [h0, h84, hlam]
                              · linarith only [h11, h84, hlam]
                            · linarith only [h83, hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h0, hlam, p74_1]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            rcases p74_3 (m.d 0 2) (by simp) with h90 | h90
                            · rcases p74_3 (m.d 1 2) (by simp) with h91 | h91
                              · rcases p74_3 (m.d 2 3) (by simp) with h92 | h92
                                · linarith only [h92, hlam, p74_0]
                                · rcases p74_3 (m.d 2 4) (by simp) with h94 | h94
                                  · linarith only [h10, h94, hlam]
                                  · linarith only [h15, h94, hlam]
                              · linarith only [h91, hlam, p74_0]
                            · linarith only [h3, h90, hlam]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h72, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p74_1, u2elo1]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            rcases p74_3 (m.d 0 2) (by simp) with h100 | h100
                            · rcases p74_3 (m.d 1 2) (by simp) with h101 | h101
                              · rcases p74_3 (m.d 2 3) (by simp) with h102 | h102
                                · linarith only [h102, h9, hlam]
                                · rcases p74_3 (m.d 2 4) (by simp) with h104 | h104
                                  · linarith only [h10, h104, hlam]
                                  · linarith only [h104, h72, hlam]
                              · linarith only [h101, hlam, p74_0]
                            · linarith only [h100, h5, hlam]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h3, hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h9, hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h15, hlam, p74_1]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h70, hlam, p74_1]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h4, hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h10, hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p74_1, u2elo0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h1, h12, h15, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p74_1, u2elo0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h5, hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h11, hlam, p74_0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p74_1, u2elo0]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [h72, hlam, p74_1]
                          · have p74_0 := h74c.1
                            have p74_1 := h74c.2.1
                            have p74_2 := h74c.2.2.1
                            have p74_3 := h74c.2.2.2
                            linarith only [hlam, p74_0]
                        · linarith only [h1, h12, h14, h15, h3, h73, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h125 | h125
                        · linarith only [h1, h12, h125, h3, h72, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · linarith only [h1, h12, h125, h14, h15, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h128 | h128
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h129 | h129
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h130 | h130
                      · linarith only [h130, h14, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h132 | h132
                        · linarith only [h10, h128, h132, h14, hlam]
                        · rcases h2bigk with h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c | h134c
                          · have p134_0 := h134c.1
                            have p134_1 := h134c.2.1
                            have p134_2 := h134c.2.2.1
                            have p134_3 := h134c.2.2.2
                            linarith only [hlam, p134_0]
                          · have p134_0 := h134c.1
                            have p134_1 := h134c.2.1
                            have p134_2 := h134c.2.2.1
                            have p134_3 := h134c.2.2.2
                            linarith only [hc12, hlam, hphi, p134_1, u2elo0]
                          · have p134_0 := h134c.1
                            have p134_1 := h134c.2.1
                            have p134_2 := h134c.2.2.1
                            have p134_3 := h134c.2.2.2
                            linarith only [h129, h132, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p134_1, u2elo0]
                          · have p134_0 := h134c.1
                            have p134_1 := h134c.2.1
                            have p134_2 := h134c.2.2.1
                            have p134_3 := h134c.2.2.2
                            rcases p134_3 (m.d 0 2) (by simp) with h138 | h138
                            · rcases p134_3 (m.d 1 2) (by simp) with h139 | h139
                              · linarith only [h0, h139, hlam]
                              · linarith only [h10, h139, hlam]
                            · linarith only [h138, hlam, p134_0]
                          · have p134_0 := h134c.1
                            have p134_1 := h134c.2.1
                            have p134_2 := h134c.2.2.1
                            have p134_3 := h134c.2.2.2
                            rcases p134_3 (m.d 0 2) (by simp) with h143 | h143
                            · rcases p134_3 (m.d 1 2) (by simp) with h144 | h144
                              · linarith only [h0, h144, hlam]
                              · linarith only [h11, h144, hlam]
                            · linarith only [h143, hlam, p134_0]
                          · have p134_0 := h134c.1
                            have p134_1 := h134c.2.1
                            have p134_2 := h134c.2.2.1
                            have p134_3 := h134c.2.2.2
                            linarith only [h0, hlam, p134_1]
                          · have p134_0 := h134c.1
                            have p134_1 := h134c.2.1
                            have p134_2 := h134c.2.2.1
                            have p134_3 := h134c.2.2.2
                            linarith only [hlam, p134_0]
                          · have p134_0 := h134c.1
                            have p134_1 := h134c.2.1
                            have p134_2 := h134c.2.2.1
                            have p134_3 := h134c.2.2.2
                            linarith only [h129, h132, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p134_1, u2elo1]
                          · have p134_0 := h134c.1
                            have p134_1 := h134c.2.1
                            have p134_2 := h134c.2.2.1
                            have p134_3 := h134c.2.2.2
                            rcases p134_3 (m.d 0 2) (by simp) with h151 | h151
                            · rcases p134_3 (m.d 1 2) (by simp) with h152 | h152
                              · rcases p134_3 (m.d 2 3) (by simp) with h153 | h153
                                · linarith only [h153, h9, hlam]
                                · linarith only [h128, h153, hlam]
                              · linarith only [h152, hlam, p134_0]
                            · linarith only [h151, h4, hlam]
                          · have p134_0 := h134c.1
                            have p134_1 := h134c.2.1
                            have p134_2 := h134c.2.2.1
                            have p134_3 := h134c.2.2.2
                            rcases p134_3 (m.d 0 2) (by simp) with h158 | h158
                            · rcases p134_3 (m.d 1 2) (by simp) with h159 | h159
                              · rcases p134_3 (m.d 2 3) (by simp) with h160 | h160
                                · linarith only [h160, h9, hlam]
                                · linarith only [h129, h160, hlam]
                              · linarith only [h159, hlam, p134_0]
                            · linarith only [h158, h5, hlam]
                          · have p134_0 := h134c.1
                            have p134_1 := h134c.2.1
                            have p134_2 := h134c.2.2.1
                            have p134_3 := h134c.2.2.2
                            linarith only [h3, hlam, p134_0]
                          · have p134_0 := h134c.1
                            have p134_1 := h134c.2.1
                            have p134_2 := h134c.2.2.1
                            have p134_3 := h134c.2.2.2
                            linarith only [h9, hlam, p134_0]
                          · have p134_0 := h134c.1
                            have p134_1 := h134c.2.1
                            have p134_2 := h134c.2.2.1
                            have p134_3 := h134c.2.2.2
                            linarith only [hlam, p134_0]
                          · have p134_0 := h134c.1
                            have p134_1 := h134c.2.1
                            have p134_2 := h134c.2.2.1
                            have p134_3 := h134c.2.2.2
                            linarith only [h128, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p134_1, u2elo0]
                          · have p134_0 := h134c.1
                            have p134_1 := h134c.2.1
                            have p134_2 := h134c.2.2.1
                            have p134_3 := h134c.2.2.2
                            linarith only [h0, h9, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p134_1, u2elo0]
                          · have p134_0 := h134c.1
                            have p134_1 := h134c.2.1
                            have p134_2 := h134c.2.2.1
                            have p134_3 := h134c.2.2.2
                            linarith only [h4, hlam, p134_0]
                          · have p134_0 := h134c.1
                            have p134_1 := h134c.2.1
                            have p134_2 := h134c.2.2.1
                            have p134_3 := h134c.2.2.2
                            linarith only [h10, hlam, p134_0]
                          · have p134_0 := h134c.1
                            have p134_1 := h134c.2.1
                            have p134_2 := h134c.2.2.1
                            have p134_3 := h134c.2.2.2
                            linarith only [h128, hlam, p134_0]
                          · have p134_0 := h134c.1
                            have p134_1 := h134c.2.1
                            have p134_2 := h134c.2.2.1
                            have p134_3 := h134c.2.2.2
                            linarith only [hlam, p134_0]
                          · have p134_0 := h134c.1
                            have p134_1 := h134c.2.1
                            have p134_2 := h134c.2.2.1
                            have p134_3 := h134c.2.2.2
                            linarith only [h130, hlam, p134_0]
                          · have p134_0 := h134c.1
                            have p134_1 := h134c.2.1
                            have p134_2 := h134c.2.2.1
                            have p134_3 := h134c.2.2.2
                            linarith only [h5, hlam, p134_0]
                          · have p134_0 := h134c.1
                            have p134_1 := h134c.2.1
                            have p134_2 := h134c.2.2.1
                            have p134_3 := h134c.2.2.2
                            linarith only [h11, hlam, p134_0]
                          · have p134_0 := h134c.1
                            have p134_1 := h134c.2.1
                            have p134_2 := h134c.2.2.1
                            have p134_3 := h134c.2.2.2
                            linarith only [h129, hlam, p134_0]
                          · have p134_0 := h134c.1
                            have p134_1 := h134c.2.1
                            have p134_2 := h134c.2.2.1
                            have p134_3 := h134c.2.2.2
                            linarith only [h128, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p134_1, u2elo0]
                          · have p134_0 := h134c.1
                            have p134_1 := h134c.2.1
                            have p134_2 := h134c.2.2.1
                            have p134_3 := h134c.2.2.2
                            linarith only [hlam, p134_0]
                    · linarith only [h128, h129, h3, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                  · linarith only [h12, h128, h14, h3, h6, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
              · linarith only [h12, h13, h3, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h183 | h183
              · linarith only [h12, h183, h3, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h185 | h185
                · rcases m.htr 2 3 4 (by decide) (by decide) with h186 | h186
                  · linarith only [h12, h186, h3, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h188 | h188
                    · linarith only [h12, h183, h188, h3, h6, h9, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h190 | h190
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h191 | h191
                        · rcases h2bigk with h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c | h192c
                          · have p192_0 := h192c.1
                            have p192_1 := h192c.2.1
                            have p192_2 := h192c.2.2.1
                            have p192_3 := h192c.2.2.2
                            linarith only [hlam, p192_0]
                          · have p192_0 := h192c.1
                            have p192_1 := h192c.2.1
                            have p192_2 := h192c.2.2.1
                            have p192_3 := h192c.2.2.2
                            linarith only [hc12, hlam, hphi, p192_1, u2elo0]
                          · have p192_0 := h192c.1
                            have p192_1 := h192c.2.1
                            have p192_2 := h192c.2.2.1
                            have p192_3 := h192c.2.2.2
                            rcases p192_3 (m.d 0 2) (by simp) with h195 | h195
                            · rcases p192_3 (m.d 1 2) (by simp) with h196 | h196
                              · linarith only [h0, h196, hlam]
                              · linarith only [h196, h9, hlam]
                            · linarith only [h195, hlam, p192_0]
                          · have p192_0 := h192c.1
                            have p192_1 := h192c.2.1
                            have p192_2 := h192c.2.2.1
                            have p192_3 := h192c.2.2.2
                            linarith only [h190, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p192_1, u2elo0]
                          · have p192_0 := h192c.1
                            have p192_1 := h192c.2.1
                            have p192_2 := h192c.2.2.1
                            have p192_3 := h192c.2.2.2
                            rcases p192_3 (m.d 0 2) (by simp) with h201 | h201
                            · rcases p192_3 (m.d 1 2) (by simp) with h202 | h202
                              · linarith only [h0, h202, hlam]
                              · linarith only [h11, h202, hlam]
                            · linarith only [h201, hlam, p192_0]
                          · have p192_0 := h192c.1
                            have p192_1 := h192c.2.1
                            have p192_2 := h192c.2.2.1
                            have p192_3 := h192c.2.2.2
                            linarith only [h0, hlam, p192_1]
                          · have p192_0 := h192c.1
                            have p192_1 := h192c.2.1
                            have p192_2 := h192c.2.2.1
                            have p192_3 := h192c.2.2.2
                            linarith only [hlam, p192_0]
                          · have p192_0 := h192c.1
                            have p192_1 := h192c.2.1
                            have p192_2 := h192c.2.2.1
                            have p192_3 := h192c.2.2.2
                            rcases p192_3 (m.d 0 2) (by simp) with h208 | h208
                            · rcases p192_3 (m.d 1 2) (by simp) with h209 | h209
                              · rcases p192_3 (m.d 2 3) (by simp) with h210 | h210
                                · linarith only [h210, hlam, p192_0]
                                · rcases p192_3 (m.d 2 4) (by simp) with h212 | h212
                                  · linarith only [h10, h212, hlam]
                                  · linarith only [h186, h212, hlam]
                              · linarith only [h209, hlam, p192_0]
                            · linarith only [h208, h3, hlam]
                          · have p192_0 := h192c.1
                            have p192_1 := h192c.2.1
                            have p192_2 := h192c.2.2.1
                            have p192_3 := h192c.2.2.2
                            linarith only [h190, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p192_1, u2elo1]
                          · have p192_0 := h192c.1
                            have p192_1 := h192c.2.1
                            have p192_2 := h192c.2.2.1
                            have p192_3 := h192c.2.2.2
                            rcases p192_3 (m.d 0 2) (by simp) with h218 | h218
                            · rcases p192_3 (m.d 1 2) (by simp) with h219 | h219
                              · rcases p192_3 (m.d 2 3) (by simp) with h220 | h220
                                · linarith only [h220, h9, hlam]
                                · rcases p192_3 (m.d 2 4) (by simp) with h222 | h222
                                  · linarith only [h10, h222, hlam]
                                  · linarith only [h190, h222, hlam]
                              · linarith only [h219, hlam, p192_0]
                            · linarith only [h218, h5, hlam]
                          · have p192_0 := h192c.1
                            have p192_1 := h192c.2.1
                            have p192_2 := h192c.2.2.1
                            have p192_3 := h192c.2.2.2
                            linarith only [h3, hlam, p192_0]
                          · have p192_0 := h192c.1
                            have p192_1 := h192c.2.1
                            have p192_2 := h192c.2.2.1
                            have p192_3 := h192c.2.2.2
                            linarith only [h9, hlam, p192_0]
                          · have p192_0 := h192c.1
                            have p192_1 := h192c.2.1
                            have p192_2 := h192c.2.2.1
                            have p192_3 := h192c.2.2.2
                            linarith only [hlam, p192_0]
                          · have p192_0 := h192c.1
                            have p192_1 := h192c.2.1
                            have p192_2 := h192c.2.2.1
                            have p192_3 := h192c.2.2.2
                            linarith only [h186, hlam, p192_1]
                          · have p192_0 := h192c.1
                            have p192_1 := h192c.2.1
                            have p192_2 := h192c.2.2.1
                            have p192_3 := h192c.2.2.2
                            linarith only [h188, hlam, p192_1]
                          · have p192_0 := h192c.1
                            have p192_1 := h192c.2.1
                            have p192_2 := h192c.2.2.1
                            have p192_3 := h192c.2.2.2
                            linarith only [h4, hlam, p192_0]
                          · have p192_0 := h192c.1
                            have p192_1 := h192c.2.1
                            have p192_2 := h192c.2.2.1
                            have p192_3 := h192c.2.2.2
                            linarith only [h10, hlam, p192_0]
                          · have p192_0 := h192c.1
                            have p192_1 := h192c.2.1
                            have p192_2 := h192c.2.2.1
                            have p192_3 := h192c.2.2.2
                            linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p192_1, u2elo0]
                          · have p192_0 := h192c.1
                            have p192_1 := h192c.2.1
                            have p192_2 := h192c.2.2.1
                            have p192_3 := h192c.2.2.2
                            linarith only [hlam, p192_0]
                          · have p192_0 := h192c.1
                            have p192_1 := h192c.2.1
                            have p192_2 := h192c.2.2.1
                            have p192_3 := h192c.2.2.2
                            linarith only [h10, h12, h3, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p192_1, u2elo0]
                          · have p192_0 := h192c.1
                            have p192_1 := h192c.2.1
                            have p192_2 := h192c.2.2.1
                            have p192_3 := h192c.2.2.2
                            linarith only [h5, hlam, p192_0]
                          · have p192_0 := h192c.1
                            have p192_1 := h192c.2.1
                            have p192_2 := h192c.2.2.1
                            have p192_3 := h192c.2.2.2
                            linarith only [h11, hlam, p192_0]
                          · have p192_0 := h192c.1
                            have p192_1 := h192c.2.1
                            have p192_2 := h192c.2.2.1
                            have p192_3 := h192c.2.2.2
                            linarith only [h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p192_1, u2elo0]
                          · have p192_0 := h192c.1
                            have p192_1 := h192c.2.1
                            have p192_2 := h192c.2.2.1
                            have p192_3 := h192c.2.2.2
                            linarith only [h190, hlam, p192_1]
                          · have p192_0 := h192c.1
                            have p192_1 := h192c.2.1
                            have p192_2 := h192c.2.2.1
                            have p192_3 := h192c.2.2.2
                            linarith only [hlam, p192_0]
                        · linarith only [h12, h191, h3, h6, h8, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · linarith only [h12, h185, h190, h3, h6, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h244 | h244
                  · linarith only [h183, h244, h3, h7, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h246 | h246
                    · linarith only [h12, h185, h246, h3, h6, h8, h9, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h248 | h248
                      · linarith only [h12, h185, h248, h4, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h250 | h250
                        · linarith only [h12, h185, h250, h3, h6, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                        · linarith only [h12, h250, h4, h8, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
          · linarith only [h11, h5, hc12, hlam, hphi, u2elo0]
        · linarith only [h10, h4, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
      · linarith only [h3, h9, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h256 | h256
      · rcases m.htr 1 2 4 (by decide) (by decide) with h257 | h257
        · rcases m.htr 1 2 5 (by decide) (by decide) with h258 | h258
          · rcases m.htr 1 3 4 (by decide) (by decide) with h259 | h259
            · rcases m.htr 1 3 5 (by decide) (by decide) with h260 | h260
              · rcases m.htr 1 4 5 (by decide) (by decide) with h261 | h261
                · linarith only [h2, h261, h8, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h263 | h263
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h264 | h264
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h265 | h265
                      · linarith only [h265, h4, h8, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h267 | h267
                        · linarith only [h263, h267, h4, h8, hlam]
                        · rcases h2bigk with h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c | h269c
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [hlam, p269_0]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h256, h264, h267, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p269_1, u2elo0]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h264, h267, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p269_1, u2elo0]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            rcases p269_3 (m.d 0 2) (by simp) with h273 | h273
                            · rcases p269_3 (m.d 1 2) (by simp) with h274 | h274
                              · linarith only [h0, h274, hlam]
                              · linarith only [h257, h274, hlam]
                            · linarith only [h273, hlam, p269_0]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            rcases p269_3 (m.d 0 2) (by simp) with h278 | h278
                            · rcases p269_3 (m.d 1 2) (by simp) with h279 | h279
                              · linarith only [h0, h279, hlam]
                              · linarith only [h258, h279, hlam]
                            · linarith only [h278, hlam, p269_0]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h0, hlam, p269_1]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [hlam, p269_0]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h264, h267, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p269_1, u2elo1]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            rcases p269_3 (m.d 0 2) (by simp) with h286 | h286
                            · rcases p269_3 (m.d 1 2) (by simp) with h287 | h287
                              · rcases p269_3 (m.d 2 3) (by simp) with h288 | h288
                                · linarith only [h256, h288, hlam]
                                · linarith only [h263, h288, hlam]
                              · linarith only [h287, hlam, p269_0]
                            · linarith only [h286, h4, hlam]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            rcases p269_3 (m.d 0 2) (by simp) with h293 | h293
                            · rcases p269_3 (m.d 1 2) (by simp) with h294 | h294
                              · rcases p269_3 (m.d 2 3) (by simp) with h295 | h295
                                · linarith only [h256, h295, hlam]
                                · linarith only [h264, h295, hlam]
                              · linarith only [h294, hlam, p269_0]
                            · linarith only [h293, h5, hlam]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h3, hlam, p269_0]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h256, hlam, p269_0]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [hlam, p269_0]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h263, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p269_1, u2elo0]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h0, h256, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p269_1, u2elo0]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h4, hlam, p269_0]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h257, hlam, p269_0]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h263, hlam, p269_0]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [hlam, p269_0]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h265, hlam, p269_0]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h5, hlam, p269_0]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h258, hlam, p269_0]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h264, hlam, p269_0]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [h263, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p269_1, u2elo0]
                          · have p269_0 := h269c.1
                            have p269_1 := h269c.2.1
                            have p269_2 := h269c.2.2.1
                            have p269_3 := h269c.2.2.2
                            linarith only [hlam, p269_0]
                    · linarith only [h1, h260, h263, h264, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h316 | h316
                    · linarith only [h263, h3, h316, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h318 | h318
                      · linarith only [h263, h318, h6, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h320 | h320
                        · linarith only [h320, h6, h8, hlam]
                        · rcases h2bigk with h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c
                          · have p322_0 := h322c.1
                            have p322_1 := h322c.2.1
                            have p322_2 := h322c.2.2.1
                            have p322_3 := h322c.2.2.2
                            linarith only [hlam, p322_0]
                          · have p322_0 := h322c.1
                            have p322_1 := h322c.2.1
                            have p322_2 := h322c.2.2.1
                            have p322_3 := h322c.2.2.2
                            linarith only [hc12, hlam, hphi, p322_1, u2elo0]
                          · have p322_0 := h322c.1
                            have p322_1 := h322c.2.1
                            have p322_2 := h322c.2.2.1
                            have p322_3 := h322c.2.2.2
                            rcases p322_3 (m.d 0 2) (by simp) with h325 | h325
                            · rcases p322_3 (m.d 1 2) (by simp) with h326 | h326
                              · linarith only [h0, h326, hlam]
                              · linarith only [h256, h326, hlam]
                            · linarith only [h325, hlam, p322_0]
                          · have p322_0 := h322c.1
                            have p322_1 := h322c.2.1
                            have p322_2 := h322c.2.2.1
                            have p322_3 := h322c.2.2.2
                            rcases p322_3 (m.d 0 2) (by simp) with h330 | h330
                            · rcases p322_3 (m.d 1 2) (by simp) with h331 | h331
                              · linarith only [h0, h331, hlam]
                              · linarith only [h257, h331, hlam]
                            · linarith only [h330, hlam, p322_0]
                          · have p322_0 := h322c.1
                            have p322_1 := h322c.2.1
                            have p322_2 := h322c.2.2.1
                            have p322_3 := h322c.2.2.2
                            rcases p322_3 (m.d 0 2) (by simp) with h335 | h335
                            · rcases p322_3 (m.d 1 2) (by simp) with h336 | h336
                              · linarith only [h0, h336, hlam]
                              · linarith only [h258, h336, hlam]
                            · linarith only [h335, hlam, p322_0]
                          · have p322_0 := h322c.1
                            have p322_1 := h322c.2.1
                            have p322_2 := h322c.2.2.1
                            have p322_3 := h322c.2.2.2
                            linarith only [h0, hlam, p322_1]
                          · have p322_0 := h322c.1
                            have p322_1 := h322c.2.1
                            have p322_2 := h322c.2.2.1
                            have p322_3 := h322c.2.2.2
                            linarith only [hlam, p322_0]
                          · have p322_0 := h322c.1
                            have p322_1 := h322c.2.1
                            have p322_2 := h322c.2.2.1
                            have p322_3 := h322c.2.2.2
                            rcases p322_3 (m.d 0 2) (by simp) with h342 | h342
                            · rcases p322_3 (m.d 1 2) (by simp) with h343 | h343
                              · rcases p322_3 (m.d 2 3) (by simp) with h344 | h344
                                · linarith only [h344, hlam, p322_0]
                                · rcases p322_3 (m.d 2 4) (by simp) with h346 | h346
                                  · linarith only [h257, h346, hlam]
                                  · linarith only [h263, h346, hlam]
                              · linarith only [h343, hlam, p322_0]
                            · linarith only [h3, h342, hlam]
                          · have p322_0 := h322c.1
                            have p322_1 := h322c.2.1
                            have p322_2 := h322c.2.2.1
                            have p322_3 := h322c.2.2.2
                            rcases p322_3 (m.d 0 2) (by simp) with h351 | h351
                            · rcases p322_3 (m.d 1 2) (by simp) with h352 | h352
                              · rcases p322_3 (m.d 2 3) (by simp) with h353 | h353
                                · linarith only [h256, h353, hlam]
                                · rcases p322_3 (m.d 2 4) (by simp) with h355 | h355
                                  · linarith only [h355, hlam, p322_0]
                                  · rcases p322_3 (m.d 2 5) (by simp) with h357 | h357
                                    · linarith only [h258, h357, hlam]
                                    · linarith only [h318, h357, hlam]
                              · linarith only [h352, hlam, p322_0]
                            · linarith only [h351, h4, hlam]
                          · have p322_0 := h322c.1
                            have p322_1 := h322c.2.1
                            have p322_2 := h322c.2.2.1
                            have p322_3 := h322c.2.2.2
                            rcases p322_3 (m.d 0 2) (by simp) with h362 | h362
                            · rcases p322_3 (m.d 1 2) (by simp) with h363 | h363
                              · rcases p322_3 (m.d 2 3) (by simp) with h364 | h364
                                · linarith only [h256, h364, hlam]
                                · rcases p322_3 (m.d 2 4) (by simp) with h366 | h366
                                  · linarith only [h257, h366, hlam]
                                  · rcases p322_3 (m.d 2 5) (by simp) with h368 | h368
                                    · linarith only [h368, hlam, p322_0]
                                    · rcases h3bigk with h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c | h370c
                                      · have p370_0 := h370c.1
                                        have p370_1 := h370c.2.1
                                        have p370_2 := h370c.2.2.1
                                        have p370_3 := h370c.2.2.2
                                        linarith only [hlam, p370_0]
                                      · have p370_0 := h370c.1
                                        have p370_1 := h370c.2.1
                                        have p370_2 := h370c.2.2.1
                                        have p370_3 := h370c.2.2.2
                                        linarith only [h260, h263, h3, h320, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p370_1, u2elo0]
                                      · have p370_0 := h370c.1
                                        have p370_1 := h370c.2.1
                                        have p370_2 := h370c.2.2.1
                                        have p370_3 := h370c.2.2.2
                                        rcases p370_3 (m.d 0 3) (by simp) with h373 | h373
                                        · rcases p370_3 (m.d 1 3) (by simp) with h374 | h374
                                          · linarith only [h1, h374, hlam]
                                          · linarith only [h256, h374, hlam]
                                        · linarith only [h3, h373, hlam]
                                      · have p370_0 := h370c.1
                                        have p370_1 := h370c.2.1
                                        have p370_2 := h370c.2.2.1
                                        have p370_3 := h370c.2.2.2
                                        linarith only [h263, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p370_1, u2elo0]
                                      · have p370_0 := h370c.1
                                        have p370_1 := h370c.2.1
                                        have p370_2 := h370c.2.2.1
                                        have p370_3 := h370c.2.2.2
                                        linarith only [h263, h3, h320, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p370_1, u2elo0]
                                      · have p370_0 := h370c.1
                                        have p370_1 := h370c.2.1
                                        have p370_2 := h370c.2.2.1
                                        have p370_3 := h370c.2.2.2
                                        linarith only [h1, hlam, p370_0]
                                      · have p370_0 := h370c.1
                                        have p370_1 := h370c.2.1
                                        have p370_2 := h370c.2.2.1
                                        have p370_3 := h370c.2.2.2
                                        linarith only [hlam, p370_0]
                                      · have p370_0 := h370c.1
                                        have p370_1 := h370c.2.1
                                        have p370_2 := h370c.2.2.1
                                        have p370_3 := h370c.2.2.2
                                        rcases p370_3 (m.d 0 3) (by simp) with h382 | h382
                                        · rcases p370_3 (m.d 1 3) (by simp) with h383 | h383
                                          · rcases p370_3 (m.d 2 3) (by simp) with h384 | h384
                                            · linarith only [h256, h384, hlam]
                                            · rcases p370_3 (m.d 3 4) (by simp) with h386 | h386
                                              · linarith only [h259, h386, hlam]
                                              · linarith only [h263, h386, hlam]
                                          · linarith only [h256, h383, hlam]
                                        · linarith only [h3, h382, hlam]
                                      · have p370_0 := h370c.1
                                        have p370_1 := h370c.2.1
                                        have p370_2 := h370c.2.2.1
                                        have p370_3 := h370c.2.2.2
                                        linarith only [h256, h263, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p370_1, u2elo1]
                                      · have p370_0 := h370c.1
                                        have p370_1 := h370c.2.1
                                        have p370_2 := h370c.2.2.1
                                        have p370_3 := h370c.2.2.2
                                        linarith only [h0, h256, h263, h320, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p370_1, u2elo0]
                                      · have p370_0 := h370c.1
                                        have p370_1 := h370c.2.1
                                        have p370_2 := h370c.2.2.1
                                        have p370_3 := h370c.2.2.2
                                        linarith only [h3, hlam, p370_1]
                                      · have p370_0 := h370c.1
                                        have p370_1 := h370c.2.1
                                        have p370_2 := h370c.2.2.1
                                        have p370_3 := h370c.2.2.2
                                        linarith only [h256, hlam, p370_1]
                                      · have p370_0 := h370c.1
                                        have p370_1 := h370c.2.1
                                        have p370_2 := h370c.2.2.1
                                        have p370_3 := h370c.2.2.2
                                        linarith only [hlam, p370_0]
                                      · have p370_0 := h370c.1
                                        have p370_1 := h370c.2.1
                                        have p370_2 := h370c.2.2.1
                                        have p370_3 := h370c.2.2.2
                                        linarith only [h263, hlam, p370_0]
                                      · have p370_0 := h370c.1
                                        have p370_1 := h370c.2.1
                                        have p370_2 := h370c.2.2.1
                                        have p370_3 := h370c.2.2.2
                                        linarith only [h316, hlam, p370_0]
                                      · have p370_0 := h370c.1
                                        have p370_1 := h370c.2.1
                                        have p370_2 := h370c.2.2.1
                                        have p370_3 := h370c.2.2.2
                                        linarith only [h6, hlam, p370_0]
                                      · have p370_0 := h370c.1
                                        have p370_1 := h370c.2.1
                                        have p370_2 := h370c.2.2.1
                                        have p370_3 := h370c.2.2.2
                                        linarith only [h259, hlam, p370_0]
                                      · have p370_0 := h370c.1
                                        have p370_1 := h370c.2.1
                                        have p370_2 := h370c.2.2.1
                                        have p370_3 := h370c.2.2.2
                                        linarith only [h6, h8, hc23, hc45, hlam, hphi, ht34, p370_1]
                                      · have p370_0 := h370c.1
                                        have p370_1 := h370c.2.1
                                        have p370_2 := h370c.2.2.1
                                        have p370_3 := h370c.2.2.2
                                        linarith only [hlam, p370_0]
                                      · have p370_0 := h370c.1
                                        have p370_1 := h370c.2.1
                                        have p370_2 := h370c.2.2.1
                                        have p370_3 := h370c.2.2.2
                                        linarith only [h320, hlam, p370_0]
                                      · have p370_0 := h370c.1
                                        have p370_1 := h370c.2.1
                                        have p370_2 := h370c.2.2.1
                                        have p370_3 := h370c.2.2.2
                                        linarith only [h7, hlam, p370_0]
                                      · have p370_0 := h370c.1
                                        have p370_1 := h370c.2.1
                                        have p370_2 := h370c.2.2.1
                                        have p370_3 := h370c.2.2.2
                                        linarith only [h260, hlam, p370_0]
                                      · have p370_0 := h370c.1
                                        have p370_1 := h370c.2.1
                                        have p370_2 := h370c.2.2.1
                                        have p370_3 := h370c.2.2.2
                                        linarith only [h0, h256, h260, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p370_1, u2elo0]
                                      · have p370_0 := h370c.1
                                        have p370_1 := h370c.2.1
                                        have p370_2 := h370c.2.2.1
                                        have p370_3 := h370c.2.2.2
                                        linarith only [h0, h256, h260, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p370_1, u2elo0]
                                      · have p370_0 := h370c.1
                                        have p370_1 := h370c.2.1
                                        have p370_2 := h370c.2.2.1
                                        have p370_3 := h370c.2.2.2
                                        linarith only [hlam, p370_0]
                              · linarith only [h363, hlam, p322_0]
                            · linarith only [h362, h5, hlam]
                          · have p322_0 := h322c.1
                            have p322_1 := h322c.2.1
                            have p322_2 := h322c.2.2.1
                            have p322_3 := h322c.2.2.2
                            linarith only [h3, hlam, p322_0]
                          · have p322_0 := h322c.1
                            have p322_1 := h322c.2.1
                            have p322_2 := h322c.2.2.1
                            have p322_3 := h322c.2.2.2
                            linarith only [h256, hlam, p322_0]
                          · have p322_0 := h322c.1
                            have p322_1 := h322c.2.1
                            have p322_2 := h322c.2.2.1
                            have p322_3 := h322c.2.2.2
                            linarith only [hlam, p322_0]
                          · have p322_0 := h322c.1
                            have p322_1 := h322c.2.1
                            have p322_2 := h322c.2.2.1
                            have p322_3 := h322c.2.2.2
                            linarith only [h263, hlam, p322_1]
                          · have p322_0 := h322c.1
                            have p322_1 := h322c.2.1
                            have p322_2 := h322c.2.2.1
                            have p322_3 := h322c.2.2.2
                            linarith only [h316, hlam, p322_1]
                          · have p322_0 := h322c.1
                            have p322_1 := h322c.2.1
                            have p322_2 := h322c.2.2.1
                            have p322_3 := h322c.2.2.2
                            linarith only [h4, hlam, p322_0]
                          · have p322_0 := h322c.1
                            have p322_1 := h322c.2.1
                            have p322_2 := h322c.2.2.1
                            have p322_3 := h322c.2.2.2
                            linarith only [h257, hlam, p322_0]
                          · have p322_0 := h322c.1
                            have p322_1 := h322c.2.1
                            have p322_2 := h322c.2.2.1
                            have p322_3 := h322c.2.2.2
                            linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p322_1, u2elo0]
                          · have p322_0 := h322c.1
                            have p322_1 := h322c.2.1
                            have p322_2 := h322c.2.2.1
                            have p322_3 := h322c.2.2.2
                            linarith only [hlam, p322_0]
                          · have p322_0 := h322c.1
                            have p322_1 := h322c.2.1
                            have p322_2 := h322c.2.2.1
                            have p322_3 := h322c.2.2.2
                            linarith only [h318, hlam, p322_0]
                          · have p322_0 := h322c.1
                            have p322_1 := h322c.2.1
                            have p322_2 := h322c.2.2.1
                            have p322_3 := h322c.2.2.2
                            linarith only [h5, hlam, p322_0]
                          · have p322_0 := h322c.1
                            have p322_1 := h322c.2.1
                            have p322_2 := h322c.2.2.1
                            have p322_3 := h322c.2.2.2
                            linarith only [h258, hlam, p322_0]
                          · have p322_0 := h322c.1
                            have p322_1 := h322c.2.1
                            have p322_2 := h322c.2.2.1
                            have p322_3 := h322c.2.2.2
                            linarith only [h0, h256, h260, h316, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p322_1, u2elo0]
                          · have p322_0 := h322c.1
                            have p322_1 := h322c.2.1
                            have p322_2 := h322c.2.2.1
                            have p322_3 := h322c.2.2.2
                            linarith only [h0, h256, h260, h316, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p322_1, u2elo0]
                          · have p322_0 := h322c.1
                            have p322_1 := h322c.2.1
                            have p322_2 := h322c.2.2.1
                            have p322_3 := h322c.2.2.2
                            linarith only [hlam, p322_0]
              · linarith only [h259, h260, h3, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h426 | h426
              · linarith only [h259, h3, h426, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h428 | h428
                · linarith only [h0, h257, h259, h428, h6, h8, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h430 | h430
                  · linarith only [h256, h259, h430, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h432 | h432
                    · linarith only [h256, h258, h259, h3, h426, h432, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h434 | h434
                      · linarith only [h4, h434, h8, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h436 | h436
                        · linarith only [h436, h6, h8, hlam]
                        · rcases h2bigk with h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c | h438c
                          · have p438_0 := h438c.1
                            have p438_1 := h438c.2.1
                            have p438_2 := h438c.2.2.1
                            have p438_3 := h438c.2.2.2
                            linarith only [hlam, p438_0]
                          · have p438_0 := h438c.1
                            have p438_1 := h438c.2.1
                            have p438_2 := h438c.2.2.1
                            have p438_3 := h438c.2.2.2
                            linarith only [hc12, hlam, hphi, p438_1, u2elo0]
                          · have p438_0 := h438c.1
                            have p438_1 := h438c.2.1
                            have p438_2 := h438c.2.2.1
                            have p438_3 := h438c.2.2.2
                            rcases p438_3 (m.d 0 2) (by simp) with h441 | h441
                            · rcases p438_3 (m.d 1 2) (by simp) with h442 | h442
                              · linarith only [h0, h442, hlam]
                              · linarith only [h256, h442, hlam]
                            · linarith only [h441, hlam, p438_0]
                          · have p438_0 := h438c.1
                            have p438_1 := h438c.2.1
                            have p438_2 := h438c.2.2.1
                            have p438_3 := h438c.2.2.2
                            rcases p438_3 (m.d 0 2) (by simp) with h446 | h446
                            · rcases p438_3 (m.d 1 2) (by simp) with h447 | h447
                              · linarith only [h0, h447, hlam]
                              · linarith only [h257, h447, hlam]
                            · linarith only [h446, hlam, p438_0]
                          · have p438_0 := h438c.1
                            have p438_1 := h438c.2.1
                            have p438_2 := h438c.2.2.1
                            have p438_3 := h438c.2.2.2
                            rcases p438_3 (m.d 0 2) (by simp) with h451 | h451
                            · rcases p438_3 (m.d 1 2) (by simp) with h452 | h452
                              · linarith only [h0, h452, hlam]
                              · linarith only [h258, h452, hlam]
                            · linarith only [h451, hlam, p438_0]
                          · have p438_0 := h438c.1
                            have p438_1 := h438c.2.1
                            have p438_2 := h438c.2.2.1
                            have p438_3 := h438c.2.2.2
                            linarith only [h0, hlam, p438_1]
                          · have p438_0 := h438c.1
                            have p438_1 := h438c.2.1
                            have p438_2 := h438c.2.2.1
                            have p438_3 := h438c.2.2.2
                            linarith only [hlam, p438_0]
                          · have p438_0 := h438c.1
                            have p438_1 := h438c.2.1
                            have p438_2 := h438c.2.2.1
                            have p438_3 := h438c.2.2.2
                            rcases p438_3 (m.d 0 2) (by simp) with h458 | h458
                            · rcases p438_3 (m.d 1 2) (by simp) with h459 | h459
                              · rcases p438_3 (m.d 2 3) (by simp) with h460 | h460
                                · linarith only [h460, hlam, p438_0]
                                · rcases p438_3 (m.d 2 4) (by simp) with h462 | h462
                                  · linarith only [h257, h462, hlam]
                                  · linarith only [h430, h462, hlam]
                              · linarith only [h459, hlam, p438_0]
                            · linarith only [h3, h458, hlam]
                          · have p438_0 := h438c.1
                            have p438_1 := h438c.2.1
                            have p438_2 := h438c.2.2.1
                            have p438_3 := h438c.2.2.2
                            rcases p438_3 (m.d 0 2) (by simp) with h467 | h467
                            · rcases p438_3 (m.d 1 2) (by simp) with h468 | h468
                              · rcases p438_3 (m.d 2 3) (by simp) with h469 | h469
                                · linarith only [h256, h469, hlam]
                                · rcases p438_3 (m.d 2 4) (by simp) with h471 | h471
                                  · linarith only [h471, hlam, p438_0]
                                  · rcases p438_3 (m.d 2 5) (by simp) with h473 | h473
                                    · linarith only [h258, h473, hlam]
                                    · linarith only [h434, h473, hlam]
                              · linarith only [h468, hlam, p438_0]
                            · linarith only [h4, h467, hlam]
                          · have p438_0 := h438c.1
                            have p438_1 := h438c.2.1
                            have p438_2 := h438c.2.2.1
                            have p438_3 := h438c.2.2.2
                            rcases p438_3 (m.d 0 2) (by simp) with h478 | h478
                            · rcases p438_3 (m.d 1 2) (by simp) with h479 | h479
                              · rcases p438_3 (m.d 2 3) (by simp) with h480 | h480
                                · linarith only [h256, h480, hlam]
                                · rcases p438_3 (m.d 2 4) (by simp) with h482 | h482
                                  · linarith only [h257, h482, hlam]
                                  · rcases p438_3 (m.d 2 5) (by simp) with h484 | h484
                                    · linarith only [h484, hlam, p438_0]
                                    · rcases h3bigk with h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c | h486c
                                      · have p486_0 := h486c.1
                                        have p486_1 := h486c.2.1
                                        have p486_2 := h486c.2.2.1
                                        have p486_3 := h486c.2.2.2
                                        linarith only [hlam, p486_0]
                                      · have p486_0 := h486c.1
                                        have p486_1 := h486c.2.1
                                        have p486_2 := h486c.2.2.1
                                        have p486_3 := h486c.2.2.2
                                        rcases p486_3 (m.d 0 3) (by simp) with h488 | h488
                                        · rcases p486_3 (m.d 1 3) (by simp) with h489 | h489
                                          · linarith only [h1, h489, hlam]
                                          · rcases p486_3 (m.d 2 3) (by simp) with h491 | h491
                                            · linarith only [h3, h491, hlam]
                                            · rcases p486_3 (m.d 3 4) (by simp) with h493 | h493
                                              · linarith only [h493, h6, hlam]
                                              · linarith only [h259, h493, hlam]
                                        · linarith only [h1, h488, hlam]
                                      · have p486_0 := h486c.1
                                        have p486_1 := h486c.2.1
                                        have p486_2 := h486c.2.2.1
                                        have p486_3 := h486c.2.2.2
                                        rcases p486_3 (m.d 0 3) (by simp) with h497 | h497
                                        · rcases p486_3 (m.d 1 3) (by simp) with h498 | h498
                                          · linarith only [h1, h498, hlam]
                                          · linarith only [h256, h498, hlam]
                                        · linarith only [h3, h497, hlam]
                                      · have p486_0 := h486c.1
                                        have p486_1 := h486c.2.1
                                        have p486_2 := h486c.2.2.1
                                        have p486_3 := h486c.2.2.2
                                        linarith only [h256, h259, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p486_1, u2elo0]
                                      · have p486_0 := h486c.1
                                        have p486_1 := h486c.2.1
                                        have p486_2 := h486c.2.2.1
                                        have p486_3 := h486c.2.2.2
                                        linarith only [h256, h259, h3, h436, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p486_1, u2elo0]
                                      · have p486_0 := h486c.1
                                        have p486_1 := h486c.2.1
                                        have p486_2 := h486c.2.2.1
                                        have p486_3 := h486c.2.2.2
                                        linarith only [h1, hlam, p486_0]
                                      · have p486_0 := h486c.1
                                        have p486_1 := h486c.2.1
                                        have p486_2 := h486c.2.2.1
                                        have p486_3 := h486c.2.2.2
                                        linarith only [hlam, p486_0]
                                      · have p486_0 := h486c.1
                                        have p486_1 := h486c.2.1
                                        have p486_2 := h486c.2.2.1
                                        have p486_3 := h486c.2.2.2
                                        linarith only [h259, hc23, hc34, hlam, hphi, p486_1]
                                      · have p486_0 := h486c.1
                                        have p486_1 := h486c.2.1
                                        have p486_2 := h486c.2.2.1
                                        have p486_3 := h486c.2.2.2
                                        linarith only [h259, hlam, p486_0]
                                      · have p486_0 := h486c.1
                                        have p486_1 := h486c.2.1
                                        have p486_2 := h486c.2.2.1
                                        have p486_3 := h486c.2.2.2
                                        linarith only [h426, hlam, p486_0]
                                      · have p486_0 := h486c.1
                                        have p486_1 := h486c.2.1
                                        have p486_2 := h486c.2.2.1
                                        have p486_3 := h486c.2.2.2
                                        linarith only [h3, hlam, p486_1]
                                      · have p486_0 := h486c.1
                                        have p486_1 := h486c.2.1
                                        have p486_2 := h486c.2.2.1
                                        have p486_3 := h486c.2.2.2
                                        linarith only [h256, hlam, p486_1]
                                      · have p486_0 := h486c.1
                                        have p486_1 := h486c.2.1
                                        have p486_2 := h486c.2.2.1
                                        have p486_3 := h486c.2.2.2
                                        linarith only [hlam, p486_0]
                                      · have p486_0 := h486c.1
                                        have p486_1 := h486c.2.1
                                        have p486_2 := h486c.2.2.1
                                        have p486_3 := h486c.2.2.2
                                        linarith only [h430, hlam, p486_0]
                                      · have p486_0 := h486c.1
                                        have p486_1 := h486c.2.1
                                        have p486_2 := h486c.2.2.1
                                        have p486_3 := h486c.2.2.2
                                        linarith only [h432, hlam, p486_0]
                                      · have p486_0 := h486c.1
                                        have p486_1 := h486c.2.1
                                        have p486_2 := h486c.2.2.1
                                        have p486_3 := h486c.2.2.2
                                        linarith only [h6, hlam, p486_0]
                                      · have p486_0 := h486c.1
                                        have p486_1 := h486c.2.1
                                        have p486_2 := h486c.2.2.1
                                        have p486_3 := h486c.2.2.2
                                        linarith only [h3, h6, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p486_1, u2elo0]
                                      · have p486_0 := h486c.1
                                        have p486_1 := h486c.2.1
                                        have p486_2 := h486c.2.2.1
                                        have p486_3 := h486c.2.2.2
                                        linarith only [h3, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p486_1, u2elo0]
                                      · have p486_0 := h486c.1
                                        have p486_1 := h486c.2.1
                                        have p486_2 := h486c.2.2.1
                                        have p486_3 := h486c.2.2.2
                                        linarith only [hlam, p486_0]
                                      · have p486_0 := h486c.1
                                        have p486_1 := h486c.2.1
                                        have p486_2 := h486c.2.2.1
                                        have p486_3 := h486c.2.2.2
                                        linarith only [h436, hlam, p486_0]
                                      · have p486_0 := h486c.1
                                        have p486_1 := h486c.2.1
                                        have p486_2 := h486c.2.2.1
                                        have p486_3 := h486c.2.2.2
                                        linarith only [h7, hlam, p486_0]
                                      · have p486_0 := h486c.1
                                        have p486_1 := h486c.2.1
                                        have p486_2 := h486c.2.2.1
                                        have p486_3 := h486c.2.2.2
                                        linarith only [h256, h3, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p486_1, u2elo0]
                                      · have p486_0 := h486c.1
                                        have p486_1 := h486c.2.1
                                        have p486_2 := h486c.2.2.1
                                        have p486_3 := h486c.2.2.2
                                        linarith only [h3, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p486_1, u2elo0]
                                      · have p486_0 := h486c.1
                                        have p486_1 := h486c.2.1
                                        have p486_2 := h486c.2.2.1
                                        have p486_3 := h486c.2.2.2
                                        linarith only [h3, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p486_1, u2elo0]
                                      · have p486_0 := h486c.1
                                        have p486_1 := h486c.2.1
                                        have p486_2 := h486c.2.2.1
                                        have p486_3 := h486c.2.2.2
                                        linarith only [hlam, p486_0]
                              · linarith only [h479, hlam, p438_0]
                            · linarith only [h478, h5, hlam]
                          · have p438_0 := h438c.1
                            have p438_1 := h438c.2.1
                            have p438_2 := h438c.2.2.1
                            have p438_3 := h438c.2.2.2
                            linarith only [h3, hlam, p438_0]
                          · have p438_0 := h438c.1
                            have p438_1 := h438c.2.1
                            have p438_2 := h438c.2.2.1
                            have p438_3 := h438c.2.2.2
                            linarith only [h256, hlam, p438_0]
                          · have p438_0 := h438c.1
                            have p438_1 := h438c.2.1
                            have p438_2 := h438c.2.2.1
                            have p438_3 := h438c.2.2.2
                            linarith only [hlam, p438_0]
                          · have p438_0 := h438c.1
                            have p438_1 := h438c.2.1
                            have p438_2 := h438c.2.2.1
                            have p438_3 := h438c.2.2.2
                            linarith only [h430, hlam, p438_1]
                          · have p438_0 := h438c.1
                            have p438_1 := h438c.2.1
                            have p438_2 := h438c.2.2.1
                            have p438_3 := h438c.2.2.2
                            linarith only [h432, hlam, p438_1]
                          · have p438_0 := h438c.1
                            have p438_1 := h438c.2.1
                            have p438_2 := h438c.2.2.1
                            have p438_3 := h438c.2.2.2
                            linarith only [h4, hlam, p438_0]
                          · have p438_0 := h438c.1
                            have p438_1 := h438c.2.1
                            have p438_2 := h438c.2.2.1
                            have p438_3 := h438c.2.2.2
                            linarith only [h257, hlam, p438_0]
                          · have p438_0 := h438c.1
                            have p438_1 := h438c.2.1
                            have p438_2 := h438c.2.2.1
                            have p438_3 := h438c.2.2.2
                            linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p438_1, u2elo0]
                          · have p438_0 := h438c.1
                            have p438_1 := h438c.2.1
                            have p438_2 := h438c.2.2.1
                            have p438_3 := h438c.2.2.2
                            linarith only [hlam, p438_0]
                          · have p438_0 := h438c.1
                            have p438_1 := h438c.2.1
                            have p438_2 := h438c.2.2.1
                            have p438_3 := h438c.2.2.2
                            linarith only [h434, hlam, p438_0]
                          · have p438_0 := h438c.1
                            have p438_1 := h438c.2.1
                            have p438_2 := h438c.2.2.1
                            have p438_3 := h438c.2.2.2
                            linarith only [h5, hlam, p438_0]
                          · have p438_0 := h438c.1
                            have p438_1 := h438c.2.1
                            have p438_2 := h438c.2.2.1
                            have p438_3 := h438c.2.2.2
                            linarith only [h258, hlam, p438_0]
                          · have p438_0 := h438c.1
                            have p438_1 := h438c.2.1
                            have p438_2 := h438c.2.2.1
                            have p438_3 := h438c.2.2.2
                            linarith only [h258, h3, h426, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p438_1, u2elo0]
                          · have p438_0 := h438c.1
                            have p438_1 := h438c.2.1
                            have p438_2 := h438c.2.2.1
                            have p438_3 := h438c.2.2.2
                            linarith only [h258, h3, h426, h7, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p438_1, u2elo0]
                          · have p438_0 := h438c.1
                            have p438_1 := h438c.2.1
                            have p438_2 := h438c.2.2.1
                            have p438_3 := h438c.2.2.2
                            linarith only [hlam, p438_0]
          · linarith only [h258, h5, hc12, hlam, hphi, u2elo0]
        · linarith only [h256, h257, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
      · linarith only [h256, h3, hc12, hlam, hphi, u2elo0]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h544 | h544
    · linarith only [h544, h6, h7, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h546 | h546
      · rcases m.htr 1 2 4 (by decide) (by decide) with h547 | h547
        · rcases m.htr 1 2 5 (by decide) (by decide) with h548 | h548
          · rcases m.htr 1 3 4 (by decide) (by decide) with h549 | h549
            · rcases m.htr 1 3 5 (by decide) (by decide) with h550 | h550
              · linarith only [h1, h550, h7, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h552 | h552
                · linarith only [h1, h544, h549, h552, h7, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h554 | h554
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h555 | h555
                    · linarith only [h1, h3, h555, h7, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h557 | h557
                      · linarith only [h4, h544, h557, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h559 | h559
                        · linarith only [h544, h548, h554, h555, h559, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases h2bigk with h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c
                          · have p561_0 := h561c.1
                            have p561_1 := h561c.2.1
                            have p561_2 := h561c.2.2.1
                            have p561_3 := h561c.2.2.2
                            linarith only [hlam, p561_0]
                          · have p561_0 := h561c.1
                            have p561_1 := h561c.2.1
                            have p561_2 := h561c.2.2.1
                            have p561_3 := h561c.2.2.2
                            linarith only [h548, h554, h555, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p561_1, u2elo0]
                          · have p561_0 := h561c.1
                            have p561_1 := h561c.2.1
                            have p561_2 := h561c.2.2.1
                            have p561_3 := h561c.2.2.2
                            linarith only [h554, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p561_1, u2elo0]
                          · have p561_0 := h561c.1
                            have p561_1 := h561c.2.1
                            have p561_2 := h561c.2.2.1
                            have p561_3 := h561c.2.2.2
                            rcases p561_3 (m.d 0 2) (by simp) with h565 | h565
                            · rcases p561_3 (m.d 1 2) (by simp) with h566 | h566
                              · linarith only [h0, h566, hlam]
                              · linarith only [h547, h566, hlam]
                            · linarith only [h565, hlam, p561_0]
                          · have p561_0 := h561c.1
                            have p561_1 := h561c.2.1
                            have p561_2 := h561c.2.2.1
                            have p561_3 := h561c.2.2.2
                            linarith only [h554, h555, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p561_1, u2elo0]
                          · have p561_0 := h561c.1
                            have p561_1 := h561c.2.1
                            have p561_2 := h561c.2.2.1
                            have p561_3 := h561c.2.2.2
                            linarith only [h0, hlam, p561_1]
                          · have p561_0 := h561c.1
                            have p561_1 := h561c.2.1
                            have p561_2 := h561c.2.2.1
                            have p561_3 := h561c.2.2.2
                            linarith only [hlam, p561_0]
                          · have p561_0 := h561c.1
                            have p561_1 := h561c.2.1
                            have p561_2 := h561c.2.2.1
                            have p561_3 := h561c.2.2.2
                            linarith only [h554, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p561_1, u2elo1]
                          · have p561_0 := h561c.1
                            have p561_1 := h561c.2.1
                            have p561_2 := h561c.2.2.1
                            have p561_3 := h561c.2.2.2
                            rcases p561_3 (m.d 0 2) (by simp) with h574 | h574
                            · rcases p561_3 (m.d 1 2) (by simp) with h575 | h575
                              · rcases p561_3 (m.d 2 3) (by simp) with h576 | h576
                                · linarith only [h546, h576, hlam]
                                · linarith only [h554, h576, hlam]
                              · linarith only [h575, hlam, p561_0]
                            · linarith only [h4, h574, hlam]
                          · have p561_0 := h561c.1
                            have p561_1 := h561c.2.1
                            have p561_2 := h561c.2.2.1
                            have p561_3 := h561c.2.2.2
                            linarith only [h0, h554, h555, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p561_1, u2elo0]
                          · have p561_0 := h561c.1
                            have p561_1 := h561c.2.1
                            have p561_2 := h561c.2.2.1
                            have p561_3 := h561c.2.2.2
                            linarith only [h3, hlam, p561_0]
                          · have p561_0 := h561c.1
                            have p561_1 := h561c.2.1
                            have p561_2 := h561c.2.2.1
                            have p561_3 := h561c.2.2.2
                            linarith only [h546, hlam, p561_0]
                          · have p561_0 := h561c.1
                            have p561_1 := h561c.2.1
                            have p561_2 := h561c.2.2.1
                            have p561_3 := h561c.2.2.2
                            linarith only [hlam, p561_0]
                          · have p561_0 := h561c.1
                            have p561_1 := h561c.2.1
                            have p561_2 := h561c.2.2.1
                            have p561_3 := h561c.2.2.2
                            linarith only [h3, h554, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p561_1, u2elo0]
                          · have p561_0 := h561c.1
                            have p561_1 := h561c.2.1
                            have p561_2 := h561c.2.2.1
                            have p561_3 := h561c.2.2.2
                            linarith only [h555, hlam, p561_1]
                          · have p561_0 := h561c.1
                            have p561_1 := h561c.2.1
                            have p561_2 := h561c.2.2.1
                            have p561_3 := h561c.2.2.2
                            linarith only [h4, hlam, p561_0]
                          · have p561_0 := h561c.1
                            have p561_1 := h561c.2.1
                            have p561_2 := h561c.2.2.1
                            have p561_3 := h561c.2.2.2
                            linarith only [h547, hlam, p561_0]
                          · have p561_0 := h561c.1
                            have p561_1 := h561c.2.1
                            have p561_2 := h561c.2.2.1
                            have p561_3 := h561c.2.2.2
                            linarith only [h554, hlam, p561_0]
                          · have p561_0 := h561c.1
                            have p561_1 := h561c.2.1
                            have p561_2 := h561c.2.2.1
                            have p561_3 := h561c.2.2.2
                            linarith only [hlam, p561_0]
                          · have p561_0 := h561c.1
                            have p561_1 := h561c.2.1
                            have p561_2 := h561c.2.2.1
                            have p561_3 := h561c.2.2.2
                            linarith only [h557, hlam, p561_0]
                          · have p561_0 := h561c.1
                            have p561_1 := h561c.2.1
                            have p561_2 := h561c.2.2.1
                            have p561_3 := h561c.2.2.2
                            linarith only [h5, hlam, p561_0]
                          · have p561_0 := h561c.1
                            have p561_1 := h561c.2.1
                            have p561_2 := h561c.2.2.1
                            have p561_3 := h561c.2.2.2
                            linarith only [h548, hlam, p561_0]
                          · have p561_0 := h561c.1
                            have p561_1 := h561c.2.1
                            have p561_2 := h561c.2.2.1
                            have p561_3 := h561c.2.2.2
                            linarith only [h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p561_1, u2elo0]
                          · have p561_0 := h561c.1
                            have p561_1 := h561c.2.1
                            have p561_2 := h561c.2.2.1
                            have p561_3 := h561c.2.2.2
                            linarith only [h0, h548, h554, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p561_1, u2elo0]
                          · have p561_0 := h561c.1
                            have p561_1 := h561c.2.1
                            have p561_2 := h561c.2.2.1
                            have p561_3 := h561c.2.2.2
                            linarith only [hlam, p561_0]
                  · linarith only [h554, h6, h7, hc23, hc35, hlam, hphi]
            · linarith only [h549, h6, h7, hc13, hc35, hlam, hphi]
          · linarith only [h5, h548, hc12, hlam, hphi, u2elo0]
        · linarith only [h4, h546, h547, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
      · linarith only [h3, h546, hc12, hlam, hphi, u2elo0]

end R2N4
