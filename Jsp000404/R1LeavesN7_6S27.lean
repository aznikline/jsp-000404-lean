import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_6S24
import Jsp000404.R1LeavesN7_6S25
import Jsp000404.R1LeavesN7_6S26

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9982000 in
set_option maxHeartbeats 9982000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s12_x1_x1_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg10058 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11024 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11558 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h14803 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h15246 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h15483 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h15484 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h16201 | h16201
  · linarith only [h15483, h15484, h16201, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h16203 | h16203
    · rcases m.htr 1 2 4 (by decide) (by decide) with h16204 | h16204
      · rcases m.htr 1 2 5 (by decide) (by decide) with h16205 | h16205
        · rcases m.htr 1 3 4 (by decide) (by decide) with h16206 | h16206
          · rcases m.htr 1 4 5 (by decide) (by decide) with h16207 | h16207
            · rcases m.htr 2 3 4 (by decide) (by decide) with h16208 | h16208
              · rcases m.htr 2 3 5 (by decide) (by decide) with h16209 | h16209
                · linarith only [h15483, h15484, h16203, h16209, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h16211 | h16211
                  · linarith only [h0, h14803, h16201, h16208, h16209, h16211, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h14803, h16203, h16206, h16207, h16211, hc01, hc12, hlam, hphi]
              · linarith only [h0, h11558, h15483, h16208, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h16215 | h16215
              · rcases m.htr 2 3 5 (by decide) (by decide) with h16216 | h16216
                · linarith only [h15483, h15484, h16203, h16216, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h16218 | h16218
                  · linarith only [h16204, h16207, h16218, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h16220 | h16220
                    · linarith only [h0, h14803, h15483, h16204, h16207, h16220, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · rcases h0bigk with h16222c | h16222c | h16222c | h16222c | h16222c | h16222c | h16222c | h16222c | h16222c | h16222c | h16222c | h16222c | h16222c | h16222c | h16222c | h16222c | h16222c | h16222c | h16222c | h16222c | h16222c | h16222c | h16222c | h16222c | h16222c
                      · have p16222_0 := h16222c.1
                        have p16222_1 := h16222c.2.1
                        have p16222_2 := h16222c.2.2.1
                        have p16222_3 := h16222c.2.2.2
                        linarith only [hlam, p16222_0]
                      · have p16222_0 := h16222c.1
                        have p16222_1 := h16222c.2.1
                        have p16222_2 := h16222c.2.2.1
                        have p16222_3 := h16222c.2.2.2
                        linarith only [h0, hlam, p16222_1]
                      · have p16222_0 := h16222c.1
                        have p16222_1 := h16222c.2.1
                        have p16222_2 := h16222c.2.2.1
                        have p16222_3 := h16222c.2.2.2
                        linarith only [h6793, hlam, p16222_0]
                      · have p16222_0 := h16222c.1
                        have p16222_1 := h16222c.2.1
                        have p16222_2 := h16222c.2.2.1
                        have p16222_3 := h16222c.2.2.2
                        linarith only [h10058, hlam, p16222_1]
                      · have p16222_0 := h16222c.1
                        have p16222_1 := h16222c.2.1
                        have p16222_2 := h16222c.2.2.1
                        have p16222_3 := h16222c.2.2.2
                        linarith only [h11024, hlam, p16222_1]
                      · have p16222_0 := h16222c.1
                        have p16222_1 := h16222c.2.1
                        have p16222_2 := h16222c.2.2.1
                        have p16222_3 := h16222c.2.2.2
                        linarith only [h14803, h16204, hc01, hc14, hlam, hphi, p16222_1]
                      · have p16222_0 := h16222c.1
                        have p16222_1 := h16222c.2.1
                        have p16222_2 := h16222c.2.2.1
                        have p16222_3 := h16222c.2.2.2
                        linarith only [hlam, p16222_0]
                      · have p16222_0 := h16222c.1
                        have p16222_1 := h16222c.2.1
                        have p16222_2 := h16222c.2.2.1
                        have p16222_3 := h16222c.2.2.2
                        linarith only [h11558, hlam, p16222_0]
                      · have p16222_0 := h16222c.1
                        have p16222_1 := h16222c.2.1
                        have p16222_2 := h16222c.2.2.1
                        have p16222_3 := h16222c.2.2.2
                        linarith only [h14803, hlam, p16222_1]
                      · have p16222_0 := h16222c.1
                        have p16222_1 := h16222c.2.1
                        have p16222_2 := h16222c.2.2.1
                        have p16222_3 := h16222c.2.2.2
                        linarith only [h15246, hlam, p16222_0]
                      · have p16222_0 := h16222c.1
                        have p16222_1 := h16222c.2.1
                        have p16222_2 := h16222c.2.2.1
                        have p16222_3 := h16222c.2.2.2
                        linarith only [h11558, h16216, h16220, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p16222_1]
                      · have p16222_0 := h16222c.1
                        have p16222_1 := h16222c.2.1
                        have p16222_2 := h16222c.2.2.1
                        have p16222_3 := h16222c.2.2.2
                        linarith only [h11558, h16216, h16220, hc02, hc45, hlam, hphi, ht23, ht34, p16222_1]
                      · have p16222_0 := h16222c.1
                        have p16222_1 := h16222c.2.1
                        have p16222_2 := h16222c.2.2.1
                        have p16222_3 := h16222c.2.2.2
                        linarith only [hlam, p16222_0]
                      · have p16222_0 := h16222c.1
                        have p16222_1 := h16222c.2.1
                        have p16222_2 := h16222c.2.2.1
                        have p16222_3 := h16222c.2.2.2
                        linarith only [h0, h11558, h14803, h16216, h16220, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p16222_1]
                      · have p16222_0 := h16222c.1
                        have p16222_1 := h16222c.2.1
                        have p16222_2 := h16222c.2.2.1
                        have p16222_3 := h16222c.2.2.2
                        linarith only [h15484, hlam, p16222_1]
                      · have p16222_0 := h16222c.1
                        have p16222_1 := h16222c.2.1
                        have p16222_2 := h16222c.2.2.1
                        have p16222_3 := h16222c.2.2.2
                        linarith only [h11558, h15483, h16216, h16220, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p16222_1]
                      · have p16222_0 := h16222c.1
                        have p16222_1 := h16222c.2.1
                        have p16222_2 := h16222c.2.2.1
                        have p16222_3 := h16222c.2.2.2
                        linarith only [h0, h11558, h15483, h16216, h16220, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p16222_1]
                      · have p16222_0 := h16222c.1
                        have p16222_1 := h16222c.2.1
                        have p16222_2 := h16222c.2.2.1
                        have p16222_3 := h16222c.2.2.2
                        linarith only [h15483, hlam, p16222_0]
                      · have p16222_0 := h16222c.1
                        have p16222_1 := h16222c.2.1
                        have p16222_2 := h16222c.2.2.1
                        have p16222_3 := h16222c.2.2.2
                        linarith only [hlam, p16222_0]
                      · have p16222_0 := h16222c.1
                        have p16222_1 := h16222c.2.1
                        have p16222_2 := h16222c.2.2.1
                        have p16222_3 := h16222c.2.2.2
                        linarith only [h16201, hlam, p16222_0]
                      · have p16222_0 := h16222c.1
                        have p16222_1 := h16222c.2.1
                        have p16222_2 := h16222c.2.2.1
                        have p16222_3 := h16222c.2.2.2
                        linarith only [h15246, h16205, hc01, hc12, hlam, hphi, p16222_1]
                      · have p16222_0 := h16222c.1
                        have p16222_1 := h16222c.2.1
                        have p16222_2 := h16222c.2.2.1
                        have p16222_3 := h16222c.2.2.2
                        linarith only [h0, h15246, h16205, hc01, hc12, hlam, hphi, p16222_1]
                      · have p16222_0 := h16222c.1
                        have p16222_1 := h16222c.2.1
                        have p16222_2 := h16222c.2.2.1
                        have p16222_3 := h16222c.2.2.2
                        linarith only [h15246, h15483, h16205, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16222_1]
                      · have p16222_0 := h16222c.1
                        have p16222_1 := h16222c.2.1
                        have p16222_2 := h16222c.2.2.1
                        have p16222_3 := h16222c.2.2.2
                        linarith only [h10058, h15246, h16205, hc01, hc12, hlam, hphi, p16222_1]
                      · have p16222_0 := h16222c.1
                        have p16222_1 := h16222c.2.1
                        have p16222_2 := h16222c.2.2.1
                        have p16222_3 := h16222c.2.2.2
                        linarith only [hlam, p16222_0]
              · linarith only [h0, h11558, h15483, h16215, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
          · linarith only [h14803, h15483, h16204, h16206, h6793, hc01, hc12, hlam, hphi]
        · linarith only [h0, h14803, h16204, h16205, hc01, hc25, hlam, hphi, ht12]
      · linarith only [h0, h11558, h16203, h16204, hc01, hc24, hlam, hphi, ht12]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h16252 | h16252
      · linarith only [h0, h14803, h16203, h16252, hc01, hc23, hlam, hphi, ht12]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h16254 | h16254
        · linarith only [h0, h15246, h16203, h16254, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h16256 | h16256
          · rcases m.htr 1 4 5 (by decide) (by decide) with h16257 | h16257
            · rcases m.htr 2 3 4 (by decide) (by decide) with h16258 | h16258
              · rcases m.htr 2 3 5 (by decide) (by decide) with h16259 | h16259
                · rcases m.htr 2 4 5 (by decide) (by decide) with h16260 | h16260
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h16261 | h16261
                    · linarith only [h15483, h15484, h16201, h16259, h16261, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases h0bigk with h16263c | h16263c | h16263c | h16263c | h16263c | h16263c | h16263c | h16263c | h16263c | h16263c | h16263c | h16263c | h16263c | h16263c | h16263c | h16263c | h16263c | h16263c | h16263c | h16263c | h16263c | h16263c | h16263c | h16263c | h16263c
                      · have p16263_0 := h16263c.1
                        have p16263_1 := h16263c.2.1
                        have p16263_2 := h16263c.2.2.1
                        have p16263_3 := h16263c.2.2.2
                        linarith only [hlam, p16263_0]
                      · have p16263_0 := h16263c.1
                        have p16263_1 := h16263c.2.1
                        have p16263_2 := h16263c.2.2.1
                        have p16263_3 := h16263c.2.2.2
                        linarith only [h0, hlam, p16263_1]
                      · have p16263_0 := h16263c.1
                        have p16263_1 := h16263c.2.1
                        have p16263_2 := h16263c.2.2.1
                        have p16263_3 := h16263c.2.2.2
                        linarith only [h6793, hlam, p16263_0]
                      · have p16263_0 := h16263c.1
                        have p16263_1 := h16263c.2.1
                        have p16263_2 := h16263c.2.2.1
                        have p16263_3 := h16263c.2.2.2
                        linarith only [h10058, hlam, p16263_1]
                      · have p16263_0 := h16263c.1
                        have p16263_1 := h16263c.2.1
                        have p16263_2 := h16263c.2.2.1
                        have p16263_3 := h16263c.2.2.2
                        linarith only [h11024, hlam, p16263_1]
                      · have p16263_0 := h16263c.1
                        have p16263_1 := h16263c.2.1
                        have p16263_2 := h16263c.2.2.1
                        have p16263_3 := h16263c.2.2.2
                        linarith only [h0, h16254, h16258, h16260, hc01, hc23, hlam, hphi, ht12, p16263_1]
                      · have p16263_0 := h16263c.1
                        have p16263_1 := h16263c.2.1
                        have p16263_2 := h16263c.2.2.1
                        have p16263_3 := h16263c.2.2.2
                        linarith only [hlam, p16263_0]
                      · have p16263_0 := h16263c.1
                        have p16263_1 := h16263c.2.1
                        have p16263_2 := h16263c.2.2.1
                        have p16263_3 := h16263c.2.2.2
                        linarith only [h11558, hlam, p16263_0]
                      · have p16263_0 := h16263c.1
                        have p16263_1 := h16263c.2.1
                        have p16263_2 := h16263c.2.2.1
                        have p16263_3 := h16263c.2.2.2
                        linarith only [h14803, hlam, p16263_1]
                      · have p16263_0 := h16263c.1
                        have p16263_1 := h16263c.2.1
                        have p16263_2 := h16263c.2.2.1
                        have p16263_3 := h16263c.2.2.2
                        linarith only [h15246, hlam, p16263_0]
                      · have p16263_0 := h16263c.1
                        have p16263_1 := h16263c.2.1
                        have p16263_2 := h16263c.2.2.1
                        have p16263_3 := h16263c.2.2.2
                        linarith only [h15484, hc01, hc35, hlam, hphi, ht12, ht23, p16263_1]
                      · have p16263_0 := h16263c.1
                        have p16263_1 := h16263c.2.1
                        have p16263_2 := h16263c.2.2.1
                        have p16263_3 := h16263c.2.2.2
                        linarith only [h15484, h16261, hc02, hc45, hlam, hphi, ht23, ht34, p16263_1]
                      · have p16263_0 := h16263c.1
                        have p16263_1 := h16263c.2.1
                        have p16263_2 := h16263c.2.2.1
                        have p16263_3 := h16263c.2.2.2
                        linarith only [hlam, p16263_0]
                      · have p16263_0 := h16263c.1
                        have p16263_1 := h16263c.2.1
                        have p16263_2 := h16263c.2.2.1
                        have p16263_3 := h16263c.2.2.2
                        linarith only [h15484, h16261, hc04, hc45, hlam, hphi, p16263_1]
                      · have p16263_0 := h16263c.1
                        have p16263_1 := h16263c.2.1
                        have p16263_2 := h16263c.2.2.1
                        have p16263_3 := h16263c.2.2.2
                        linarith only [h15484, hlam, p16263_1]
                      · have p16263_0 := h16263c.1
                        have p16263_1 := h16263c.2.1
                        have p16263_2 := h16263c.2.2.1
                        have p16263_3 := h16263c.2.2.2
                        linarith only [h15483, h15484, h16261, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p16263_1]
                      · have p16263_0 := h16263c.1
                        have p16263_1 := h16263c.2.1
                        have p16263_2 := h16263c.2.2.1
                        have p16263_3 := h16263c.2.2.2
                        linarith only [h0, h15483, h15484, h16261, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p16263_1]
                      · have p16263_0 := h16263c.1
                        have p16263_1 := h16263c.2.1
                        have p16263_2 := h16263c.2.2.1
                        have p16263_3 := h16263c.2.2.2
                        linarith only [h15483, hlam, p16263_0]
                      · have p16263_0 := h16263c.1
                        have p16263_1 := h16263c.2.1
                        have p16263_2 := h16263c.2.2.1
                        have p16263_3 := h16263c.2.2.2
                        linarith only [hlam, p16263_0]
                      · have p16263_0 := h16263c.1
                        have p16263_1 := h16263c.2.1
                        have p16263_2 := h16263c.2.2.1
                        have p16263_3 := h16263c.2.2.2
                        linarith only [h16201, hlam, p16263_0]
                      · have p16263_0 := h16263c.1
                        have p16263_1 := h16263c.2.1
                        have p16263_2 := h16263c.2.2.1
                        have p16263_3 := h16263c.2.2.2
                        linarith only [h15484, h16203, h16256, h16257, h16261, hc01, hc23, hlam, hphi, ht12, p16263_1]
                      · have p16263_0 := h16263c.1
                        have p16263_1 := h16263c.2.1
                        have p16263_2 := h16263c.2.2.1
                        have p16263_3 := h16263c.2.2.2
                        linarith only [h0, h15484, h16203, h16256, h16257, h16261, hc01, hc23, hlam, hphi, ht12, p16263_1]
                      · have p16263_0 := h16263c.1
                        have p16263_1 := h16263c.2.1
                        have p16263_2 := h16263c.2.2.1
                        have p16263_3 := h16263c.2.2.2
                        linarith only [h15483, h15484, h16203, h16256, h16257, h16261, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p16263_1]
                      · have p16263_0 := h16263c.1
                        have p16263_1 := h16263c.2.1
                        have p16263_2 := h16263c.2.2.1
                        have p16263_3 := h16263c.2.2.2
                        linarith only [h10058, h15484, h16203, h16256, h16257, h16261, hc01, hc23, hlam, hphi, ht12, p16263_1]
                      · have p16263_0 := h16263c.1
                        have p16263_1 := h16263c.2.1
                        have p16263_2 := h16263c.2.2.1
                        have p16263_3 := h16263c.2.2.2
                        linarith only [hlam, p16263_0]
                  · linarith only [h0, h14803, h16203, h16256, h16257, h16260, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h14803, h16201, h16203, h16256, h16257, h16259, hc01, hc35, hlam, hphi, ht12, ht23]
              · linarith only [h0, h14803, h15483, h16201, h16203, h16256, h16257, h16258, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h16292 | h16292
              · rcases m.htr 2 3 5 (by decide) (by decide) with h16293 | h16293
                · rcases m.htr 2 4 5 (by decide) (by decide) with h16294 | h16294
                  · linarith only [h0, h16252, h16257, h16294, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h0, h16252, h16294, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · linarith only [h0, h16203, h16293, hc01, hc35, hlam, hphi, ht12, ht23]
              · linarith only [h0, h15483, h16203, h16292, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
          · linarith only [h15483, h16256, h6793, hlam]

set_option maxHeartbeats 9982000 in
set_option maxHeartbeats 9982000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s12_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg10058 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11024 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11558 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h14803 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h15246 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h15483 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  rcases m.htr 0 3 5 (by decide) (by decide) with h15484 | h15484
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s12_x1_x1_x1_x0_x0 m hb0 hb2 hb4 hg0 hg6793 hg10058 hg11024 h11558 h14803 h15246 h15483 h15484
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s12_x1_x1_x1_x0_x1 m hb0 hb2 hb4 hg0 hg6793 hg10058 hg11024 h11558 h14803 h15246 h15483 h15484

set_option maxHeartbeats 9982000 in
set_option maxHeartbeats 9982000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s12_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg10058 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11024 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11558 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h14803 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h15246 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h15483 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  rcases m.htr 0 3 5 (by decide) (by decide) with h16300 | h16300
  · rcases m.htr 0 4 5 (by decide) (by decide) with h16301 | h16301
    · rcases m.htr 1 2 3 (by decide) (by decide) with h16302 | h16302
      · rcases m.htr 1 2 4 (by decide) (by decide) with h16303 | h16303
        · rcases m.htr 1 2 5 (by decide) (by decide) with h16304 | h16304
          · rcases m.htr 1 3 4 (by decide) (by decide) with h16305 | h16305
            · rcases m.htr 1 4 5 (by decide) (by decide) with h16306 | h16306
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16307 | h16307
                · linarith only [h15483, h16300, h16302, h16307, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h0, h11558, h16302, h16305, h16307, hc01, hc12, hlam, hphi]
              · linarith only [h10058, h15483, h16300, h16301, h16302, h16305, h16306, hc01, hc12, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h16311 | h16311
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16312 | h16312
                · linarith only [h16302, h16305, h16312, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h16314 | h16314
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h16315 | h16315
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h16316 | h16316
                      · rcases h0bigk with h16317c | h16317c | h16317c | h16317c | h16317c | h16317c | h16317c | h16317c | h16317c | h16317c | h16317c | h16317c | h16317c | h16317c | h16317c | h16317c | h16317c | h16317c | h16317c | h16317c | h16317c | h16317c | h16317c | h16317c | h16317c
                        · have p16317_0 := h16317c.1
                          have p16317_1 := h16317c.2.1
                          have p16317_2 := h16317c.2.2.1
                          have p16317_3 := h16317c.2.2.2
                          linarith only [hlam, p16317_0]
                        · have p16317_0 := h16317c.1
                          have p16317_1 := h16317c.2.1
                          have p16317_2 := h16317c.2.2.1
                          have p16317_3 := h16317c.2.2.2
                          linarith only [h0, hlam, p16317_1]
                        · have p16317_0 := h16317c.1
                          have p16317_1 := h16317c.2.1
                          have p16317_2 := h16317c.2.2.1
                          have p16317_3 := h16317c.2.2.2
                          linarith only [h6793, hlam, p16317_0]
                        · have p16317_0 := h16317c.1
                          have p16317_1 := h16317c.2.1
                          have p16317_2 := h16317c.2.2.1
                          have p16317_3 := h16317c.2.2.2
                          linarith only [h10058, hlam, p16317_1]
                        · have p16317_0 := h16317c.1
                          have p16317_1 := h16317c.2.1
                          have p16317_2 := h16317c.2.2.1
                          have p16317_3 := h16317c.2.2.2
                          linarith only [h11024, hlam, p16317_1]
                        · have p16317_0 := h16317c.1
                          have p16317_1 := h16317c.2.1
                          have p16317_2 := h16317c.2.2.1
                          have p16317_3 := h16317c.2.2.2
                          linarith only [h11558, h16302, h16305, hc01, hc34, hlam, hphi, ht12, ht23, p16317_1]
                        · have p16317_0 := h16317c.1
                          have p16317_1 := h16317c.2.1
                          have p16317_2 := h16317c.2.2.1
                          have p16317_3 := h16317c.2.2.2
                          linarith only [hlam, p16317_0]
                        · have p16317_0 := h16317c.1
                          have p16317_1 := h16317c.2.1
                          have p16317_2 := h16317c.2.2.1
                          have p16317_3 := h16317c.2.2.2
                          linarith only [h11558, hlam, p16317_0]
                        · have p16317_0 := h16317c.1
                          have p16317_1 := h16317c.2.1
                          have p16317_2 := h16317c.2.2.1
                          have p16317_3 := h16317c.2.2.2
                          linarith only [h14803, hlam, p16317_1]
                        · have p16317_0 := h16317c.1
                          have p16317_1 := h16317c.2.1
                          have p16317_2 := h16317c.2.2.1
                          have p16317_3 := h16317c.2.2.2
                          linarith only [h15246, hlam, p16317_0]
                        · have p16317_0 := h16317c.1
                          have p16317_1 := h16317c.2.1
                          have p16317_2 := h16317c.2.2.1
                          have p16317_3 := h16317c.2.2.2
                          linarith only [h11558, h16302, h16305, hc01, hc34, hlam, hphi, ht12, ht23, p16317_1]
                        · have p16317_0 := h16317c.1
                          have p16317_1 := h16317c.2.1
                          have p16317_2 := h16317c.2.2.1
                          have p16317_3 := h16317c.2.2.2
                          linarith only [h11558, h16302, h16305, hc02, hc34, hlam, hphi, ht23, p16317_1]
                        · have p16317_0 := h16317c.1
                          have p16317_1 := h16317c.2.1
                          have p16317_2 := h16317c.2.2.1
                          have p16317_3 := h16317c.2.2.2
                          linarith only [hlam, p16317_0]
                        · have p16317_0 := h16317c.1
                          have p16317_1 := h16317c.2.1
                          have p16317_2 := h16317c.2.2.1
                          have p16317_3 := h16317c.2.2.2
                          linarith only [h15483, hlam, p16317_1]
                        · have p16317_0 := h16317c.1
                          have p16317_1 := h16317c.2.1
                          have p16317_2 := h16317c.2.2.1
                          have p16317_3 := h16317c.2.2.2
                          linarith only [h11024, h11558, h16302, h16305, hc01, hc34, hlam, hphi, ht12, ht23, p16317_1]
                        · have p16317_0 := h16317c.1
                          have p16317_1 := h16317c.2.1
                          have p16317_2 := h16317c.2.2.1
                          have p16317_3 := h16317c.2.2.2
                          linarith only [h14803, h16303, hc01, hc12, hlam, hphi, p16317_1]
                        · have p16317_0 := h16317c.1
                          have p16317_1 := h16317c.2.1
                          have p16317_2 := h16317c.2.2.1
                          have p16317_3 := h16317c.2.2.2
                          linarith only [h0, h14803, h16303, hc01, hc12, hlam, hphi, p16317_1]
                        · have p16317_0 := h16317c.1
                          have p16317_1 := h16317c.2.1
                          have p16317_2 := h16317c.2.2.1
                          have p16317_3 := h16317c.2.2.2
                          linarith only [h16300, hc35, hlam, hphi, ht0b, ht5b, p16317_1, u0elo3]
                        · have p16317_0 := h16317c.1
                          have p16317_1 := h16317c.2.1
                          have p16317_2 := h16317c.2.2.1
                          have p16317_3 := h16317c.2.2.2
                          linarith only [hlam, p16317_0]
                        · have p16317_0 := h16317c.1
                          have p16317_1 := h16317c.2.1
                          have p16317_2 := h16317c.2.2.1
                          have p16317_3 := h16317c.2.2.2
                          linarith only [h0, h14803, h15246, h16303, hc01, hc12, hlam, hphi, p16317_1]
                        · have p16317_0 := h16317c.1
                          have p16317_1 := h16317c.2.1
                          have p16317_2 := h16317c.2.2.1
                          have p16317_3 := h16317c.2.2.2
                          linarith only [h16300, h16305, h6793, hc01, hc34, hlam, hphi, ht12, ht23, p16317_1]
                        · have p16317_0 := h16317c.1
                          have p16317_1 := h16317c.2.1
                          have p16317_2 := h16317c.2.2.1
                          have p16317_3 := h16317c.2.2.2
                          linarith only [h11558, h16300, h16302, h16305, hc02, hc34, hlam, hphi, ht23, p16317_1]
                        · have p16317_0 := h16317c.1
                          have p16317_1 := h16317c.2.1
                          have p16317_2 := h16317c.2.2.1
                          have p16317_3 := h16317c.2.2.2
                          linarith only [h16300, hlam, p16317_0]
                        · have p16317_0 := h16317c.1
                          have p16317_1 := h16317c.2.1
                          have p16317_2 := h16317c.2.2.1
                          have p16317_3 := h16317c.2.2.2
                          linarith only [h16301, hlam, p16317_1]
                        · have p16317_0 := h16317c.1
                          have p16317_1 := h16317c.2.1
                          have p16317_2 := h16317c.2.2.1
                          have p16317_3 := h16317c.2.2.2
                          linarith only [hlam, p16317_0]
                      · linarith only [h16305, h16316, h6793, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h15246, h16301, h16312, h16314, h16315, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h16300, h16305, h16314, h6793, hc23, hc34, hlam, hphi]
              · linarith only [h14803, h16301, h16303, h16311, hlam]
          · linarith only [h0, h11558, h16302, h16304, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h11558, h16302, h16303, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h16349 | h16349
        · linarith only [h0, h14803, h16302, h16349, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h16351 | h16351
          · linarith only [h0, h15246, h16302, h16351, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h16353 | h16353
            · rcases m.htr 1 4 5 (by decide) (by decide) with h16354 | h16354
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16355 | h16355
                · rcases m.htr 2 3 5 (by decide) (by decide) with h16356 | h16356
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h16357 | h16357
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h16358 | h16358
                      · rcases h0bigk with h16359c | h16359c | h16359c | h16359c | h16359c | h16359c | h16359c | h16359c | h16359c | h16359c | h16359c | h16359c | h16359c | h16359c | h16359c | h16359c | h16359c | h16359c | h16359c | h16359c | h16359c | h16359c | h16359c | h16359c | h16359c
                        · have p16359_0 := h16359c.1
                          have p16359_1 := h16359c.2.1
                          have p16359_2 := h16359c.2.2.1
                          have p16359_3 := h16359c.2.2.2
                          linarith only [hlam, p16359_0]
                        · have p16359_0 := h16359c.1
                          have p16359_1 := h16359c.2.1
                          have p16359_2 := h16359c.2.2.1
                          have p16359_3 := h16359c.2.2.2
                          linarith only [h0, hlam, p16359_1]
                        · have p16359_0 := h16359c.1
                          have p16359_1 := h16359c.2.1
                          have p16359_2 := h16359c.2.2.1
                          have p16359_3 := h16359c.2.2.2
                          linarith only [h6793, hlam, p16359_0]
                        · have p16359_0 := h16359c.1
                          have p16359_1 := h16359c.2.1
                          have p16359_2 := h16359c.2.2.1
                          have p16359_3 := h16359c.2.2.2
                          linarith only [h10058, hlam, p16359_1]
                        · have p16359_0 := h16359c.1
                          have p16359_1 := h16359c.2.1
                          have p16359_2 := h16359c.2.2.1
                          have p16359_3 := h16359c.2.2.2
                          linarith only [h11024, hlam, p16359_1]
                        · have p16359_0 := h16359c.1
                          have p16359_1 := h16359c.2.1
                          have p16359_2 := h16359c.2.2.1
                          have p16359_3 := h16359c.2.2.2
                          linarith only [h0, h16351, h16355, h16357, hc01, hc23, hlam, hphi, ht12, p16359_1]
                        · have p16359_0 := h16359c.1
                          have p16359_1 := h16359c.2.1
                          have p16359_2 := h16359c.2.2.1
                          have p16359_3 := h16359c.2.2.2
                          linarith only [hlam, p16359_0]
                        · have p16359_0 := h16359c.1
                          have p16359_1 := h16359c.2.1
                          have p16359_2 := h16359c.2.2.1
                          have p16359_3 := h16359c.2.2.2
                          linarith only [h11558, hlam, p16359_0]
                        · have p16359_0 := h16359c.1
                          have p16359_1 := h16359c.2.1
                          have p16359_2 := h16359c.2.2.1
                          have p16359_3 := h16359c.2.2.2
                          linarith only [h14803, hlam, p16359_1]
                        · have p16359_0 := h16359c.1
                          have p16359_1 := h16359c.2.1
                          have p16359_2 := h16359c.2.2.1
                          have p16359_3 := h16359c.2.2.2
                          linarith only [h15246, hlam, p16359_0]
                        · have p16359_0 := h16359c.1
                          have p16359_1 := h16359c.2.1
                          have p16359_2 := h16359c.2.2.1
                          have p16359_3 := h16359c.2.2.2
                          linarith only [h15483, h16302, h16353, hc01, hc23, hlam, hphi, ht12, p16359_1]
                        · have p16359_0 := h16359c.1
                          have p16359_1 := h16359c.2.1
                          have p16359_2 := h16359c.2.2.1
                          have p16359_3 := h16359c.2.2.2
                          linarith only [h15483, h16302, h16353, hc02, hc23, hlam, hphi, p16359_1]
                        · have p16359_0 := h16359c.1
                          have p16359_1 := h16359c.2.1
                          have p16359_2 := h16359c.2.2.1
                          have p16359_3 := h16359c.2.2.2
                          linarith only [hlam, p16359_0]
                        · have p16359_0 := h16359c.1
                          have p16359_1 := h16359c.2.1
                          have p16359_2 := h16359c.2.2.1
                          have p16359_3 := h16359c.2.2.2
                          linarith only [h15483, hlam, p16359_1]
                        · have p16359_0 := h16359c.1
                          have p16359_1 := h16359c.2.1
                          have p16359_2 := h16359c.2.2.1
                          have p16359_3 := h16359c.2.2.2
                          linarith only [h15483, h16302, h16353, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p16359_1]
                        · have p16359_0 := h16359c.1
                          have p16359_1 := h16359c.2.1
                          have p16359_2 := h16359c.2.2.1
                          have p16359_3 := h16359c.2.2.2
                          linarith only [h15483, h16302, h16353, hc01, hc23, hlam, hphi, ht12, p16359_1]
                        · have p16359_0 := h16359c.1
                          have p16359_1 := h16359c.2.1
                          have p16359_2 := h16359c.2.2.1
                          have p16359_3 := h16359c.2.2.2
                          linarith only [h0, h15483, h16302, h16353, hc01, hc23, hlam, hphi, ht12, p16359_1]
                        · have p16359_0 := h16359c.1
                          have p16359_1 := h16359c.2.1
                          have p16359_2 := h16359c.2.2.1
                          have p16359_3 := h16359c.2.2.2
                          linarith only [h15483, h16300, h16302, h16353, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p16359_1]
                        · have p16359_0 := h16359c.1
                          have p16359_1 := h16359c.2.1
                          have p16359_2 := h16359c.2.2.1
                          have p16359_3 := h16359c.2.2.2
                          linarith only [hlam, p16359_0]
                        · have p16359_0 := h16359c.1
                          have p16359_1 := h16359c.2.1
                          have p16359_2 := h16359c.2.2.1
                          have p16359_3 := h16359c.2.2.2
                          linarith only [h0, h15246, h15483, h16302, h16353, hc01, hc23, hlam, hphi, ht12, p16359_1]
                        · have p16359_0 := h16359c.1
                          have p16359_1 := h16359c.2.1
                          have p16359_2 := h16359c.2.2.1
                          have p16359_3 := h16359c.2.2.2
                          linarith only [h15483, h16300, h16302, h16353, hc01, hc23, hlam, hphi, ht12, p16359_1]
                        · have p16359_0 := h16359c.1
                          have p16359_1 := h16359c.2.1
                          have p16359_2 := h16359c.2.2.1
                          have p16359_3 := h16359c.2.2.2
                          linarith only [h0, h15483, h16300, h16302, h16353, hc01, hc23, hlam, hphi, ht12, p16359_1]
                        · have p16359_0 := h16359c.1
                          have p16359_1 := h16359c.2.1
                          have p16359_2 := h16359c.2.2.1
                          have p16359_3 := h16359c.2.2.2
                          linarith only [h16300, hlam, p16359_0]
                        · have p16359_0 := h16359c.1
                          have p16359_1 := h16359c.2.1
                          have p16359_2 := h16359c.2.2.1
                          have p16359_3 := h16359c.2.2.2
                          linarith only [h16301, hlam, p16359_1]
                        · have p16359_0 := h16359c.1
                          have p16359_1 := h16359c.2.1
                          have p16359_2 := h16359c.2.2.1
                          have p16359_3 := h16359c.2.2.2
                          linarith only [hlam, p16359_0]
                      · linarith only [h15483, h16301, h16358, hlam]
                    · linarith only [h0, h14803, h15483, h16300, h16301, h16353, h16357, hc01, hc14, hlam, hphi]
                  · linarith only [h15483, h16302, h16353, h16356, hc03, hc35, hlam, hphi]
                · linarith only [h16302, h16353, h16355, hlam]
              · linarith only [h15483, h16300, h16301, h16353, h16354, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h16390 | h16390
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16391 | h16391
                · linarith only [h0, h16302, h16353, h16391, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h16302, h16391, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h10058, h15483, h16300, h16301, h16390, hc01, hc34, hlam, hphi, ht12, ht23]
    · linarith only [h15483, h16300, h16301, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h16396 | h16396
    · rcases m.htr 1 2 3 (by decide) (by decide) with h16397 | h16397
      · rcases m.htr 1 2 4 (by decide) (by decide) with h16398 | h16398
        · rcases m.htr 1 2 5 (by decide) (by decide) with h16399 | h16399
          · rcases m.htr 1 3 4 (by decide) (by decide) with h16400 | h16400
            · rcases m.htr 1 4 5 (by decide) (by decide) with h16401 | h16401
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16402 | h16402
                · linarith only [h15483, h16397, h16402, h6793, hc01, hc12, hlam, hphi]
                · linarith only [h0, h11558, h16397, h16400, h16402, hc01, hc12, hlam, hphi]
              · linarith only [h14803, h16396, h16398, h16401, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h16406 | h16406
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16407 | h16407
                · linarith only [h0, h11558, h15483, h16397, h16407, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h16409 | h16409
                  · linarith only [h0, h11558, h16300, h16397, h16400, h16409, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h16411 | h16411
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h16412 | h16412
                      · rcases h0bigk with h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c
                        · have p16413_0 := h16413c.1
                          have p16413_1 := h16413c.2.1
                          have p16413_2 := h16413c.2.2.1
                          have p16413_3 := h16413c.2.2.2
                          linarith only [hlam, p16413_0]
                        · have p16413_0 := h16413c.1
                          have p16413_1 := h16413c.2.1
                          have p16413_2 := h16413c.2.2.1
                          have p16413_3 := h16413c.2.2.2
                          linarith only [h0, hlam, p16413_1]
                        · have p16413_0 := h16413c.1
                          have p16413_1 := h16413c.2.1
                          have p16413_2 := h16413c.2.2.1
                          have p16413_3 := h16413c.2.2.2
                          linarith only [h6793, hlam, p16413_0]
                        · have p16413_0 := h16413c.1
                          have p16413_1 := h16413c.2.1
                          have p16413_2 := h16413c.2.2.1
                          have p16413_3 := h16413c.2.2.2
                          linarith only [h10058, hlam, p16413_1]
                        · have p16413_0 := h16413c.1
                          have p16413_1 := h16413c.2.1
                          have p16413_2 := h16413c.2.2.1
                          have p16413_3 := h16413c.2.2.2
                          linarith only [h11024, hlam, p16413_1]
                        · have p16413_0 := h16413c.1
                          have p16413_1 := h16413c.2.1
                          have p16413_2 := h16413c.2.2.1
                          have p16413_3 := h16413c.2.2.2
                          linarith only [h11558, hc01, hc23, hlam, hphi, ht12, p16413_1]
                        · have p16413_0 := h16413c.1
                          have p16413_1 := h16413c.2.1
                          have p16413_2 := h16413c.2.2.1
                          have p16413_3 := h16413c.2.2.2
                          linarith only [hlam, p16413_0]
                        · have p16413_0 := h16413c.1
                          have p16413_1 := h16413c.2.1
                          have p16413_2 := h16413c.2.2.1
                          have p16413_3 := h16413c.2.2.2
                          linarith only [h11558, hlam, p16413_0]
                        · have p16413_0 := h16413c.1
                          have p16413_1 := h16413c.2.1
                          have p16413_2 := h16413c.2.2.1
                          have p16413_3 := h16413c.2.2.2
                          linarith only [h14803, hlam, p16413_1]
                        · have p16413_0 := h16413c.1
                          have p16413_1 := h16413c.2.1
                          have p16413_2 := h16413c.2.2.1
                          have p16413_3 := h16413c.2.2.2
                          linarith only [h15246, hlam, p16413_0]
                        · have p16413_0 := h16413c.1
                          have p16413_1 := h16413c.2.1
                          have p16413_2 := h16413c.2.2.1
                          have p16413_3 := h16413c.2.2.2
                          linarith only [h16400, h6793, hc01, hc34, hlam, hphi, ht12, ht23, p16413_1]
                        · have p16413_0 := h16413c.1
                          have p16413_1 := h16413c.2.1
                          have p16413_2 := h16413c.2.2.1
                          have p16413_3 := h16413c.2.2.2
                          linarith only [h16400, h6793, hc02, hc34, hlam, hphi, ht23, p16413_1]
                        · have p16413_0 := h16413c.1
                          have p16413_1 := h16413c.2.1
                          have p16413_2 := h16413c.2.2.1
                          have p16413_3 := h16413c.2.2.2
                          linarith only [hlam, p16413_0]
                        · have p16413_0 := h16413c.1
                          have p16413_1 := h16413c.2.1
                          have p16413_2 := h16413c.2.2.1
                          have p16413_3 := h16413c.2.2.2
                          linarith only [h15483, hlam, p16413_1]
                        · have p16413_0 := h16413c.1
                          have p16413_1 := h16413c.2.1
                          have p16413_2 := h16413c.2.2.1
                          have p16413_3 := h16413c.2.2.2
                          linarith only [h16300, hlam, p16413_1]
                        · have p16413_0 := h16413c.1
                          have p16413_1 := h16413c.2.1
                          have p16413_2 := h16413c.2.2.1
                          have p16413_3 := h16413c.2.2.2
                          linarith only [h14803, h16398, hc01, hc12, hlam, hphi, p16413_1]
                        · have p16413_0 := h16413c.1
                          have p16413_1 := h16413c.2.1
                          have p16413_2 := h16413c.2.2.1
                          have p16413_3 := h16413c.2.2.2
                          linarith only [h0, h14803, h16398, hc01, hc12, hlam, hphi, p16413_1]
                        · have p16413_0 := h16413c.1
                          have p16413_1 := h16413c.2.1
                          have p16413_2 := h16413c.2.2.1
                          have p16413_3 := h16413c.2.2.2
                          linarith only [h14803, h16398, h6793, hc01, hc12, hlam, hphi, p16413_1]
                        · have p16413_0 := h16413c.1
                          have p16413_1 := h16413c.2.1
                          have p16413_2 := h16413c.2.2.1
                          have p16413_3 := h16413c.2.2.2
                          linarith only [hlam, p16413_0]
                        · have p16413_0 := h16413c.1
                          have p16413_1 := h16413c.2.1
                          have p16413_2 := h16413c.2.2.1
                          have p16413_3 := h16413c.2.2.2
                          linarith only [h11024, h14803, h16398, hc01, hc12, hlam, hphi, p16413_1]
                        · have p16413_0 := h16413c.1
                          have p16413_1 := h16413c.2.1
                          have p16413_2 := h16413c.2.2.1
                          have p16413_3 := h16413c.2.2.2
                          linarith only [h14803, h16396, h16398, hc01, hc12, hlam, hphi, p16413_1]
                        · have p16413_0 := h16413c.1
                          have p16413_1 := h16413c.2.1
                          have p16413_2 := h16413c.2.2.1
                          have p16413_3 := h16413c.2.2.2
                          linarith only [h0, h14803, h16396, h16398, hc01, hc12, hlam, hphi, p16413_1]
                        · have p16413_0 := h16413c.1
                          have p16413_1 := h16413c.2.1
                          have p16413_2 := h16413c.2.2.1
                          have p16413_3 := h16413c.2.2.2
                          linarith only [h0, h11558, h14803, h16396, h16398, hc01, hc12, hlam, hphi, p16413_1]
                        · have p16413_0 := h16413c.1
                          have p16413_1 := h16413c.2.1
                          have p16413_2 := h16413c.2.2.1
                          have p16413_3 := h16413c.2.2.2
                          linarith only [h16396, hlam, p16413_1]
                        · have p16413_0 := h16413c.1
                          have p16413_1 := h16413c.2.1
                          have p16413_2 := h16413c.2.2.1
                          have p16413_3 := h16413c.2.2.2
                          linarith only [hlam, p16413_0]
                      · linarith only [h14803, h16396, h16398, h16400, h16412, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h14803, h16396, h16411, hlam]
              · linarith only [h14803, h16396, h16398, h16406, hlam]
          · linarith only [h0, h14803, h16398, h16399, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h11558, h16397, h16398, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h16444 | h16444
        · linarith only [h0, h14803, h16397, h16444, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h16446 | h16446
          · linarith only [h0, h15246, h16397, h16446, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h16448 | h16448
            · rcases m.htr 1 4 5 (by decide) (by decide) with h16449 | h16449
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16450 | h16450
                · rcases m.htr 2 3 5 (by decide) (by decide) with h16451 | h16451
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h16452 | h16452
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h16453 | h16453
                      · rcases h0bigk with h16454c | h16454c | h16454c | h16454c | h16454c | h16454c | h16454c | h16454c | h16454c | h16454c | h16454c | h16454c | h16454c | h16454c | h16454c | h16454c | h16454c | h16454c | h16454c | h16454c | h16454c | h16454c | h16454c | h16454c | h16454c
                        · have p16454_0 := h16454c.1
                          have p16454_1 := h16454c.2.1
                          have p16454_2 := h16454c.2.2.1
                          have p16454_3 := h16454c.2.2.2
                          linarith only [hlam, p16454_0]
                        · have p16454_0 := h16454c.1
                          have p16454_1 := h16454c.2.1
                          have p16454_2 := h16454c.2.2.1
                          have p16454_3 := h16454c.2.2.2
                          linarith only [h0, hlam, p16454_1]
                        · have p16454_0 := h16454c.1
                          have p16454_1 := h16454c.2.1
                          have p16454_2 := h16454c.2.2.1
                          have p16454_3 := h16454c.2.2.2
                          linarith only [h6793, hlam, p16454_0]
                        · have p16454_0 := h16454c.1
                          have p16454_1 := h16454c.2.1
                          have p16454_2 := h16454c.2.2.1
                          have p16454_3 := h16454c.2.2.2
                          linarith only [h10058, hlam, p16454_1]
                        · have p16454_0 := h16454c.1
                          have p16454_1 := h16454c.2.1
                          have p16454_2 := h16454c.2.2.1
                          have p16454_3 := h16454c.2.2.2
                          linarith only [h11024, hlam, p16454_1]
                        · have p16454_0 := h16454c.1
                          have p16454_1 := h16454c.2.1
                          have p16454_2 := h16454c.2.2.1
                          have p16454_3 := h16454c.2.2.2
                          linarith only [h11558, h16300, h16448, h16453, hc01, hc13, hlam, hphi, p16454_1]
                        · have p16454_0 := h16454c.1
                          have p16454_1 := h16454c.2.1
                          have p16454_2 := h16454c.2.2.1
                          have p16454_3 := h16454c.2.2.2
                          linarith only [hlam, p16454_0]
                        · have p16454_0 := h16454c.1
                          have p16454_1 := h16454c.2.1
                          have p16454_2 := h16454c.2.2.1
                          have p16454_3 := h16454c.2.2.2
                          linarith only [h11558, hlam, p16454_0]
                        · have p16454_0 := h16454c.1
                          have p16454_1 := h16454c.2.1
                          have p16454_2 := h16454c.2.2.1
                          have p16454_3 := h16454c.2.2.2
                          linarith only [h14803, hlam, p16454_1]
                        · have p16454_0 := h16454c.1
                          have p16454_1 := h16454c.2.1
                          have p16454_2 := h16454c.2.2.1
                          have p16454_3 := h16454c.2.2.2
                          linarith only [h15246, hlam, p16454_0]
                        · have p16454_0 := h16454c.1
                          have p16454_1 := h16454c.2.1
                          have p16454_2 := h16454c.2.2.1
                          have p16454_3 := h16454c.2.2.2
                          linarith only [h16300, h16448, h16453, hc01, hc13, hlam, hphi, p16454_1]
                        · have p16454_0 := h16454c.1
                          have p16454_1 := h16454c.2.1
                          have p16454_2 := h16454c.2.2.1
                          have p16454_3 := h16454c.2.2.2
                          linarith only [h16300, h16448, h16453, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p16454_1]
                        · have p16454_0 := h16454c.1
                          have p16454_1 := h16454c.2.1
                          have p16454_2 := h16454c.2.2.1
                          have p16454_3 := h16454c.2.2.2
                          linarith only [hlam, p16454_0]
                        · have p16454_0 := h16454c.1
                          have p16454_1 := h16454c.2.1
                          have p16454_2 := h16454c.2.2.1
                          have p16454_3 := h16454c.2.2.2
                          linarith only [h15483, hlam, p16454_1]
                        · have p16454_0 := h16454c.1
                          have p16454_1 := h16454c.2.1
                          have p16454_2 := h16454c.2.2.1
                          have p16454_3 := h16454c.2.2.2
                          linarith only [h16300, hlam, p16454_1]
                        · have p16454_0 := h16454c.1
                          have p16454_1 := h16454c.2.1
                          have p16454_2 := h16454c.2.2.1
                          have p16454_3 := h16454c.2.2.2
                          linarith only [h15483, h16448, hc01, hc13, hlam, hphi, p16454_1]
                        · have p16454_0 := h16454c.1
                          have p16454_1 := h16454c.2.1
                          have p16454_2 := h16454c.2.2.1
                          have p16454_3 := h16454c.2.2.2
                          linarith only [h0, h15483, h16448, hc01, hc13, hlam, hphi, p16454_1]
                        · have p16454_0 := h16454c.1
                          have p16454_1 := h16454c.2.1
                          have p16454_2 := h16454c.2.2.1
                          have p16454_3 := h16454c.2.2.2
                          linarith only [h15483, h16448, h6793, hc01, hc13, hlam, hphi, p16454_1]
                        · have p16454_0 := h16454c.1
                          have p16454_1 := h16454c.2.1
                          have p16454_2 := h16454c.2.2.1
                          have p16454_3 := h16454c.2.2.2
                          linarith only [hlam, p16454_0]
                        · have p16454_0 := h16454c.1
                          have p16454_1 := h16454c.2.1
                          have p16454_2 := h16454c.2.2.1
                          have p16454_3 := h16454c.2.2.2
                          linarith only [h0, h11558, h15483, h16300, h16448, hc01, hc13, hlam, hphi, p16454_1]
                        · have p16454_0 := h16454c.1
                          have p16454_1 := h16454c.2.1
                          have p16454_2 := h16454c.2.2.1
                          have p16454_3 := h16454c.2.2.2
                          linarith only [h16300, h16448, h16453, hc01, hc13, hlam, hphi, p16454_1]
                        · have p16454_0 := h16454c.1
                          have p16454_1 := h16454c.2.1
                          have p16454_2 := h16454c.2.2.1
                          have p16454_3 := h16454c.2.2.2
                          linarith only [h0, h16300, h16448, h16453, hc01, hc13, hlam, hphi, p16454_1]
                        · have p16454_0 := h16454c.1
                          have p16454_1 := h16454c.2.1
                          have p16454_2 := h16454c.2.2.1
                          have p16454_3 := h16454c.2.2.2
                          linarith only [h0, h11558, h16300, h16448, h16453, hc01, hc13, hlam, hphi, p16454_1]
                        · have p16454_0 := h16454c.1
                          have p16454_1 := h16454c.2.1
                          have p16454_2 := h16454c.2.2.1
                          have p16454_3 := h16454c.2.2.2
                          linarith only [h16396, hlam, p16454_1]
                        · have p16454_0 := h16454c.1
                          have p16454_1 := h16454c.2.1
                          have p16454_2 := h16454c.2.2.1
                          have p16454_3 := h16454c.2.2.2
                          linarith only [hlam, p16454_0]
                      · linarith only [h15483, h16396, h16453, hlam]
                    · linarith only [h0, h14803, h15483, h16396, h16397, h16448, h16452, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h11558, h15483, h16397, h16448, h16451, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h16397, h16448, h16450, hlam]
              · linarith only [h0, h11558, h15483, h16396, h16448, h16449, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h16485 | h16485
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16486 | h16486
                · linarith only [h16448, h16486, h6793, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h16397, h16486, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h10058, h16396, h16485, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h16490 | h16490
      · rcases m.htr 1 2 4 (by decide) (by decide) with h16491 | h16491
        · rcases m.htr 1 2 5 (by decide) (by decide) with h16492 | h16492
          · rcases m.htr 1 3 4 (by decide) (by decide) with h16493 | h16493
            · rcases m.htr 1 4 5 (by decide) (by decide) with h16494 | h16494
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16495 | h16495
                · linarith only [h0, h11558, h15483, h16490, h16495, hc01, hc12, hlam, hphi]
                · linarith only [h0, h11558, h16493, h16495, hc01, hc13, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16498 | h16498
                · linarith only [h0, h11558, h15483, h16490, h16498, hc01, hc12, hlam, hphi]
                · linarith only [h0, h11558, h16493, h16494, h16498, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h16501 | h16501
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16502 | h16502
                · linarith only [h16493, h16502, h6793, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h16504 | h16504
                  · linarith only [h0, h11558, h16300, h16490, h16504, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h16506 | h16506
                    · linarith only [h0, h11558, h15483, h16396, h16491, h16506, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h14803, h16493, h16501, h16506, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16509 | h16509
                · linarith only [h0, h11558, h15483, h16490, h16509, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h16511 | h16511
                  · linarith only [h0, h11558, h16300, h16490, h16493, h16501, h16511, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h16513 | h16513
                    · linarith only [h16493, h16501, h16513, h6793, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h16515 | h16515
                      · linarith only [h0, h11558, h16490, h16493, h16501, h16515, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h11558, h16490, h16493, h16515, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h11558, h16490, h16492, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h11558, h16490, h16491, hc01, hc24, hlam, hphi, ht12]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h16520 | h16520
        · linarith only [h0, h14803, h16490, h16520, hc01, hc23, hlam, hphi, ht12]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h16522 | h16522
          · linarith only [h0, h15246, h16490, h16522, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h16524 | h16524
            · rcases m.htr 1 4 5 (by decide) (by decide) with h16525 | h16525
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16526 | h16526
                · rcases m.htr 2 3 5 (by decide) (by decide) with h16527 | h16527
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h16528 | h16528
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h16529 | h16529
                      · linarith only [h0, h11558, h15483, h16396, h16490, h16524, h16529, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h11558, h15483, h16490, h16524, h16525, h16529, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h14803, h16490, h16524, h16525, h16528, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h0, h11558, h15483, h16396, h16490, h16524, h16525, h16527, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h0, h11558, h15483, h16396, h16490, h16524, h16525, h16526, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16535 | h16535
                · rcases m.htr 2 3 5 (by decide) (by decide) with h16536 | h16536
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h16537 | h16537
                    · linarith only [h10058, h16525, h16537, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h16520, h16537, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h0, h16490, h16536, hc01, hc35, hlam, hphi, ht12, ht23]
                · linarith only [h16490, h16524, h16535, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h16542 | h16542
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16543 | h16543
                · linarith only [h16524, h16543, h6793, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h16490, h16543, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16546 | h16546
                · linarith only [h0, h16490, h16524, h16546, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h16490, h16546, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 9982000 in
set_option maxHeartbeats 9982000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s12_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg10058 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11024 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11558 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h14803 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h15246 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  rcases m.htr 0 3 4 (by decide) (by decide) with h15483 | h15483
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s12_x1_x1_x1_x0 m hb0 hb2 hb4 hg0 hg6793 hg10058 hg11024 h11558 h14803 h15246 h15483
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s12_x1_x1_x1_x1 m hb0 hb2 hb4 hg0 hg6793 hg10058 hg11024 h11558 h14803 h15246 h15483

set_option maxHeartbeats 9982000 in
set_option maxHeartbeats 9982000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s12_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg10058 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11024 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11558 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h14803 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h15246 | h15246
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s12_x1_x1_x0 m hb0 hb2 hb4 hg0 hg6793 hg10058 hg11024 h11558 h14803 h15246
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s12_x1_x1_x1 m hb0 hb2 hb4 hg0 hg6793 hg10058 hg11024 h11558 h14803 h15246

set_option maxHeartbeats 9982000 in
set_option maxHeartbeats 9982000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s12_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg10058 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11024 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11558 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h14803 | h14803
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s12_x1_x0 m hb0 hb2 hb4 hg0 hg6793 hg10058 hg11024 h11558 h14803
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s12_x1_x1 m hb0 hb2 hb4 hg0 hg6793 hg10058 hg11024 h11558 h14803

set_option maxHeartbeats 9982000 in
set_option maxHeartbeats 9982000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s12 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg10058 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11024 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  rcases m.htr 0 2 3 (by decide) (by decide) with h11558 | h11558
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s12_x0 m hb0 hb2 hb4 hg0 hg6793 hg10058 hg11024 h11558
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s12_x1 m hb0 hb2 hb4 hg0 hg6793 hg10058 hg11024 h11558

end R2N4
