import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6812000 in
theorem r1l7_11_12_25_L_0_L_I_H_I_x0_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h1 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h1158 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 1 2 5 (by decide) (by decide) with h1159 | h1159
  · linarith only [h0, h1, h1159, hlam]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1161 | h1161
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1162 | h1162
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1163 | h1163
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1164 | h1164
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1165 | h1165
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1166 | h1166
              · rcases h5bigk with h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c
                · have p1167_0 := h1167c.1
                  have p1167_1 := h1167c.2.1
                  have p1167_2 := h1167c.2.2.1
                  have p1167_3 := h1167c.2.2.2
                  linarith only [hlam, p1167_0]
                · have p1167_0 := h1167c.1
                  have p1167_1 := h1167c.2.1
                  have p1167_2 := h1167c.2.2.1
                  have p1167_3 := h1167c.2.2.2
                  linarith only [h0, h1161, h1166, hc45, hlam, hphi, ht01, ht0b, ht5b, p1167_1, u1elo0]
                · have p1167_0 := h1167c.1
                  have p1167_1 := h1167c.2.1
                  have p1167_2 := h1167c.2.2.1
                  have p1167_3 := h1167c.2.2.2
                  linarith only [h1, hlam, p1167_0]
                · have p1167_0 := h1167c.1
                  have p1167_1 := h1167c.2.1
                  have p1167_2 := h1167c.2.2.1
                  have p1167_3 := h1167c.2.2.2
                  linarith only [h0, h1166, hc45, hlam, hphi, ht01, ht0b, ht5b, p1167_1, u1elo0]
                · have p1167_0 := h1167c.1
                  have p1167_1 := h1167c.2.1
                  have p1167_2 := h1167c.2.2.1
                  have p1167_3 := h1167c.2.2.2
                  linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p1167_1, u1elo0]
                · have p1167_0 := h1167c.1
                  have p1167_1 := h1167c.2.1
                  have p1167_2 := h1167c.2.2.1
                  have p1167_3 := h1167c.2.2.2
                  linarith only [h0, hlam, p1167_0]
                · have p1167_0 := h1167c.1
                  have p1167_1 := h1167c.2.1
                  have p1167_2 := h1167c.2.2.1
                  have p1167_3 := h1167c.2.2.2
                  linarith only [hlam, p1167_0]
                · have p1167_0 := h1167c.1
                  have p1167_1 := h1167c.2.1
                  have p1167_2 := h1167c.2.2.1
                  have p1167_3 := h1167c.2.2.2
                  linarith only [h1159, hlam, p1167_0]
                · have p1167_0 := h1167c.1
                  have p1167_1 := h1167c.2.1
                  have p1167_2 := h1167c.2.2.1
                  have p1167_3 := h1167c.2.2.2
                  linarith only [h1166, hc45, hlam, hphi, ht01, ht0b, ht5b, p1167_1, u1elo4]
                · have p1167_0 := h1167c.1
                  have p1167_1 := h1167c.2.1
                  have p1167_2 := h1167c.2.2.1
                  have p1167_3 := h1167c.2.2.2
                  linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p1167_1, u1elo0]
                · have p1167_0 := h1167c.1
                  have p1167_1 := h1167c.2.1
                  have p1167_2 := h1167c.2.2.1
                  have p1167_3 := h1167c.2.2.2
                  linarith only [h1, h1163, h1165, hc02, hc23, hlam, hphi, p1167_1]
                · have p1167_0 := h1167c.1
                  have p1167_1 := h1167c.2.1
                  have p1167_2 := h1167c.2.2.1
                  have p1167_3 := h1167c.2.2.2
                  linarith only [h1159, h1163, h1165, hc12, hc23, hlam, hphi, p1167_1]
                · have p1167_0 := h1167c.1
                  have p1167_1 := h1167c.2.1
                  have p1167_2 := h1167c.2.2.1
                  have p1167_3 := h1167c.2.2.2
                  linarith only [hlam, p1167_0]
                · have p1167_0 := h1167c.1
                  have p1167_1 := h1167c.2.1
                  have p1167_2 := h1167c.2.2.1
                  have p1167_3 := h1167c.2.2.2
                  rcases p1167_3 (m.d 0 5) (by simp) with h1181 | h1181
                  · linarith only [h1, h1181, hlam]
                  · linarith only [h0, h1161, h1181, hlam]
                · have p1167_0 := h1167c.1
                  have p1167_1 := h1167c.2.1
                  have p1167_2 := h1167c.2.2.1
                  have p1167_3 := h1167c.2.2.2
                  rcases p1167_3 (m.d 0 5) (by simp) with h1184 | h1184
                  · linarith only [h1, h1184, hlam]
                  · linarith only [h1158, h1184, hlam]
                · have p1167_0 := h1167c.1
                  have p1167_1 := h1167c.2.1
                  have p1167_2 := h1167c.2.2.1
                  have p1167_3 := h1167c.2.2.2
                  linarith only [h0, h1161, hlam, p1167_1]
                · have p1167_0 := h1167c.1
                  have p1167_1 := h1167c.2.1
                  have p1167_2 := h1167c.2.2.1
                  have p1167_3 := h1167c.2.2.2
                  linarith only [h1161, hlam, p1167_1]
                · have p1167_0 := h1167c.1
                  have p1167_1 := h1167c.2.1
                  have p1167_2 := h1167c.2.2.1
                  have p1167_3 := h1167c.2.2.2
                  linarith only [h1164, hlam, p1167_0]
                · have p1167_0 := h1167c.1
                  have p1167_1 := h1167c.2.1
                  have p1167_2 := h1167c.2.2.1
                  have p1167_3 := h1167c.2.2.2
                  linarith only [hlam, p1167_0]
                · have p1167_0 := h1167c.1
                  have p1167_1 := h1167c.2.1
                  have p1167_2 := h1167c.2.2.1
                  have p1167_3 := h1167c.2.2.2
                  linarith only [h1161, hc45, hlam, hphi, ht01, ht0b, ht5b, p1167_1, u1elo2]
                · have p1167_0 := h1167c.1
                  have p1167_1 := h1167c.2.1
                  have p1167_2 := h1167c.2.2.1
                  have p1167_3 := h1167c.2.2.2
                  linarith only [h1158, hlam, p1167_1]
                · have p1167_0 := h1167c.1
                  have p1167_1 := h1167c.2.1
                  have p1167_2 := h1167c.2.2.1
                  have p1167_3 := h1167c.2.2.2
                  linarith only [h1162, hlam, p1167_1]
                · have p1167_0 := h1167c.1
                  have p1167_1 := h1167c.2.1
                  have p1167_2 := h1167c.2.2.1
                  have p1167_3 := h1167c.2.2.2
                  linarith only [h1165, hlam, p1167_1]
                · have p1167_0 := h1167c.1
                  have p1167_1 := h1167c.2.1
                  have p1167_2 := h1167c.2.2.1
                  have p1167_3 := h1167c.2.2.2
                  linarith only [h1166, hlam, p1167_1]
                · have p1167_0 := h1167c.1
                  have p1167_1 := h1167c.2.1
                  have p1167_2 := h1167c.2.2.1
                  have p1167_3 := h1167c.2.2.2
                  linarith only [hlam, p1167_0]
              · rcases h5bigk with h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c
                · have p1197_0 := h1197c.1
                  have p1197_1 := h1197c.2.1
                  have p1197_2 := h1197c.2.2.1
                  have p1197_3 := h1197c.2.2.2
                  linarith only [hlam, p1197_0]
                · have p1197_0 := h1197c.1
                  have p1197_1 := h1197c.2.1
                  have p1197_2 := h1197c.2.2.1
                  have p1197_3 := h1197c.2.2.2
                  linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p1197_1, u1elo0]
                · have p1197_0 := h1197c.1
                  have p1197_1 := h1197c.2.1
                  have p1197_2 := h1197c.2.2.1
                  have p1197_3 := h1197c.2.2.2
                  linarith only [h1, hlam, p1197_0]
                · have p1197_0 := h1197c.1
                  have p1197_1 := h1197c.2.1
                  have p1197_2 := h1197c.2.2.1
                  have p1197_3 := h1197c.2.2.2
                  linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p1197_1, u1elo0]
                · have p1197_0 := h1197c.1
                  have p1197_1 := h1197c.2.1
                  have p1197_2 := h1197c.2.2.1
                  have p1197_3 := h1197c.2.2.2
                  linarith only [h0, h1166, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1197_1, u1elo0]
                · have p1197_0 := h1197c.1
                  have p1197_1 := h1197c.2.1
                  have p1197_2 := h1197c.2.2.1
                  have p1197_3 := h1197c.2.2.2
                  linarith only [h0, hlam, p1197_0]
                · have p1197_0 := h1197c.1
                  have p1197_1 := h1197c.2.1
                  have p1197_2 := h1197c.2.2.1
                  have p1197_3 := h1197c.2.2.2
                  linarith only [hlam, p1197_0]
                · have p1197_0 := h1197c.1
                  have p1197_1 := h1197c.2.1
                  have p1197_2 := h1197c.2.2.1
                  have p1197_3 := h1197c.2.2.2
                  linarith only [h1159, hlam, p1197_0]
                · have p1197_0 := h1197c.1
                  have p1197_1 := h1197c.2.1
                  have p1197_2 := h1197c.2.2.1
                  have p1197_3 := h1197c.2.2.2
                  linarith only [hc35, hlam, hphi, ht01, ht0b, ht5b, p1197_1, u1elo4]
                · have p1197_0 := h1197c.1
                  have p1197_1 := h1197c.2.1
                  have p1197_2 := h1197c.2.2.1
                  have p1197_3 := h1197c.2.2.2
                  linarith only [h0, h1166, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1197_1, u1elo0]
                · have p1197_0 := h1197c.1
                  have p1197_1 := h1197c.2.1
                  have p1197_2 := h1197c.2.2.1
                  have p1197_3 := h1197c.2.2.2
                  linarith only [h1, h1163, h1165, hc02, hc23, hlam, hphi, p1197_1]
                · have p1197_0 := h1197c.1
                  have p1197_1 := h1197c.2.1
                  have p1197_2 := h1197c.2.2.1
                  have p1197_3 := h1197c.2.2.2
                  linarith only [h1159, h1163, h1165, hc12, hc23, hlam, hphi, p1197_1]
                · have p1197_0 := h1197c.1
                  have p1197_1 := h1197c.2.1
                  have p1197_2 := h1197c.2.2.1
                  have p1197_3 := h1197c.2.2.2
                  linarith only [hlam, p1197_0]
                · have p1197_0 := h1197c.1
                  have p1197_1 := h1197c.2.1
                  have p1197_2 := h1197c.2.2.1
                  have p1197_3 := h1197c.2.2.2
                  rcases p1197_3 (m.d 0 5) (by simp) with h1211 | h1211
                  · linarith only [h1, h1211, hlam]
                  · linarith only [h0, h1161, h1211, hlam]
                · have p1197_0 := h1197c.1
                  have p1197_1 := h1197c.2.1
                  have p1197_2 := h1197c.2.2.1
                  have p1197_3 := h1197c.2.2.2
                  linarith only [h1163, h1165, h1166, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1197_1]
                · have p1197_0 := h1197c.1
                  have p1197_1 := h1197c.2.1
                  have p1197_2 := h1197c.2.2.1
                  have p1197_3 := h1197c.2.2.2
                  linarith only [h0, h1162, h1166, hlam, p1197_1]
                · have p1197_0 := h1197c.1
                  have p1197_1 := h1197c.2.1
                  have p1197_2 := h1197c.2.2.1
                  have p1197_3 := h1197c.2.2.2
                  linarith only [h1161, hlam, p1197_1]
                · have p1197_0 := h1197c.1
                  have p1197_1 := h1197c.2.1
                  have p1197_2 := h1197c.2.2.1
                  have p1197_3 := h1197c.2.2.2
                  linarith only [h1164, hlam, p1197_0]
                · have p1197_0 := h1197c.1
                  have p1197_1 := h1197c.2.1
                  have p1197_2 := h1197c.2.2.1
                  have p1197_3 := h1197c.2.2.2
                  linarith only [hlam, p1197_0]
                · have p1197_0 := h1197c.1
                  have p1197_1 := h1197c.2.1
                  have p1197_2 := h1197c.2.2.1
                  have p1197_3 := h1197c.2.2.2
                  linarith only [h1166, hlam, p1197_0]
                · have p1197_0 := h1197c.1
                  have p1197_1 := h1197c.2.1
                  have p1197_2 := h1197c.2.2.1
                  have p1197_3 := h1197c.2.2.2
                  linarith only [h1158, hlam, p1197_1]
                · have p1197_0 := h1197c.1
                  have p1197_1 := h1197c.2.1
                  have p1197_2 := h1197c.2.2.1
                  have p1197_3 := h1197c.2.2.2
                  linarith only [h1162, hlam, p1197_1]
                · have p1197_0 := h1197c.1
                  have p1197_1 := h1197c.2.1
                  have p1197_2 := h1197c.2.2.1
                  have p1197_3 := h1197c.2.2.2
                  linarith only [h1165, hlam, p1197_1]
                · have p1197_0 := h1197c.1
                  have p1197_1 := h1197c.2.1
                  have p1197_2 := h1197c.2.2.1
                  have p1197_3 := h1197c.2.2.2
                  linarith only [h1162, hc35, hlam, hphi, ht01, ht0b, ht5b, p1197_1, u1elo3]
                · have p1197_0 := h1197c.1
                  have p1197_1 := h1197c.2.1
                  have p1197_2 := h1197c.2.2.1
                  have p1197_3 := h1197c.2.2.2
                  linarith only [hlam, p1197_0]
            · linarith only [h0, h1, h1162, h1165, hlam]
          · linarith only [h0, h1161, h1163, h1164, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1227 | h1227
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1228 | h1228
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1229 | h1229
              · rcases h5bigk with h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c | h1230c
                · have p1230_0 := h1230c.1
                  have p1230_1 := h1230c.2.1
                  have p1230_2 := h1230c.2.2.1
                  have p1230_3 := h1230c.2.2.2
                  linarith only [hlam, p1230_0]
                · have p1230_0 := h1230c.1
                  have p1230_1 := h1230c.2.1
                  have p1230_2 := h1230c.2.2.1
                  have p1230_3 := h1230c.2.2.2
                  linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p1230_1, u1elo0]
                · have p1230_0 := h1230c.1
                  have p1230_1 := h1230c.2.1
                  have p1230_2 := h1230c.2.2.1
                  have p1230_3 := h1230c.2.2.2
                  linarith only [h1, hlam, p1230_0]
                · have p1230_0 := h1230c.1
                  have p1230_1 := h1230c.2.1
                  have p1230_2 := h1230c.2.2.1
                  have p1230_3 := h1230c.2.2.2
                  linarith only [h1, h1163, h1227, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1230_1]
                · have p1230_0 := h1230c.1
                  have p1230_1 := h1230c.2.1
                  have p1230_2 := h1230c.2.2.1
                  have p1230_3 := h1230c.2.2.2
                  linarith only [h1, h1163, h1227, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1230_1]
                · have p1230_0 := h1230c.1
                  have p1230_1 := h1230c.2.1
                  have p1230_2 := h1230c.2.2.1
                  have p1230_3 := h1230c.2.2.2
                  linarith only [h0, hlam, p1230_0]
                · have p1230_0 := h1230c.1
                  have p1230_1 := h1230c.2.1
                  have p1230_2 := h1230c.2.2.1
                  have p1230_3 := h1230c.2.2.2
                  linarith only [hlam, p1230_0]
                · have p1230_0 := h1230c.1
                  have p1230_1 := h1230c.2.1
                  have p1230_2 := h1230c.2.2.1
                  have p1230_3 := h1230c.2.2.2
                  linarith only [h1159, hlam, p1230_0]
                · have p1230_0 := h1230c.1
                  have p1230_1 := h1230c.2.1
                  have p1230_2 := h1230c.2.2.1
                  have p1230_3 := h1230c.2.2.2
                  linarith only [h1229, hc45, hlam, hphi, ht01, ht0b, ht5b, p1230_1, u1elo4]
                · have p1230_0 := h1230c.1
                  have p1230_1 := h1230c.2.1
                  have p1230_2 := h1230c.2.2.1
                  have p1230_3 := h1230c.2.2.2
                  linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p1230_1, u1elo0]
                · have p1230_0 := h1230c.1
                  have p1230_1 := h1230c.2.1
                  have p1230_2 := h1230c.2.2.1
                  have p1230_3 := h1230c.2.2.2
                  linarith only [h1163, h1227, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1230_1]
                · have p1230_0 := h1230c.1
                  have p1230_1 := h1230c.2.1
                  have p1230_2 := h1230c.2.2.1
                  have p1230_3 := h1230c.2.2.2
                  linarith only [h1163, h1227, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1230_1]
                · have p1230_0 := h1230c.1
                  have p1230_1 := h1230c.2.1
                  have p1230_2 := h1230c.2.2.1
                  have p1230_3 := h1230c.2.2.2
                  linarith only [hlam, p1230_0]
                · have p1230_0 := h1230c.1
                  have p1230_1 := h1230c.2.1
                  have p1230_2 := h1230c.2.2.1
                  have p1230_3 := h1230c.2.2.2
                  linarith only [h1163, h1227, h1229, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1230_1]
                · have p1230_0 := h1230c.1
                  have p1230_1 := h1230c.2.1
                  have p1230_2 := h1230c.2.2.1
                  have p1230_3 := h1230c.2.2.2
                  linarith only [h1163, h1227, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1230_1]
                · have p1230_0 := h1230c.1
                  have p1230_1 := h1230c.2.1
                  have p1230_2 := h1230c.2.2.1
                  have p1230_3 := h1230c.2.2.2
                  linarith only [h0, h1159, hc12, hc35, hlam, hphi, ht23, p1230_1]
                · have p1230_0 := h1230c.1
                  have p1230_1 := h1230c.2.1
                  have p1230_2 := h1230c.2.2.1
                  have p1230_3 := h1230c.2.2.2
                  linarith only [h1161, hlam, p1230_1]
                · have p1230_0 := h1230c.1
                  have p1230_1 := h1230c.2.1
                  have p1230_2 := h1230c.2.2.1
                  have p1230_3 := h1230c.2.2.2
                  linarith only [h1227, hlam, p1230_0]
                · have p1230_0 := h1230c.1
                  have p1230_1 := h1230c.2.1
                  have p1230_2 := h1230c.2.2.1
                  have p1230_3 := h1230c.2.2.2
                  linarith only [hlam, p1230_0]
                · have p1230_0 := h1230c.1
                  have p1230_1 := h1230c.2.1
                  have p1230_2 := h1230c.2.2.1
                  have p1230_3 := h1230c.2.2.2
                  linarith only [h1161, hc45, hlam, hphi, ht01, ht0b, ht5b, p1230_1, u1elo4]
                · have p1230_0 := h1230c.1
                  have p1230_1 := h1230c.2.1
                  have p1230_2 := h1230c.2.2.1
                  have p1230_3 := h1230c.2.2.2
                  linarith only [h1158, hlam, p1230_1]
                · have p1230_0 := h1230c.1
                  have p1230_1 := h1230c.2.1
                  have p1230_2 := h1230c.2.2.1
                  have p1230_3 := h1230c.2.2.2
                  linarith only [h1162, hlam, p1230_1]
                · have p1230_0 := h1230c.1
                  have p1230_1 := h1230c.2.1
                  have p1230_2 := h1230c.2.2.1
                  have p1230_3 := h1230c.2.2.2
                  linarith only [h1228, hlam, p1230_1]
                · have p1230_0 := h1230c.1
                  have p1230_1 := h1230c.2.1
                  have p1230_2 := h1230c.2.2.1
                  have p1230_3 := h1230c.2.2.2
                  linarith only [h1229, hlam, p1230_1]
                · have p1230_0 := h1230c.1
                  have p1230_1 := h1230c.2.1
                  have p1230_2 := h1230c.2.2.1
                  have p1230_3 := h1230c.2.2.2
                  linarith only [hlam, p1230_0]
              · linarith only [h1, h1163, h1227, h1229, hc02, hc45, hlam, hphi, ht23, ht34]
            · linarith only [h0, h1, h1162, h1163, h1227, h1228, hlam]
          · linarith only [h0, h1, h1161, h1227, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1259 | h1259
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1260 | h1260
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1261 | h1261
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1262 | h1262
              · linarith only [h1161, h1162, h1262, hlam]
              · rcases h5bigk with h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c
                · have p1264_0 := h1264c.1
                  have p1264_1 := h1264c.2.1
                  have p1264_2 := h1264c.2.2.1
                  have p1264_3 := h1264c.2.2.2
                  linarith only [hlam, p1264_0]
                · have p1264_0 := h1264c.1
                  have p1264_1 := h1264c.2.1
                  have p1264_2 := h1264c.2.2.1
                  have p1264_3 := h1264c.2.2.2
                  linarith only [h0, h1161, hc35, hlam, hphi, ht01, ht0b, ht5b, p1264_1, u1elo0]
                · have p1264_0 := h1264c.1
                  have p1264_1 := h1264c.2.1
                  have p1264_2 := h1264c.2.2.1
                  have p1264_3 := h1264c.2.2.2
                  linarith only [h1, hlam, p1264_0]
                · have p1264_0 := h1264c.1
                  have p1264_1 := h1264c.2.1
                  have p1264_2 := h1264c.2.2.1
                  have p1264_3 := h1264c.2.2.2
                  linarith only [h0, h1262, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1264_1, u1elo0]
                · have p1264_0 := h1264c.1
                  have p1264_1 := h1264c.2.1
                  have p1264_2 := h1264c.2.2.1
                  have p1264_3 := h1264c.2.2.2
                  linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p1264_1, u1elo0]
                · have p1264_0 := h1264c.1
                  have p1264_1 := h1264c.2.1
                  have p1264_2 := h1264c.2.2.1
                  have p1264_3 := h1264c.2.2.2
                  linarith only [h0, hlam, p1264_0]
                · have p1264_0 := h1264c.1
                  have p1264_1 := h1264c.2.1
                  have p1264_2 := h1264c.2.2.1
                  have p1264_3 := h1264c.2.2.2
                  linarith only [hlam, p1264_0]
                · have p1264_0 := h1264c.1
                  have p1264_1 := h1264c.2.1
                  have p1264_2 := h1264c.2.2.1
                  have p1264_3 := h1264c.2.2.2
                  linarith only [h1159, hlam, p1264_0]
                · have p1264_0 := h1264c.1
                  have p1264_1 := h1264c.2.1
                  have p1264_2 := h1264c.2.2.1
                  have p1264_3 := h1264c.2.2.2
                  linarith only [h1262, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1264_1, u1elo4]
                · have p1264_0 := h1264c.1
                  have p1264_1 := h1264c.2.1
                  have p1264_2 := h1264c.2.2.1
                  have p1264_3 := h1264c.2.2.2
                  linarith only [h1162, hlam, p1264_0]
                · have p1264_0 := h1264c.1
                  have p1264_1 := h1264c.2.1
                  have p1264_2 := h1264c.2.2.1
                  have p1264_3 := h1264c.2.2.2
                  linarith only [h1, hc02, hc25, hlam, hphi, p1264_1]
                · have p1264_0 := h1264c.1
                  have p1264_1 := h1264c.2.1
                  have p1264_2 := h1264c.2.2.1
                  have p1264_3 := h1264c.2.2.2
                  linarith only [h1159, hc12, hc25, hlam, hphi, p1264_1]
                · have p1264_0 := h1264c.1
                  have p1264_1 := h1264c.2.1
                  have p1264_2 := h1264c.2.2.1
                  have p1264_3 := h1264c.2.2.2
                  linarith only [hlam, p1264_0]
                · have p1264_0 := h1264c.1
                  have p1264_1 := h1264c.2.1
                  have p1264_2 := h1264c.2.2.1
                  have p1264_3 := h1264c.2.2.2
                  rcases p1264_3 (m.d 0 5) (by simp) with h1278 | h1278
                  · linarith only [h1, h1278, hlam]
                  · linarith only [h0, h1161, h1278, hlam]
                · have p1264_0 := h1264c.1
                  have p1264_1 := h1264c.2.1
                  have p1264_2 := h1264c.2.2.1
                  have p1264_3 := h1264c.2.2.2
                  linarith only [h1159, h1162, h1259, h1261, hc12, hc23, hlam, hphi, p1264_1]
                · have p1264_0 := h1264c.1
                  have p1264_1 := h1264c.2.1
                  have p1264_2 := h1264c.2.2.1
                  have p1264_3 := h1264c.2.2.2
                  linarith only [h1158, h1161, h1162, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1264_1, u1elo4]
                · have p1264_0 := h1264c.1
                  have p1264_1 := h1264c.2.1
                  have p1264_2 := h1264c.2.2.1
                  have p1264_3 := h1264c.2.2.2
                  linarith only [h1161, hlam, p1264_1]
                · have p1264_0 := h1264c.1
                  have p1264_1 := h1264c.2.1
                  have p1264_2 := h1264c.2.2.1
                  have p1264_3 := h1264c.2.2.2
                  linarith only [h1260, hlam, p1264_0]
                · have p1264_0 := h1264c.1
                  have p1264_1 := h1264c.2.1
                  have p1264_2 := h1264c.2.2.1
                  have p1264_3 := h1264c.2.2.2
                  linarith only [hlam, p1264_0]
                · have p1264_0 := h1264c.1
                  have p1264_1 := h1264c.2.1
                  have p1264_2 := h1264c.2.2.1
                  have p1264_3 := h1264c.2.2.2
                  linarith only [h1262, hlam, p1264_0]
                · have p1264_0 := h1264c.1
                  have p1264_1 := h1264c.2.1
                  have p1264_2 := h1264c.2.2.1
                  have p1264_3 := h1264c.2.2.2
                  linarith only [h1158, hlam, p1264_1]
                · have p1264_0 := h1264c.1
                  have p1264_1 := h1264c.2.1
                  have p1264_2 := h1264c.2.2.1
                  have p1264_3 := h1264c.2.2.2
                  linarith only [h1158, hc04, hc15, hlam, hphi, ht0b, ht5b, p1264_1]
                · have p1264_0 := h1264c.1
                  have p1264_1 := h1264c.2.1
                  have p1264_2 := h1264c.2.2.1
                  have p1264_3 := h1264c.2.2.2
                  linarith only [h1261, hlam, p1264_1]
                · have p1264_0 := h1264c.1
                  have p1264_1 := h1264c.2.1
                  have p1264_2 := h1264c.2.2.1
                  have p1264_3 := h1264c.2.2.2
                  linarith only [h1259, h1261, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1264_1]
                · have p1264_0 := h1264c.1
                  have p1264_1 := h1264c.2.1
                  have p1264_2 := h1264c.2.2.1
                  have p1264_3 := h1264c.2.2.2
                  linarith only [hlam, p1264_0]
            · linarith only [h1, h1158, h1261, hlam]
          · linarith only [h0, h1161, h1259, h1260, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1294 | h1294
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1295 | h1295
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1296 | h1296
              · linarith only [h1161, h1162, h1296, hlam]
              · linarith only [h1259, h1294, h1295, h1296, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · linarith only [h1, h1158, h1259, h1294, h1295, hlam]
          · linarith only [h1, h1158, h1161, h1162, h1294, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1301 | h1301
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1302 | h1302
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1303 | h1303
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1304 | h1304
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1305 | h1305
              · rcases h5bigk with h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c
                · have p1306_0 := h1306c.1
                  have p1306_1 := h1306c.2.1
                  have p1306_2 := h1306c.2.2.1
                  have p1306_3 := h1306c.2.2.2
                  linarith only [hlam, p1306_0]
                · have p1306_0 := h1306c.1
                  have p1306_1 := h1306c.2.1
                  have p1306_2 := h1306c.2.2.1
                  have p1306_3 := h1306c.2.2.2
                  linarith only [h0, h1301, hc45, hlam, hphi, ht01, ht0b, ht5b, p1306_1, u1elo0]
                · have p1306_0 := h1306c.1
                  have p1306_1 := h1306c.2.1
                  have p1306_2 := h1306c.2.2.1
                  have p1306_3 := h1306c.2.2.2
                  linarith only [h1, hlam, p1306_0]
                · have p1306_0 := h1306c.1
                  have p1306_1 := h1306c.2.1
                  have p1306_2 := h1306c.2.2.1
                  have p1306_3 := h1306c.2.2.2
                  linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p1306_1, u1elo0]
                · have p1306_0 := h1306c.1
                  have p1306_1 := h1306c.2.1
                  have p1306_2 := h1306c.2.2.1
                  have p1306_3 := h1306c.2.2.2
                  linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p1306_1, u1elo0]
                · have p1306_0 := h1306c.1
                  have p1306_1 := h1306c.2.1
                  have p1306_2 := h1306c.2.2.1
                  have p1306_3 := h1306c.2.2.2
                  linarith only [h0, hlam, p1306_0]
                · have p1306_0 := h1306c.1
                  have p1306_1 := h1306c.2.1
                  have p1306_2 := h1306c.2.2.1
                  have p1306_3 := h1306c.2.2.2
                  linarith only [hlam, p1306_0]
                · have p1306_0 := h1306c.1
                  have p1306_1 := h1306c.2.1
                  have p1306_2 := h1306c.2.2.1
                  have p1306_3 := h1306c.2.2.2
                  linarith only [h1159, hlam, p1306_0]
                · have p1306_0 := h1306c.1
                  have p1306_1 := h1306c.2.1
                  have p1306_2 := h1306c.2.2.1
                  have p1306_3 := h1306c.2.2.2
                  linarith only [h1161, hlam, p1306_0]
                · have p1306_0 := h1306c.1
                  have p1306_1 := h1306c.2.1
                  have p1306_2 := h1306c.2.2.1
                  have p1306_3 := h1306c.2.2.2
                  linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p1306_1, u1elo4]
                · have p1306_0 := h1306c.1
                  have p1306_1 := h1306c.2.1
                  have p1306_2 := h1306c.2.2.1
                  have p1306_3 := h1306c.2.2.2
                  linarith only [h1, h1304, hc02, hc24, hlam, hphi, p1306_1]
                · have p1306_0 := h1306c.1
                  have p1306_1 := h1306c.2.1
                  have p1306_2 := h1306c.2.2.1
                  have p1306_3 := h1306c.2.2.2
                  linarith only [h1159, h1304, hc12, hc24, hlam, hphi, p1306_1]
                · have p1306_0 := h1306c.1
                  have p1306_1 := h1306c.2.1
                  have p1306_2 := h1306c.2.2.1
                  have p1306_3 := h1306c.2.2.2
                  linarith only [hlam, p1306_0]
                · have p1306_0 := h1306c.1
                  have p1306_1 := h1306c.2.1
                  have p1306_2 := h1306c.2.2.1
                  have p1306_3 := h1306c.2.2.2
                  linarith only [h1161, h1302, h1304, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1306_1]
                · have p1306_0 := h1306c.1
                  have p1306_1 := h1306c.2.1
                  have p1306_2 := h1306c.2.2.1
                  have p1306_3 := h1306c.2.2.2
                  rcases p1306_3 (m.d 0 5) (by simp) with h1321 | h1321
                  · linarith only [h1, h1321, hlam]
                  · linarith only [h1158, h1321, hlam]
                · have p1306_0 := h1306c.1
                  have p1306_1 := h1306c.2.1
                  have p1306_2 := h1306c.2.2.1
                  have p1306_3 := h1306c.2.2.2
                  linarith only [h0, h1159, hc12, hc35, hlam, hphi, ht23, p1306_1]
                · have p1306_0 := h1306c.1
                  have p1306_1 := h1306c.2.1
                  have p1306_2 := h1306c.2.2.1
                  have p1306_3 := h1306c.2.2.2
                  linarith only [h1159, hc12, hc35, hlam, hphi, ht23, p1306_1]
                · have p1306_0 := h1306c.1
                  have p1306_1 := h1306c.2.1
                  have p1306_2 := h1306c.2.2.1
                  have p1306_3 := h1306c.2.2.2
                  linarith only [h1303, hlam, p1306_0]
                · have p1306_0 := h1306c.1
                  have p1306_1 := h1306c.2.1
                  have p1306_2 := h1306c.2.2.1
                  have p1306_3 := h1306c.2.2.2
                  linarith only [hlam, p1306_0]
                · have p1306_0 := h1306c.1
                  have p1306_1 := h1306c.2.1
                  have p1306_2 := h1306c.2.2.1
                  have p1306_3 := h1306c.2.2.2
                  linarith only [h1302, h1305, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1306_1]
                · have p1306_0 := h1306c.1
                  have p1306_1 := h1306c.2.1
                  have p1306_2 := h1306c.2.2.1
                  have p1306_3 := h1306c.2.2.2
                  linarith only [h1158, hlam, p1306_1]
                · have p1306_0 := h1306c.1
                  have p1306_1 := h1306c.2.1
                  have p1306_2 := h1306c.2.2.1
                  have p1306_3 := h1306c.2.2.2
                  linarith only [h1301, hlam, p1306_1]
                · have p1306_0 := h1306c.1
                  have p1306_1 := h1306c.2.1
                  have p1306_2 := h1306c.2.2.1
                  have p1306_3 := h1306c.2.2.2
                  linarith only [h1304, hlam, p1306_1]
                · have p1306_0 := h1306c.1
                  have p1306_1 := h1306c.2.1
                  have p1306_2 := h1306c.2.2.1
                  have p1306_3 := h1306c.2.2.2
                  linarith only [h1305, hlam, p1306_1]
                · have p1306_0 := h1306c.1
                  have p1306_1 := h1306c.2.1
                  have p1306_2 := h1306c.2.2.1
                  have p1306_3 := h1306c.2.2.2
                  linarith only [hlam, p1306_0]
              · linarith only [h1161, h1301, h1305, hlam]
            · linarith only [h0, h1, h1301, h1304, hlam]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1336 | h1336
            · linarith only [h1302, h1303, h1336, hlam]
            · linarith only [h1, h1158, h1336, hlam]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1339 | h1339
          · linarith only [h1161, h1302, h1339, hc13, hc34, hlam, hphi]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1341 | h1341
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1342 | h1342
              · rcases h5bigk with h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c
                · have p1343_0 := h1343c.1
                  have p1343_1 := h1343c.2.1
                  have p1343_2 := h1343c.2.2.1
                  have p1343_3 := h1343c.2.2.2
                  linarith only [hlam, p1343_0]
                · have p1343_0 := h1343c.1
                  have p1343_1 := h1343c.2.1
                  have p1343_2 := h1343c.2.2.1
                  have p1343_3 := h1343c.2.2.2
                  linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p1343_1, u1elo0]
                · have p1343_0 := h1343c.1
                  have p1343_1 := h1343c.2.1
                  have p1343_2 := h1343c.2.2.1
                  have p1343_3 := h1343c.2.2.2
                  linarith only [h1, hlam, p1343_0]
                · have p1343_0 := h1343c.1
                  have p1343_1 := h1343c.2.1
                  have p1343_2 := h1343c.2.2.1
                  have p1343_3 := h1343c.2.2.2
                  linarith only [h1339, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1343_1]
                · have p1343_0 := h1343c.1
                  have p1343_1 := h1343c.2.1
                  have p1343_2 := h1343c.2.2.1
                  have p1343_3 := h1343c.2.2.2
                  linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p1343_1, u1elo0]
                · have p1343_0 := h1343c.1
                  have p1343_1 := h1343c.2.1
                  have p1343_2 := h1343c.2.2.1
                  have p1343_3 := h1343c.2.2.2
                  linarith only [h0, hlam, p1343_0]
                · have p1343_0 := h1343c.1
                  have p1343_1 := h1343c.2.1
                  have p1343_2 := h1343c.2.2.1
                  have p1343_3 := h1343c.2.2.2
                  linarith only [hlam, p1343_0]
                · have p1343_0 := h1343c.1
                  have p1343_1 := h1343c.2.1
                  have p1343_2 := h1343c.2.2.1
                  have p1343_3 := h1343c.2.2.2
                  linarith only [h1159, hlam, p1343_0]
                · have p1343_0 := h1343c.1
                  have p1343_1 := h1343c.2.1
                  have p1343_2 := h1343c.2.2.1
                  have p1343_3 := h1343c.2.2.2
                  linarith only [h1161, hlam, p1343_0]
                · have p1343_0 := h1343c.1
                  have p1343_1 := h1343c.2.1
                  have p1343_2 := h1343c.2.2.1
                  have p1343_3 := h1343c.2.2.2
                  linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p1343_1, u1elo4]
                · have p1343_0 := h1343c.1
                  have p1343_1 := h1343c.2.1
                  have p1343_2 := h1343c.2.2.1
                  have p1343_3 := h1343c.2.2.2
                  linarith only [h1, h1341, hc02, hc24, hlam, hphi, p1343_1]
                · have p1343_0 := h1343c.1
                  have p1343_1 := h1343c.2.1
                  have p1343_2 := h1343c.2.2.1
                  have p1343_3 := h1343c.2.2.2
                  linarith only [h1159, h1341, hc12, hc24, hlam, hphi, p1343_1]
                · have p1343_0 := h1343c.1
                  have p1343_1 := h1343c.2.1
                  have p1343_2 := h1343c.2.2.1
                  have p1343_3 := h1343c.2.2.2
                  linarith only [hlam, p1343_0]
                · have p1343_0 := h1343c.1
                  have p1343_1 := h1343c.2.1
                  have p1343_2 := h1343c.2.2.1
                  have p1343_3 := h1343c.2.2.2
                  linarith only [h1339, hlam, p1343_1]
                · have p1343_0 := h1343c.1
                  have p1343_1 := h1343c.2.1
                  have p1343_2 := h1343c.2.2.1
                  have p1343_3 := h1343c.2.2.2
                  rcases p1343_3 (m.d 0 5) (by simp) with h1358 | h1358
                  · linarith only [h1, h1358, hlam]
                  · linarith only [h1158, h1358, hlam]
                · have p1343_0 := h1343c.1
                  have p1343_1 := h1343c.2.1
                  have p1343_2 := h1343c.2.2.1
                  have p1343_3 := h1343c.2.2.2
                  linarith only [h0, h1159, hc12, hc35, hlam, hphi, ht23, p1343_1]
                · have p1343_0 := h1343c.1
                  have p1343_1 := h1343c.2.1
                  have p1343_2 := h1343c.2.2.1
                  have p1343_3 := h1343c.2.2.2
                  linarith only [h1159, hc12, hc35, hlam, hphi, ht23, p1343_1]
                · have p1343_0 := h1343c.1
                  have p1343_1 := h1343c.2.1
                  have p1343_2 := h1343c.2.2.1
                  have p1343_3 := h1343c.2.2.2
                  linarith only [h1, hc02, hc35, hlam, hphi, ht23, p1343_1]
                · have p1343_0 := h1343c.1
                  have p1343_1 := h1343c.2.1
                  have p1343_2 := h1343c.2.2.1
                  have p1343_3 := h1343c.2.2.2
                  linarith only [hlam, p1343_0]
                · have p1343_0 := h1343c.1
                  have p1343_1 := h1343c.2.1
                  have p1343_2 := h1343c.2.2.1
                  have p1343_3 := h1343c.2.2.2
                  rcases p1343_3 (m.d 0 5) (by simp) with h1365 | h1365
                  · linarith only [h1, h1339, h1365, hlam]
                  · linarith only [h1158, h1365, hlam]
                · have p1343_0 := h1343c.1
                  have p1343_1 := h1343c.2.1
                  have p1343_2 := h1343c.2.2.1
                  have p1343_3 := h1343c.2.2.2
                  linarith only [h1158, hlam, p1343_1]
                · have p1343_0 := h1343c.1
                  have p1343_1 := h1343c.2.1
                  have p1343_2 := h1343c.2.2.1
                  have p1343_3 := h1343c.2.2.2
                  linarith only [h1301, hlam, p1343_1]
                · have p1343_0 := h1343c.1
                  have p1343_1 := h1343c.2.1
                  have p1343_2 := h1343c.2.2.1
                  have p1343_3 := h1343c.2.2.2
                  linarith only [h1341, hlam, p1343_1]
                · have p1343_0 := h1343c.1
                  have p1343_1 := h1343c.2.1
                  have p1343_2 := h1343c.2.2.1
                  have p1343_3 := h1343c.2.2.2
                  linarith only [h1342, hlam, p1343_1]
                · have p1343_0 := h1343c.1
                  have p1343_1 := h1343c.2.1
                  have p1343_2 := h1343c.2.2.1
                  have p1343_3 := h1343c.2.2.2
                  linarith only [hlam, p1343_0]
              · linarith only [h0, h1301, h1302, h1342, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
            · linarith only [h0, h1, h1301, h1341, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1375 | h1375
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1376 | h1376
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1377 | h1377
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1378 | h1378
              · rcases h5bigk with h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c
                · have p1379_0 := h1379c.1
                  have p1379_1 := h1379c.2.1
                  have p1379_2 := h1379c.2.2.1
                  have p1379_3 := h1379c.2.2.2
                  linarith only [hlam, p1379_0]
                · have p1379_0 := h1379c.1
                  have p1379_1 := h1379c.2.1
                  have p1379_2 := h1379c.2.2.1
                  have p1379_3 := h1379c.2.2.2
                  linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p1379_1, u1elo0]
                · have p1379_0 := h1379c.1
                  have p1379_1 := h1379c.2.1
                  have p1379_2 := h1379c.2.2.1
                  have p1379_3 := h1379c.2.2.2
                  linarith only [h1, hlam, p1379_0]
                · have p1379_0 := h1379c.1
                  have p1379_1 := h1379c.2.1
                  have p1379_2 := h1379c.2.2.1
                  have p1379_3 := h1379c.2.2.2
                  linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p1379_1, u1elo0]
                · have p1379_0 := h1379c.1
                  have p1379_1 := h1379c.2.1
                  have p1379_2 := h1379c.2.2.1
                  have p1379_3 := h1379c.2.2.2
                  linarith only [h0, h1301, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1379_1, u1elo0]
                · have p1379_0 := h1379c.1
                  have p1379_1 := h1379c.2.1
                  have p1379_2 := h1379c.2.2.1
                  have p1379_3 := h1379c.2.2.2
                  linarith only [h0, hlam, p1379_0]
                · have p1379_0 := h1379c.1
                  have p1379_1 := h1379c.2.1
                  have p1379_2 := h1379c.2.2.1
                  have p1379_3 := h1379c.2.2.2
                  linarith only [hlam, p1379_0]
                · have p1379_0 := h1379c.1
                  have p1379_1 := h1379c.2.1
                  have p1379_2 := h1379c.2.2.1
                  have p1379_3 := h1379c.2.2.2
                  linarith only [h1159, hlam, p1379_0]
                · have p1379_0 := h1379c.1
                  have p1379_1 := h1379c.2.1
                  have p1379_2 := h1379c.2.2.1
                  have p1379_3 := h1379c.2.2.2
                  linarith only [h1161, hlam, p1379_0]
                · have p1379_0 := h1379c.1
                  have p1379_1 := h1379c.2.1
                  have p1379_2 := h1379c.2.2.1
                  have p1379_3 := h1379c.2.2.2
                  linarith only [h1301, hlam, p1379_0]
                · have p1379_0 := h1379c.1
                  have p1379_1 := h1379c.2.1
                  have p1379_2 := h1379c.2.2.1
                  have p1379_3 := h1379c.2.2.2
                  linarith only [h0, h1159, hc12, hc25, hlam, hphi, p1379_1]
                · have p1379_0 := h1379c.1
                  have p1379_1 := h1379c.2.1
                  have p1379_2 := h1379c.2.2.1
                  have p1379_3 := h1379c.2.2.2
                  linarith only [h1159, hc12, hc25, hlam, hphi, p1379_1]
                · have p1379_0 := h1379c.1
                  have p1379_1 := h1379c.2.1
                  have p1379_2 := h1379c.2.2.1
                  have p1379_3 := h1379c.2.2.2
                  linarith only [hlam, p1379_0]
                · have p1379_0 := h1379c.1
                  have p1379_1 := h1379c.2.1
                  have p1379_2 := h1379c.2.2.1
                  have p1379_3 := h1379c.2.2.2
                  linarith only [h1161, h1376, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1379_1]
                · have p1379_0 := h1379c.1
                  have p1379_1 := h1379c.2.1
                  have p1379_2 := h1379c.2.2.1
                  have p1379_3 := h1379c.2.2.2
                  linarith only [h1301, h1375, h1377, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1379_1]
                · have p1379_0 := h1379c.1
                  have p1379_1 := h1379c.2.1
                  have p1379_2 := h1379c.2.2.1
                  have p1379_3 := h1379c.2.2.2
                  linarith only [h1158, h1301, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1379_1]
                · have p1379_0 := h1379c.1
                  have p1379_1 := h1379c.2.1
                  have p1379_2 := h1379c.2.2.1
                  have p1379_3 := h1379c.2.2.2
                  linarith only [h1159, hc12, hc35, hlam, hphi, ht23, p1379_1]
                · have p1379_0 := h1379c.1
                  have p1379_1 := h1379c.2.1
                  have p1379_2 := h1379c.2.2.1
                  have p1379_3 := h1379c.2.2.2
                  linarith only [h1376, hlam, p1379_0]
                · have p1379_0 := h1379c.1
                  have p1379_1 := h1379c.2.1
                  have p1379_2 := h1379c.2.2.1
                  have p1379_3 := h1379c.2.2.2
                  linarith only [hlam, p1379_0]
                · have p1379_0 := h1379c.1
                  have p1379_1 := h1379c.2.1
                  have p1379_2 := h1379c.2.2.1
                  have p1379_3 := h1379c.2.2.2
                  linarith only [h1301, h1375, h1378, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1379_1]
                · have p1379_0 := h1379c.1
                  have p1379_1 := h1379c.2.1
                  have p1379_2 := h1379c.2.2.1
                  have p1379_3 := h1379c.2.2.2
                  linarith only [h1158, hlam, p1379_1]
                · have p1379_0 := h1379c.1
                  have p1379_1 := h1379c.2.1
                  have p1379_2 := h1379c.2.2.1
                  have p1379_3 := h1379c.2.2.2
                  linarith only [h1159, hc12, hc45, hlam, hphi, ht23, ht34, p1379_1]
                · have p1379_0 := h1379c.1
                  have p1379_1 := h1379c.2.1
                  have p1379_2 := h1379c.2.2.1
                  have p1379_3 := h1379c.2.2.2
                  linarith only [h1377, hlam, p1379_1]
                · have p1379_0 := h1379c.1
                  have p1379_1 := h1379c.2.1
                  have p1379_2 := h1379c.2.2.1
                  have p1379_3 := h1379c.2.2.2
                  linarith only [h1378, hlam, p1379_1]
                · have p1379_0 := h1379c.1
                  have p1379_1 := h1379c.2.1
                  have p1379_2 := h1379c.2.2.1
                  have p1379_3 := h1379c.2.2.2
                  linarith only [hlam, p1379_0]
              · rcases h5bigk with h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c | h1405c
                · have p1405_0 := h1405c.1
                  have p1405_1 := h1405c.2.1
                  have p1405_2 := h1405c.2.2.1
                  have p1405_3 := h1405c.2.2.2
                  linarith only [hlam, p1405_0]
                · have p1405_0 := h1405c.1
                  have p1405_1 := h1405c.2.1
                  have p1405_2 := h1405c.2.2.1
                  have p1405_3 := h1405c.2.2.2
                  linarith only [h0, h1159, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1405_1, u1elo0]
                · have p1405_0 := h1405c.1
                  have p1405_1 := h1405c.2.1
                  have p1405_2 := h1405c.2.2.1
                  have p1405_3 := h1405c.2.2.2
                  linarith only [h1, hlam, p1405_0]
                · have p1405_0 := h1405c.1
                  have p1405_1 := h1405c.2.1
                  have p1405_2 := h1405c.2.2.1
                  have p1405_3 := h1405c.2.2.2
                  linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p1405_1, u1elo0]
                · have p1405_0 := h1405c.1
                  have p1405_1 := h1405c.2.1
                  have p1405_2 := h1405c.2.2.1
                  have p1405_3 := h1405c.2.2.2
                  linarith only [h0, h1378, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1405_1, u1elo0]
                · have p1405_0 := h1405c.1
                  have p1405_1 := h1405c.2.1
                  have p1405_2 := h1405c.2.2.1
                  have p1405_3 := h1405c.2.2.2
                  linarith only [h0, hlam, p1405_0]
                · have p1405_0 := h1405c.1
                  have p1405_1 := h1405c.2.1
                  have p1405_2 := h1405c.2.2.1
                  have p1405_3 := h1405c.2.2.2
                  linarith only [hlam, p1405_0]
                · have p1405_0 := h1405c.1
                  have p1405_1 := h1405c.2.1
                  have p1405_2 := h1405c.2.2.1
                  have p1405_3 := h1405c.2.2.2
                  linarith only [h1159, hlam, p1405_0]
                · have p1405_0 := h1405c.1
                  have p1405_1 := h1405c.2.1
                  have p1405_2 := h1405c.2.2.1
                  have p1405_3 := h1405c.2.2.2
                  linarith only [h1161, hlam, p1405_0]
                · have p1405_0 := h1405c.1
                  have p1405_1 := h1405c.2.1
                  have p1405_2 := h1405c.2.2.1
                  have p1405_3 := h1405c.2.2.2
                  linarith only [h1301, hlam, p1405_0]
                · have p1405_0 := h1405c.1
                  have p1405_1 := h1405c.2.1
                  have p1405_2 := h1405c.2.2.1
                  have p1405_3 := h1405c.2.2.2
                  linarith only [h0, h1159, h1375, h1377, hc12, hc23, hlam, hphi, p1405_1]
                · have p1405_0 := h1405c.1
                  have p1405_1 := h1405c.2.1
                  have p1405_2 := h1405c.2.2.1
                  have p1405_3 := h1405c.2.2.2
                  linarith only [h1159, h1375, h1377, hc12, hc23, hlam, hphi, p1405_1]
                · have p1405_0 := h1405c.1
                  have p1405_1 := h1405c.2.1
                  have p1405_2 := h1405c.2.2.1
                  have p1405_3 := h1405c.2.2.2
                  linarith only [hlam, p1405_0]
                · have p1405_0 := h1405c.1
                  have p1405_1 := h1405c.2.1
                  have p1405_2 := h1405c.2.2.1
                  have p1405_3 := h1405c.2.2.2
                  linarith only [h1161, h1375, h1377, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1405_1]
                · have p1405_0 := h1405c.1
                  have p1405_1 := h1405c.2.1
                  have p1405_2 := h1405c.2.2.1
                  have p1405_3 := h1405c.2.2.2
                  linarith only [h1375, h1377, h1378, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1405_1]
                · have p1405_0 := h1405c.1
                  have p1405_1 := h1405c.2.1
                  have p1405_2 := h1405c.2.2.1
                  have p1405_3 := h1405c.2.2.2
                  linarith only [h1158, h1378, hlam, p1405_1]
                · have p1405_0 := h1405c.1
                  have p1405_1 := h1405c.2.1
                  have p1405_2 := h1405c.2.2.1
                  have p1405_3 := h1405c.2.2.2
                  linarith only [h1159, hc12, hc35, hlam, hphi, ht23, p1405_1]
                · have p1405_0 := h1405c.1
                  have p1405_1 := h1405c.2.1
                  have p1405_2 := h1405c.2.2.1
                  have p1405_3 := h1405c.2.2.2
                  linarith only [h1376, hlam, p1405_0]
                · have p1405_0 := h1405c.1
                  have p1405_1 := h1405c.2.1
                  have p1405_2 := h1405c.2.2.1
                  have p1405_3 := h1405c.2.2.2
                  linarith only [hlam, p1405_0]
                · have p1405_0 := h1405c.1
                  have p1405_1 := h1405c.2.1
                  have p1405_2 := h1405c.2.2.1
                  have p1405_3 := h1405c.2.2.2
                  linarith only [h1378, hlam, p1405_0]
                · have p1405_0 := h1405c.1
                  have p1405_1 := h1405c.2.1
                  have p1405_2 := h1405c.2.2.1
                  have p1405_3 := h1405c.2.2.2
                  linarith only [h1158, hlam, p1405_1]
                · have p1405_0 := h1405c.1
                  have p1405_1 := h1405c.2.1
                  have p1405_2 := h1405c.2.2.1
                  have p1405_3 := h1405c.2.2.2
                  linarith only [h0, h1158, h1159, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1405_1, u1elo0]
                · have p1405_0 := h1405c.1
                  have p1405_1 := h1405c.2.1
                  have p1405_2 := h1405c.2.2.1
                  have p1405_3 := h1405c.2.2.2
                  linarith only [h1377, hlam, p1405_1]
                · have p1405_0 := h1405c.1
                  have p1405_1 := h1405c.2.1
                  have p1405_2 := h1405c.2.2.1
                  have p1405_3 := h1405c.2.2.2
                  linarith only [h1375, h1377, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1405_1]
                · have p1405_0 := h1405c.1
                  have p1405_1 := h1405c.2.1
                  have p1405_2 := h1405c.2.2.1
                  have p1405_3 := h1405c.2.2.2
                  linarith only [hlam, p1405_0]
            · linarith only [h1, h1158, h1377, hlam]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1432 | h1432
            · linarith only [h1375, h1376, h1432, hlam]
            · linarith only [h1, h1158, h1432, hlam]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1435 | h1435
          · linarith only [h1161, h1375, h1435, hc13, hc34, hlam, hphi]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1437 | h1437
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1438 | h1438
              · rcases h5bigk with h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c
                · have p1439_0 := h1439c.1
                  have p1439_1 := h1439c.2.1
                  have p1439_2 := h1439c.2.2.1
                  have p1439_3 := h1439c.2.2.2
                  linarith only [hlam, p1439_0]
                · have p1439_0 := h1439c.1
                  have p1439_1 := h1439c.2.1
                  have p1439_2 := h1439c.2.2.1
                  have p1439_3 := h1439c.2.2.2
                  linarith only [h0, h1159, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1439_1, u1elo0]
                · have p1439_0 := h1439c.1
                  have p1439_1 := h1439c.2.1
                  have p1439_2 := h1439c.2.2.1
                  have p1439_3 := h1439c.2.2.2
                  linarith only [h1, hlam, p1439_0]
                · have p1439_0 := h1439c.1
                  have p1439_1 := h1439c.2.1
                  have p1439_2 := h1439c.2.2.1
                  have p1439_3 := h1439c.2.2.2
                  linarith only [h0, h1435, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1439_1, u1elo0]
                · have p1439_0 := h1439c.1
                  have p1439_1 := h1439c.2.1
                  have p1439_2 := h1439c.2.2.1
                  have p1439_3 := h1439c.2.2.2
                  linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p1439_1, u1elo0]
                · have p1439_0 := h1439c.1
                  have p1439_1 := h1439c.2.1
                  have p1439_2 := h1439c.2.2.1
                  have p1439_3 := h1439c.2.2.2
                  linarith only [h0, hlam, p1439_0]
                · have p1439_0 := h1439c.1
                  have p1439_1 := h1439c.2.1
                  have p1439_2 := h1439c.2.2.1
                  have p1439_3 := h1439c.2.2.2
                  linarith only [hlam, p1439_0]
                · have p1439_0 := h1439c.1
                  have p1439_1 := h1439c.2.1
                  have p1439_2 := h1439c.2.2.1
                  have p1439_3 := h1439c.2.2.2
                  linarith only [h1159, hlam, p1439_0]
                · have p1439_0 := h1439c.1
                  have p1439_1 := h1439c.2.1
                  have p1439_2 := h1439c.2.2.1
                  have p1439_3 := h1439c.2.2.2
                  linarith only [h1161, hlam, p1439_0]
                · have p1439_0 := h1439c.1
                  have p1439_1 := h1439c.2.1
                  have p1439_2 := h1439c.2.2.1
                  have p1439_3 := h1439c.2.2.2
                  linarith only [h1301, hlam, p1439_0]
                · have p1439_0 := h1439c.1
                  have p1439_1 := h1439c.2.1
                  have p1439_2 := h1439c.2.2.1
                  have p1439_3 := h1439c.2.2.2
                  linarith only [h0, h1159, hc12, hc25, hlam, hphi, p1439_1]
                · have p1439_0 := h1439c.1
                  have p1439_1 := h1439c.2.1
                  have p1439_2 := h1439c.2.2.1
                  have p1439_3 := h1439c.2.2.2
                  linarith only [h1159, hc12, hc25, hlam, hphi, p1439_1]
                · have p1439_0 := h1439c.1
                  have p1439_1 := h1439c.2.1
                  have p1439_2 := h1439c.2.2.1
                  have p1439_3 := h1439c.2.2.2
                  linarith only [hlam, p1439_0]
                · have p1439_0 := h1439c.1
                  have p1439_1 := h1439c.2.1
                  have p1439_2 := h1439c.2.2.1
                  have p1439_3 := h1439c.2.2.2
                  linarith only [h1435, hlam, p1439_1]
                · have p1439_0 := h1439c.1
                  have p1439_1 := h1439c.2.1
                  have p1439_2 := h1439c.2.2.1
                  have p1439_3 := h1439c.2.2.2
                  linarith only [h1301, h1375, h1437, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1439_1]
                · have p1439_0 := h1439c.1
                  have p1439_1 := h1439c.2.1
                  have p1439_2 := h1439c.2.2.1
                  have p1439_3 := h1439c.2.2.2
                  linarith only [h1158, h1301, h1438, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1439_1]
                · have p1439_0 := h1439c.1
                  have p1439_1 := h1439c.2.1
                  have p1439_2 := h1439c.2.2.1
                  have p1439_3 := h1439c.2.2.2
                  linarith only [h1159, h1438, hc12, hc34, hlam, hphi, ht23, p1439_1]
                · have p1439_0 := h1439c.1
                  have p1439_1 := h1439c.2.1
                  have p1439_2 := h1439c.2.2.1
                  have p1439_3 := h1439c.2.2.2
                  linarith only [h1, h1438, hc02, hc34, hlam, hphi, ht23, p1439_1]
                · have p1439_0 := h1439c.1
                  have p1439_1 := h1439c.2.1
                  have p1439_2 := h1439c.2.2.1
                  have p1439_3 := h1439c.2.2.2
                  linarith only [hlam, p1439_0]
                · have p1439_0 := h1439c.1
                  have p1439_1 := h1439c.2.1
                  have p1439_2 := h1439c.2.2.1
                  have p1439_3 := h1439c.2.2.2
                  linarith only [h1301, h1438, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1439_1]
                · have p1439_0 := h1439c.1
                  have p1439_1 := h1439c.2.1
                  have p1439_2 := h1439c.2.2.1
                  have p1439_3 := h1439c.2.2.2
                  linarith only [h1158, hlam, p1439_1]
                · have p1439_0 := h1439c.1
                  have p1439_1 := h1439c.2.1
                  have p1439_2 := h1439c.2.2.1
                  have p1439_3 := h1439c.2.2.2
                  linarith only [h1159, hc12, hc45, hlam, hphi, ht23, ht34, p1439_1]
                · have p1439_0 := h1439c.1
                  have p1439_1 := h1439c.2.1
                  have p1439_2 := h1439c.2.2.1
                  have p1439_3 := h1439c.2.2.2
                  linarith only [h1437, hlam, p1439_1]
                · have p1439_0 := h1439c.1
                  have p1439_1 := h1439c.2.1
                  have p1439_2 := h1439c.2.2.1
                  have p1439_3 := h1439c.2.2.2
                  linarith only [h1438, hlam, p1439_1]
                · have p1439_0 := h1439c.1
                  have p1439_1 := h1439c.2.1
                  have p1439_2 := h1439c.2.2.1
                  have p1439_3 := h1439c.2.2.2
                  linarith only [hlam, p1439_0]
              · linarith only [h1375, h1437, h1438, hlam]
            · linarith only [h1, h1158, h1437, hlam]

end R2N4
