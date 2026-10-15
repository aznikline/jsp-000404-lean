import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_36S14

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7676000 in
set_option maxHeartbeats 7676000 in
theorem r1l7_20_12_14_H_I_L_I_L_R_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0bigk := hb0.1
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1178 | h1178
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1179 | h1179
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1180 | h1180
      · linarith only [h0, h1180, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1182 | h1182
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1183 | h1183
          · linarith only [h0, h1179, h1183, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1185 | h1185
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1186 | h1186
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1187 | h1187
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1188 | h1188
                  · rcases h0bigk with h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c
                    · have p1189_0 := h1189c.1
                      have p1189_1 := h1189c.2.1
                      have p1189_2 := h1189c.2.2.1
                      have p1189_3 := h1189c.2.2.2
                      linarith only [hlam, p1189_0]
                    · have p1189_0 := h1189c.1
                      have p1189_1 := h1189c.2.1
                      have p1189_2 := h1189c.2.2.1
                      have p1189_3 := h1189c.2.2.2
                      linarith only [h1179, h1185, h1188, hc01, hlam, hphi, ht0b, ht45, ht5b, p1189_1, u4ehi4]
                    · have p1189_0 := h1189c.1
                      have p1189_1 := h1189c.2.1
                      have p1189_2 := h1189c.2.2.1
                      have p1189_3 := h1189c.2.2.2
                      linarith only [h1185, h1188, h2, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1189_1, u4ehi4]
                    · have p1189_0 := h1189c.1
                      have p1189_1 := h1189c.2.1
                      have p1189_2 := h1189c.2.2.1
                      have p1189_3 := h1189c.2.2.2
                      linarith only [h2, hlam, p1189_1]
                    · have p1189_0 := h1189c.1
                      have p1189_1 := h1189c.2.1
                      have p1189_2 := h1189c.2.2.1
                      have p1189_3 := h1189c.2.2.2
                      linarith only [h2, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p1189_1]
                    · have p1189_0 := h1189c.1
                      have p1189_1 := h1189c.2.1
                      have p1189_2 := h1189c.2.2.1
                      have p1189_3 := h1189c.2.2.2
                      linarith only [h0, hlam, p1189_0]
                    · have p1189_0 := h1189c.1
                      have p1189_1 := h1189c.2.1
                      have p1189_2 := h1189c.2.2.1
                      have p1189_3 := h1189c.2.2.2
                      linarith only [hlam, p1189_0]
                    · have p1189_0 := h1189c.1
                      have p1189_1 := h1189c.2.1
                      have p1189_2 := h1189c.2.2.1
                      have p1189_3 := h1189c.2.2.2
                      linarith only [h1185, h1188, hc02, hlam, hphi, ht0b, ht45, ht5b, p1189_1, u4ehi4]
                    · have p1189_0 := h1189c.1
                      have p1189_1 := h1189c.2.1
                      have p1189_2 := h1189c.2.2.1
                      have p1189_3 := h1189c.2.2.2
                      linarith only [h1180, hlam, p1189_1]
                    · have p1189_0 := h1189c.1
                      have p1189_1 := h1189c.2.1
                      have p1189_2 := h1189c.2.2.1
                      have p1189_3 := h1189c.2.2.2
                      linarith only [h1178, h1180, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1189_1]
                    · have p1189_0 := h1189c.1
                      have p1189_1 := h1189c.2.1
                      have p1189_2 := h1189c.2.2.1
                      have p1189_3 := h1189c.2.2.2
                      linarith only [h1, hlam, p1189_1]
                    · have p1189_0 := h1189c.1
                      have p1189_1 := h1189c.2.1
                      have p1189_2 := h1189c.2.2.1
                      have p1189_3 := h1189c.2.2.2
                      linarith only [h1179, hlam, p1189_1]
                    · have p1189_0 := h1189c.1
                      have p1189_1 := h1189c.2.1
                      have p1189_2 := h1189c.2.2.1
                      have p1189_3 := h1189c.2.2.2
                      linarith only [hlam, p1189_0]
                    · have p1189_0 := h1189c.1
                      have p1189_1 := h1189c.2.1
                      have p1189_2 := h1189c.2.2.1
                      have p1189_3 := h1189c.2.2.2
                      linarith only [h1183, hlam, p1189_1]
                    · have p1189_0 := h1189c.1
                      have p1189_1 := h1189c.2.1
                      have p1189_2 := h1189c.2.2.1
                      have p1189_3 := h1189c.2.2.2
                      linarith only [h1, h1178, h2, hc14, hc15, hlam, hphi, ht01, ht0b, ht5b, p1189_1]
                    · have p1189_0 := h1189c.1
                      have p1189_1 := h1189c.2.1
                      have p1189_2 := h1189c.2.2.1
                      have p1189_3 := h1189c.2.2.2
                      linarith only [h1183, hc01, hc34, hlam, hphi, ht12, ht23, p1189_1]
                    · have p1189_0 := h1189c.1
                      have p1189_1 := h1189c.2.1
                      have p1189_2 := h1189c.2.2.1
                      have p1189_3 := h1189c.2.2.2
                      linarith only [h1183, hc02, hc34, hlam, hphi, ht23, p1189_1]
                    · have p1189_0 := h1189c.1
                      have p1189_1 := h1189c.2.1
                      have p1189_2 := h1189c.2.2.1
                      have p1189_3 := h1189c.2.2.2
                      linarith only [h1183, hc03, hc34, hlam, hphi, p1189_1]
                    · have p1189_0 := h1189c.1
                      have p1189_1 := h1189c.2.1
                      have p1189_2 := h1189c.2.2.1
                      have p1189_3 := h1189c.2.2.2
                      linarith only [hlam, p1189_0]
                    · have p1189_0 := h1189c.1
                      have p1189_1 := h1189c.2.1
                      have p1189_2 := h1189c.2.2.1
                      have p1189_3 := h1189c.2.2.2
                      linarith only [h1183, h1185, h1188, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1189_1, u4ehi4]
                    · have p1189_0 := h1189c.1
                      have p1189_1 := h1189c.2.1
                      have p1189_2 := h1189c.2.2.1
                      have p1189_3 := h1189c.2.2.2
                      linarith only [h1178, hlam, p1189_0]
                    · have p1189_0 := h1189c.1
                      have p1189_1 := h1189c.2.1
                      have p1189_2 := h1189c.2.2.1
                      have p1189_3 := h1189c.2.2.2
                      linarith only [h1182, hlam, p1189_1]
                    · have p1189_0 := h1189c.1
                      have p1189_1 := h1189c.2.1
                      have p1189_2 := h1189c.2.2.1
                      have p1189_3 := h1189c.2.2.2
                      linarith only [h1185, hlam, p1189_0]
                    · have p1189_0 := h1189c.1
                      have p1189_1 := h1189c.2.1
                      have p1189_2 := h1189c.2.2.1
                      have p1189_3 := h1189c.2.2.2
                      linarith only [h1186, hlam, p1189_1]
                    · have p1189_0 := h1189c.1
                      have p1189_1 := h1189c.2.1
                      have p1189_2 := h1189c.2.2.1
                      have p1189_3 := h1189c.2.2.2
                      linarith only [hlam, p1189_0]
                  · linarith only [h1183, h1186, h1188, hlam]
                · linarith only [h0, h1187, h2, hc12, hc45, hlam, hphi, ht23, ht34]
              · linarith only [h0, h1179, h1185, h1186, h2, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1218 | h1218
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1219 | h1219
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1220 | h1220
                  · rcases h0bigk with h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c
                    · have p1221_0 := h1221c.1
                      have p1221_1 := h1221c.2.1
                      have p1221_2 := h1221c.2.2.1
                      have p1221_3 := h1221c.2.2.2
                      linarith only [hlam, p1221_0]
                    · have p1221_0 := h1221c.1
                      have p1221_1 := h1221c.2.1
                      have p1221_2 := h1221c.2.2.1
                      have p1221_3 := h1221c.2.2.2
                      linarith only [h1182, hc01, hc25, hlam, hphi, ht0b, ht5b, p1221_1]
                    · have p1221_0 := h1221c.1
                      have p1221_1 := h1221c.2.1
                      have p1221_2 := h1221c.2.2.1
                      have p1221_3 := h1221c.2.2.2
                      linarith only [h2, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1221_1]
                    · have p1221_0 := h1221c.1
                      have p1221_1 := h1221c.2.1
                      have p1221_2 := h1221c.2.2.1
                      have p1221_3 := h1221c.2.2.2
                      linarith only [h2, hlam, p1221_1]
                    · have p1221_0 := h1221c.1
                      have p1221_1 := h1221c.2.1
                      have p1221_2 := h1221c.2.2.1
                      have p1221_3 := h1221c.2.2.2
                      linarith only [h2, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p1221_1]
                    · have p1221_0 := h1221c.1
                      have p1221_1 := h1221c.2.1
                      have p1221_2 := h1221c.2.2.1
                      have p1221_3 := h1221c.2.2.2
                      linarith only [h0, hlam, p1221_0]
                    · have p1221_0 := h1221c.1
                      have p1221_1 := h1221c.2.1
                      have p1221_2 := h1221c.2.2.1
                      have p1221_3 := h1221c.2.2.2
                      linarith only [hlam, p1221_0]
                    · have p1221_0 := h1221c.1
                      have p1221_1 := h1221c.2.1
                      have p1221_2 := h1221c.2.2.1
                      have p1221_3 := h1221c.2.2.2
                      linarith only [h0, h1, h2, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1221_1]
                    · have p1221_0 := h1221c.1
                      have p1221_1 := h1221c.2.1
                      have p1221_2 := h1221c.2.2.1
                      have p1221_3 := h1221c.2.2.2
                      linarith only [h1180, hlam, p1221_1]
                    · have p1221_0 := h1221c.1
                      have p1221_1 := h1221c.2.1
                      have p1221_2 := h1221c.2.2.1
                      have p1221_3 := h1221c.2.2.2
                      linarith only [h0, h1178, h1219, h2, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1221_1, u4ehi4]
                    · have p1221_0 := h1221c.1
                      have p1221_1 := h1221c.2.1
                      have p1221_2 := h1221c.2.2.1
                      have p1221_3 := h1221c.2.2.2
                      linarith only [h1, hlam, p1221_1]
                    · have p1221_0 := h1221c.1
                      have p1221_1 := h1221c.2.1
                      have p1221_2 := h1221c.2.2.1
                      have p1221_3 := h1221c.2.2.2
                      linarith only [h1179, hlam, p1221_1]
                    · have p1221_0 := h1221c.1
                      have p1221_1 := h1221c.2.1
                      have p1221_2 := h1221c.2.2.1
                      have p1221_3 := h1221c.2.2.2
                      linarith only [hlam, p1221_0]
                    · have p1221_0 := h1221c.1
                      have p1221_1 := h1221c.2.1
                      have p1221_2 := h1221c.2.2.1
                      have p1221_3 := h1221c.2.2.2
                      linarith only [h1183, hlam, p1221_1]
                    · have p1221_0 := h1221c.1
                      have p1221_1 := h1221c.2.1
                      have p1221_2 := h1221c.2.2.1
                      have p1221_3 := h1221c.2.2.2
                      linarith only [h1185, hlam, p1221_1]
                    · have p1221_0 := h1221c.1
                      have p1221_1 := h1221c.2.1
                      have p1221_2 := h1221c.2.2.1
                      have p1221_3 := h1221c.2.2.2
                      linarith only [h1180, hc01, hc24, hlam, hphi, ht12, p1221_1]
                    · have p1221_0 := h1221c.1
                      have p1221_1 := h1221c.2.1
                      have p1221_2 := h1221c.2.2.1
                      have p1221_3 := h1221c.2.2.2
                      linarith only [h1180, hc02, hc24, hlam, hphi, p1221_1]
                    · have p1221_0 := h1221c.1
                      have p1221_1 := h1221c.2.1
                      have p1221_2 := h1221c.2.2.1
                      have p1221_3 := h1221c.2.2.2
                      linarith only [h1, h1183, hc13, hc34, hlam, hphi, p1221_1]
                    · have p1221_0 := h1221c.1
                      have p1221_1 := h1221c.2.1
                      have p1221_2 := h1221c.2.2.1
                      have p1221_3 := h1221c.2.2.2
                      linarith only [hlam, p1221_0]
                    · have p1221_0 := h1221c.1
                      have p1221_1 := h1221c.2.1
                      have p1221_2 := h1221c.2.2.1
                      have p1221_3 := h1221c.2.2.2
                      linarith only [h1178, h1183, h1219, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1221_1, u4ehi4]
                    · have p1221_0 := h1221c.1
                      have p1221_1 := h1221c.2.1
                      have p1221_2 := h1221c.2.2.1
                      have p1221_3 := h1221c.2.2.2
                      linarith only [h1178, hlam, p1221_0]
                    · have p1221_0 := h1221c.1
                      have p1221_1 := h1221c.2.1
                      have p1221_2 := h1221c.2.2.1
                      have p1221_3 := h1221c.2.2.2
                      linarith only [h1182, hlam, p1221_1]
                    · have p1221_0 := h1221c.1
                      have p1221_1 := h1221c.2.1
                      have p1221_2 := h1221c.2.2.1
                      have p1221_3 := h1221c.2.2.2
                      linarith only [h1, h1178, h2, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1221_1]
                    · have p1221_0 := h1221c.1
                      have p1221_1 := h1221c.2.1
                      have p1221_2 := h1221c.2.2.1
                      have p1221_3 := h1221c.2.2.2
                      linarith only [h1218, hlam, p1221_1]
                    · have p1221_0 := h1221c.1
                      have p1221_1 := h1221c.2.1
                      have p1221_2 := h1221c.2.2.1
                      have p1221_3 := h1221c.2.2.2
                      linarith only [hlam, p1221_0]
                  · linarith only [h1183, h1218, h1220, hlam]
                · linarith only [h1178, h1218, h1219, h2, hc04, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h1182, h1218, h2, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1250 | h1250
          · linarith only [h1178, h1179, h1182, h1250, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1252 | h1252
            · linarith only [h1179, h1182, h1252, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1254 | h1254
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1255 | h1255
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1256 | h1256
                  · rcases h0bigk with h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c | h1257c
                    · have p1257_0 := h1257c.1
                      have p1257_1 := h1257c.2.1
                      have p1257_2 := h1257c.2.2.1
                      have p1257_3 := h1257c.2.2.2
                      linarith only [hlam, p1257_0]
                    · have p1257_0 := h1257c.1
                      have p1257_1 := h1257c.2.1
                      have p1257_2 := h1257c.2.2.1
                      have p1257_3 := h1257c.2.2.2
                      linarith only [h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1257_1]
                    · have p1257_0 := h1257c.1
                      have p1257_1 := h1257c.2.1
                      have p1257_2 := h1257c.2.2.1
                      have p1257_3 := h1257c.2.2.2
                      linarith only [h2, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1257_1]
                    · have p1257_0 := h1257c.1
                      have p1257_1 := h1257c.2.1
                      have p1257_2 := h1257c.2.2.1
                      have p1257_3 := h1257c.2.2.2
                      linarith only [h2, hlam, p1257_1]
                    · have p1257_0 := h1257c.1
                      have p1257_1 := h1257c.2.1
                      have p1257_2 := h1257c.2.2.1
                      have p1257_3 := h1257c.2.2.2
                      linarith only [h1179, h1182, h2, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1257_1]
                    · have p1257_0 := h1257c.1
                      have p1257_1 := h1257c.2.1
                      have p1257_2 := h1257c.2.2.1
                      have p1257_3 := h1257c.2.2.2
                      linarith only [h0, hlam, p1257_0]
                    · have p1257_0 := h1257c.1
                      have p1257_1 := h1257c.2.1
                      have p1257_2 := h1257c.2.2.1
                      have p1257_3 := h1257c.2.2.2
                      linarith only [hlam, p1257_0]
                    · have p1257_0 := h1257c.1
                      have p1257_1 := h1257c.2.1
                      have p1257_2 := h1257c.2.2.1
                      have p1257_3 := h1257c.2.2.2
                      linarith only [h1, h1180, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1257_1]
                    · have p1257_0 := h1257c.1
                      have p1257_1 := h1257c.2.1
                      have p1257_2 := h1257c.2.2.1
                      have p1257_3 := h1257c.2.2.2
                      linarith only [h1180, hlam, p1257_1]
                    · have p1257_0 := h1257c.1
                      have p1257_1 := h1257c.2.1
                      have p1257_2 := h1257c.2.2.1
                      have p1257_3 := h1257c.2.2.2
                      linarith only [h1182, hlam, p1257_0]
                    · have p1257_0 := h1257c.1
                      have p1257_1 := h1257c.2.1
                      have p1257_2 := h1257c.2.2.1
                      have p1257_3 := h1257c.2.2.2
                      linarith only [h1, hlam, p1257_1]
                    · have p1257_0 := h1257c.1
                      have p1257_1 := h1257c.2.1
                      have p1257_2 := h1257c.2.2.1
                      have p1257_3 := h1257c.2.2.2
                      linarith only [h1179, hlam, p1257_1]
                    · have p1257_0 := h1257c.1
                      have p1257_1 := h1257c.2.1
                      have p1257_2 := h1257c.2.2.1
                      have p1257_3 := h1257c.2.2.2
                      linarith only [hlam, p1257_0]
                    · have p1257_0 := h1257c.1
                      have p1257_1 := h1257c.2.1
                      have p1257_2 := h1257c.2.2.1
                      have p1257_3 := h1257c.2.2.2
                      linarith only [h1250, hlam, p1257_1]
                    · have p1257_0 := h1257c.1
                      have p1257_1 := h1257c.2.1
                      have p1257_2 := h1257c.2.2.1
                      have p1257_3 := h1257c.2.2.2
                      linarith only [h1252, hlam, p1257_1]
                    · have p1257_0 := h1257c.1
                      have p1257_1 := h1257c.2.1
                      have p1257_2 := h1257c.2.2.1
                      have p1257_3 := h1257c.2.2.2
                      linarith only [h1178, hc04, hc15, hlam, hphi, ht0b, ht5b, p1257_1]
                    · have p1257_0 := h1257c.1
                      have p1257_1 := h1257c.2.1
                      have p1257_2 := h1257c.2.2.1
                      have p1257_3 := h1257c.2.2.2
                      linarith only [h1180, hc02, hc24, hlam, hphi, p1257_1]
                    · have p1257_0 := h1257c.1
                      have p1257_1 := h1257c.2.1
                      have p1257_2 := h1257c.2.2.1
                      have p1257_3 := h1257c.2.2.2
                      linarith only [h1, h1250, hc13, hc34, hlam, hphi, p1257_1]
                    · have p1257_0 := h1257c.1
                      have p1257_1 := h1257c.2.1
                      have p1257_2 := h1257c.2.2.1
                      have p1257_3 := h1257c.2.2.2
                      linarith only [hlam, p1257_0]
                    · have p1257_0 := h1257c.1
                      have p1257_1 := h1257c.2.1
                      have p1257_2 := h1257c.2.2.1
                      have p1257_3 := h1257c.2.2.2
                      linarith only [h1178, h1250, h1255, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1257_1, u4ehi4]
                    · have p1257_0 := h1257c.1
                      have p1257_1 := h1257c.2.1
                      have p1257_2 := h1257c.2.2.1
                      have p1257_3 := h1257c.2.2.2
                      linarith only [h1178, hlam, p1257_0]
                    · have p1257_0 := h1257c.1
                      have p1257_1 := h1257c.2.1
                      have p1257_2 := h1257c.2.2.1
                      have p1257_3 := h1257c.2.2.2
                      linarith only [h1179, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1257_1]
                    · have p1257_0 := h1257c.1
                      have p1257_1 := h1257c.2.1
                      have p1257_2 := h1257c.2.2.1
                      have p1257_3 := h1257c.2.2.2
                      linarith only [h1, h1178, h2, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1257_1]
                    · have p1257_0 := h1257c.1
                      have p1257_1 := h1257c.2.1
                      have p1257_2 := h1257c.2.2.1
                      have p1257_3 := h1257c.2.2.2
                      linarith only [h1254, hlam, p1257_1]
                    · have p1257_0 := h1257c.1
                      have p1257_1 := h1257c.2.1
                      have p1257_2 := h1257c.2.2.1
                      have p1257_3 := h1257c.2.2.2
                      linarith only [hlam, p1257_0]
                  · linarith only [h1250, h1254, h1256, hlam]
                · linarith only [h1250, h1254, h1255, h2, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h1178, h1254, h2, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1286 | h1286
      · linarith only [h1, h1179, h1286, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1288 | h1288
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1289 | h1289
          · linarith only [h1, h1289, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1291 | h1291
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1292 | h1292
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1293 | h1293
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1294 | h1294
                  · rcases h0bigk with h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c | h1295c
                    · have p1295_0 := h1295c.1
                      have p1295_1 := h1295c.2.1
                      have p1295_2 := h1295c.2.2.1
                      have p1295_3 := h1295c.2.2.2
                      linarith only [hlam, p1295_0]
                    · have p1295_0 := h1295c.1
                      have p1295_1 := h1295c.2.1
                      have p1295_2 := h1295c.2.2.1
                      have p1295_3 := h1295c.2.2.2
                      linarith only [h1289, h1291, h1294, h2, hc02, hc14, hc34, hlam, hphi, ht01, ht0b, ht23, ht45, ht5b, p1295_1, u4ehi4]
                    · have p1295_0 := h1295c.1
                      have p1295_1 := h1295c.2.1
                      have p1295_2 := h1295c.2.2.1
                      have p1295_3 := h1295c.2.2.2
                      linarith only [h1291, h1294, h2, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1295_1, u4ehi4]
                    · have p1295_0 := h1295c.1
                      have p1295_1 := h1295c.2.1
                      have p1295_2 := h1295c.2.2.1
                      have p1295_3 := h1295c.2.2.2
                      linarith only [h2, hlam, p1295_1]
                    · have p1295_0 := h1295c.1
                      have p1295_1 := h1295c.2.1
                      have p1295_2 := h1295c.2.2.1
                      have p1295_3 := h1295c.2.2.2
                      linarith only [h2, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p1295_1]
                    · have p1295_0 := h1295c.1
                      have p1295_1 := h1295c.2.1
                      have p1295_2 := h1295c.2.2.1
                      have p1295_3 := h1295c.2.2.2
                      linarith only [h0, hlam, p1295_0]
                    · have p1295_0 := h1295c.1
                      have p1295_1 := h1295c.2.1
                      have p1295_2 := h1295c.2.2.1
                      have p1295_3 := h1295c.2.2.2
                      linarith only [hlam, p1295_0]
                    · have p1295_0 := h1295c.1
                      have p1295_1 := h1295c.2.1
                      have p1295_2 := h1295c.2.2.1
                      have p1295_3 := h1295c.2.2.2
                      linarith only [h1179, hlam, p1295_0]
                    · have p1295_0 := h1295c.1
                      have p1295_1 := h1295c.2.1
                      have p1295_2 := h1295c.2.2.1
                      have p1295_3 := h1295c.2.2.2
                      linarith only [h1286, hlam, p1295_1]
                    · have p1295_0 := h1295c.1
                      have p1295_1 := h1295c.2.1
                      have p1295_2 := h1295c.2.2.1
                      have p1295_3 := h1295c.2.2.2
                      linarith only [h0, h1178, h2, hc14, hc15, hlam, hphi, ht01, ht0b, ht5b, p1295_1]
                    · have p1295_0 := h1295c.1
                      have p1295_1 := h1295c.2.1
                      have p1295_2 := h1295c.2.2.1
                      have p1295_3 := h1295c.2.2.2
                      linarith only [h1, hlam, p1295_1]
                    · have p1295_0 := h1295c.1
                      have p1295_1 := h1295c.2.1
                      have p1295_2 := h1295c.2.2.1
                      have p1295_3 := h1295c.2.2.2
                      linarith only [h1289, hc02, hc34, hlam, hphi, ht23, p1295_1]
                    · have p1295_0 := h1295c.1
                      have p1295_1 := h1295c.2.1
                      have p1295_2 := h1295c.2.2.1
                      have p1295_3 := h1295c.2.2.2
                      linarith only [hlam, p1295_0]
                    · have p1295_0 := h1295c.1
                      have p1295_1 := h1295c.2.1
                      have p1295_2 := h1295c.2.2.1
                      have p1295_3 := h1295c.2.2.2
                      linarith only [h1289, hlam, p1295_1]
                    · have p1295_0 := h1295c.1
                      have p1295_1 := h1295c.2.1
                      have p1295_2 := h1295c.2.2.1
                      have p1295_3 := h1295c.2.2.2
                      linarith only [h1178, h1289, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1295_1]
                    · have p1295_0 := h1295c.1
                      have p1295_1 := h1295c.2.1
                      have p1295_2 := h1295c.2.2.1
                      have p1295_3 := h1295c.2.2.2
                      linarith only [h1286, hc01, hc24, hlam, hphi, ht12, p1295_1]
                    · have p1295_0 := h1295c.1
                      have p1295_1 := h1295c.2.1
                      have p1295_2 := h1295c.2.2.1
                      have p1295_3 := h1295c.2.2.2
                      linarith only [h1286, h1288, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1295_1]
                    · have p1295_0 := h1295c.1
                      have p1295_1 := h1295c.2.1
                      have p1295_2 := h1295c.2.2.1
                      have p1295_3 := h1295c.2.2.2
                      linarith only [h1289, hc03, hc34, hlam, hphi, p1295_1]
                    · have p1295_0 := h1295c.1
                      have p1295_1 := h1295c.2.1
                      have p1295_2 := h1295c.2.2.1
                      have p1295_3 := h1295c.2.2.2
                      linarith only [hlam, p1295_0]
                    · have p1295_0 := h1295c.1
                      have p1295_1 := h1295c.2.1
                      have p1295_2 := h1295c.2.2.1
                      have p1295_3 := h1295c.2.2.2
                      linarith only [h1289, h1291, h1294, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1295_1, u4ehi4]
                    · have p1295_0 := h1295c.1
                      have p1295_1 := h1295c.2.1
                      have p1295_2 := h1295c.2.2.1
                      have p1295_3 := h1295c.2.2.2
                      linarith only [h1178, hlam, p1295_0]
                    · have p1295_0 := h1295c.1
                      have p1295_1 := h1295c.2.1
                      have p1295_2 := h1295c.2.2.1
                      have p1295_3 := h1295c.2.2.2
                      linarith only [h1288, hlam, p1295_1]
                    · have p1295_0 := h1295c.1
                      have p1295_1 := h1295c.2.1
                      have p1295_2 := h1295c.2.2.1
                      have p1295_3 := h1295c.2.2.2
                      linarith only [h1291, hlam, p1295_0]
                    · have p1295_0 := h1295c.1
                      have p1295_1 := h1295c.2.1
                      have p1295_2 := h1295c.2.2.1
                      have p1295_3 := h1295c.2.2.2
                      linarith only [h1292, hlam, p1295_1]
                    · have p1295_0 := h1295c.1
                      have p1295_1 := h1295c.2.1
                      have p1295_2 := h1295c.2.2.1
                      have p1295_3 := h1295c.2.2.2
                      linarith only [hlam, p1295_0]
                  · linarith only [h1289, h1292, h1294, hlam]
                · linarith only [h0, h1288, h1292, h1293, h2, hlam]
              · linarith only [h1, h1179, h1288, h1292, h2, hlam]
            · linarith only [h1179, h1288, h1291, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1325 | h1325
          · linarith only [h1, h1325, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1327 | h1327
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1328 | h1328
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1329 | h1329
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1330 | h1330
                  · rcases h0bigk with h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c
                    · have p1331_0 := h1331c.1
                      have p1331_1 := h1331c.2.1
                      have p1331_2 := h1331c.2.2.1
                      have p1331_3 := h1331c.2.2.2
                      linarith only [hlam, p1331_0]
                    · have p1331_0 := h1331c.1
                      have p1331_1 := h1331c.2.1
                      have p1331_2 := h1331c.2.2.1
                      have p1331_3 := h1331c.2.2.2
                      linarith only [h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1331_1]
                    · have p1331_0 := h1331c.1
                      have p1331_1 := h1331c.2.1
                      have p1331_2 := h1331c.2.2.1
                      have p1331_3 := h1331c.2.2.2
                      linarith only [h2, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1331_1]
                    · have p1331_0 := h1331c.1
                      have p1331_1 := h1331c.2.1
                      have p1331_2 := h1331c.2.2.1
                      have p1331_3 := h1331c.2.2.2
                      linarith only [h2, hlam, p1331_1]
                    · have p1331_0 := h1331c.1
                      have p1331_1 := h1331c.2.1
                      have p1331_2 := h1331c.2.2.1
                      have p1331_3 := h1331c.2.2.2
                      linarith only [h2, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p1331_1]
                    · have p1331_0 := h1331c.1
                      have p1331_1 := h1331c.2.1
                      have p1331_2 := h1331c.2.2.1
                      have p1331_3 := h1331c.2.2.2
                      linarith only [h0, hlam, p1331_0]
                    · have p1331_0 := h1331c.1
                      have p1331_1 := h1331c.2.1
                      have p1331_2 := h1331c.2.2.1
                      have p1331_3 := h1331c.2.2.2
                      linarith only [hlam, p1331_0]
                    · have p1331_0 := h1331c.1
                      have p1331_1 := h1331c.2.1
                      have p1331_2 := h1331c.2.2.1
                      have p1331_3 := h1331c.2.2.2
                      linarith only [h1179, hlam, p1331_0]
                    · have p1331_0 := h1331c.1
                      have p1331_1 := h1331c.2.1
                      have p1331_2 := h1331c.2.2.1
                      have p1331_3 := h1331c.2.2.2
                      linarith only [h1286, hlam, p1331_1]
                    · have p1331_0 := h1331c.1
                      have p1331_1 := h1331c.2.1
                      have p1331_2 := h1331c.2.2.1
                      have p1331_3 := h1331c.2.2.2
                      linarith only [h1288, hlam, p1331_0]
                    · have p1331_0 := h1331c.1
                      have p1331_1 := h1331c.2.1
                      have p1331_2 := h1331c.2.2.1
                      have p1331_3 := h1331c.2.2.2
                      linarith only [h1, hlam, p1331_1]
                    · have p1331_0 := h1331c.1
                      have p1331_1 := h1331c.2.1
                      have p1331_2 := h1331c.2.2.1
                      have p1331_3 := h1331c.2.2.2
                      linarith only [h0, h1325, hc12, hc34, hlam, hphi, ht23, p1331_1]
                    · have p1331_0 := h1331c.1
                      have p1331_1 := h1331c.2.1
                      have p1331_2 := h1331c.2.2.1
                      have p1331_3 := h1331c.2.2.2
                      linarith only [hlam, p1331_0]
                    · have p1331_0 := h1331c.1
                      have p1331_1 := h1331c.2.1
                      have p1331_2 := h1331c.2.2.1
                      have p1331_3 := h1331c.2.2.2
                      linarith only [h1325, hlam, p1331_1]
                    · have p1331_0 := h1331c.1
                      have p1331_1 := h1331c.2.1
                      have p1331_2 := h1331c.2.2.1
                      have p1331_3 := h1331c.2.2.2
                      linarith only [h0, h1288, h1325, hc12, hc34, hlam, hphi, ht23, p1331_1]
                    · have p1331_0 := h1331c.1
                      have p1331_1 := h1331c.2.1
                      have p1331_2 := h1331c.2.2.1
                      have p1331_3 := h1331c.2.2.2
                      linarith only [h0, h1325, h1327, h1330, hc04, hc12, hc34, hlam, hphi, ht0b, ht23, ht45, ht5b, p1331_1, u4ehi4]
                    · have p1331_0 := h1331c.1
                      have p1331_1 := h1331c.2.1
                      have p1331_2 := h1331c.2.2.1
                      have p1331_3 := h1331c.2.2.2
                      linarith only [h0, h1286, hc12, hc24, hlam, hphi, p1331_1]
                    · have p1331_0 := h1331c.1
                      have p1331_1 := h1331c.2.1
                      have p1331_2 := h1331c.2.2.1
                      have p1331_3 := h1331c.2.2.2
                      linarith only [h1325, h1327, h1330, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1331_1, u4ehi4]
                    · have p1331_0 := h1331c.1
                      have p1331_1 := h1331c.2.1
                      have p1331_2 := h1331c.2.2.1
                      have p1331_3 := h1331c.2.2.2
                      linarith only [hlam, p1331_0]
                    · have p1331_0 := h1331c.1
                      have p1331_1 := h1331c.2.1
                      have p1331_2 := h1331c.2.2.1
                      have p1331_3 := h1331c.2.2.2
                      linarith only [h1325, h1327, h1330, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1331_1, u4ehi4]
                    · have p1331_0 := h1331c.1
                      have p1331_1 := h1331c.2.1
                      have p1331_2 := h1331c.2.2.1
                      have p1331_3 := h1331c.2.2.2
                      linarith only [h1178, hlam, p1331_0]
                    · have p1331_0 := h1331c.1
                      have p1331_1 := h1331c.2.1
                      have p1331_2 := h1331c.2.2.1
                      have p1331_3 := h1331c.2.2.2
                      linarith only [h0, h1178, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1331_1]
                    · have p1331_0 := h1331c.1
                      have p1331_1 := h1331c.2.1
                      have p1331_2 := h1331c.2.2.1
                      have p1331_3 := h1331c.2.2.2
                      linarith only [h1327, hlam, p1331_0]
                    · have p1331_0 := h1331c.1
                      have p1331_1 := h1331c.2.1
                      have p1331_2 := h1331c.2.2.1
                      have p1331_3 := h1331c.2.2.2
                      linarith only [h1328, hlam, p1331_1]
                    · have p1331_0 := h1331c.1
                      have p1331_1 := h1331c.2.1
                      have p1331_2 := h1331c.2.2.1
                      have p1331_3 := h1331c.2.2.2
                      linarith only [hlam, p1331_0]
                  · linarith only [h1325, h1328, h1330, hlam]
                · linarith only [h1178, h1325, h1327, h1328, h1329, h2, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
              · linarith only [h1, h1327, h1328, h2, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1360 | h1360
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1361 | h1361
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1362 | h1362
                  · rcases h0bigk with h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c | h1363c
                    · have p1363_0 := h1363c.1
                      have p1363_1 := h1363c.2.1
                      have p1363_2 := h1363c.2.2.1
                      have p1363_3 := h1363c.2.2.2
                      linarith only [hlam, p1363_0]
                    · have p1363_0 := h1363c.1
                      have p1363_1 := h1363c.2.1
                      have p1363_2 := h1363c.2.2.1
                      have p1363_3 := h1363c.2.2.2
                      linarith only [h0, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1363_1]
                    · have p1363_0 := h1363c.1
                      have p1363_1 := h1363c.2.1
                      have p1363_2 := h1363c.2.2.1
                      have p1363_3 := h1363c.2.2.2
                      linarith only [h2, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1363_1]
                    · have p1363_0 := h1363c.1
                      have p1363_1 := h1363c.2.1
                      have p1363_2 := h1363c.2.2.1
                      have p1363_3 := h1363c.2.2.2
                      linarith only [h2, hlam, p1363_1]
                    · have p1363_0 := h1363c.1
                      have p1363_1 := h1363c.2.1
                      have p1363_2 := h1363c.2.2.1
                      have p1363_3 := h1363c.2.2.2
                      linarith only [h2, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p1363_1]
                    · have p1363_0 := h1363c.1
                      have p1363_1 := h1363c.2.1
                      have p1363_2 := h1363c.2.2.1
                      have p1363_3 := h1363c.2.2.2
                      linarith only [h0, hlam, p1363_0]
                    · have p1363_0 := h1363c.1
                      have p1363_1 := h1363c.2.1
                      have p1363_2 := h1363c.2.2.1
                      have p1363_3 := h1363c.2.2.2
                      linarith only [hlam, p1363_0]
                    · have p1363_0 := h1363c.1
                      have p1363_1 := h1363c.2.1
                      have p1363_2 := h1363c.2.2.1
                      have p1363_3 := h1363c.2.2.2
                      linarith only [h1179, hlam, p1363_0]
                    · have p1363_0 := h1363c.1
                      have p1363_1 := h1363c.2.1
                      have p1363_2 := h1363c.2.2.1
                      have p1363_3 := h1363c.2.2.2
                      linarith only [h1286, hlam, p1363_1]
                    · have p1363_0 := h1363c.1
                      have p1363_1 := h1363c.2.1
                      have p1363_2 := h1363c.2.2.1
                      have p1363_3 := h1363c.2.2.2
                      linarith only [h1288, hlam, p1363_0]
                    · have p1363_0 := h1363c.1
                      have p1363_1 := h1363c.2.1
                      have p1363_2 := h1363c.2.2.1
                      have p1363_3 := h1363c.2.2.2
                      linarith only [h1, hlam, p1363_1]
                    · have p1363_0 := h1363c.1
                      have p1363_1 := h1363c.2.1
                      have p1363_2 := h1363c.2.2.1
                      have p1363_3 := h1363c.2.2.2
                      linarith only [h0, h1, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1363_1]
                    · have p1363_0 := h1363c.1
                      have p1363_1 := h1363c.2.1
                      have p1363_2 := h1363c.2.2.1
                      have p1363_3 := h1363c.2.2.2
                      linarith only [hlam, p1363_0]
                    · have p1363_0 := h1363c.1
                      have p1363_1 := h1363c.2.1
                      have p1363_2 := h1363c.2.2.1
                      have p1363_3 := h1363c.2.2.2
                      linarith only [h1325, hlam, p1363_1]
                    · have p1363_0 := h1363c.1
                      have p1363_1 := h1363c.2.1
                      have p1363_2 := h1363c.2.2.1
                      have p1363_3 := h1363c.2.2.2
                      linarith only [h1327, hlam, p1363_1]
                    · have p1363_0 := h1363c.1
                      have p1363_1 := h1363c.2.1
                      have p1363_2 := h1363c.2.2.1
                      have p1363_3 := h1363c.2.2.2
                      linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1363_1]
                    · have p1363_0 := h1363c.1
                      have p1363_1 := h1363c.2.1
                      have p1363_2 := h1363c.2.2.1
                      have p1363_3 := h1363c.2.2.2
                      linarith only [h0, h1286, hc12, hc24, hlam, hphi, p1363_1]
                    · have p1363_0 := h1363c.1
                      have p1363_1 := h1363c.2.1
                      have p1363_2 := h1363c.2.2.1
                      have p1363_3 := h1363c.2.2.2
                      linarith only [h1325, hc03, hc34, hlam, hphi, p1363_1]
                    · have p1363_0 := h1363c.1
                      have p1363_1 := h1363c.2.1
                      have p1363_2 := h1363c.2.2.1
                      have p1363_3 := h1363c.2.2.2
                      linarith only [hlam, p1363_0]
                    · have p1363_0 := h1363c.1
                      have p1363_1 := h1363c.2.1
                      have p1363_2 := h1363c.2.2.1
                      have p1363_3 := h1363c.2.2.2
                      linarith only [h1178, h1325, h1361, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1363_1, u4ehi4]
                    · have p1363_0 := h1363c.1
                      have p1363_1 := h1363c.2.1
                      have p1363_2 := h1363c.2.2.1
                      have p1363_3 := h1363c.2.2.2
                      linarith only [h1178, hlam, p1363_0]
                    · have p1363_0 := h1363c.1
                      have p1363_1 := h1363c.2.1
                      have p1363_2 := h1363c.2.2.1
                      have p1363_3 := h1363c.2.2.2
                      linarith only [h0, h1178, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1363_1]
                    · have p1363_0 := h1363c.1
                      have p1363_1 := h1363c.2.1
                      have p1363_2 := h1363c.2.2.1
                      have p1363_3 := h1363c.2.2.2
                      linarith only [h0, h1178, h1179, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1363_1]
                    · have p1363_0 := h1363c.1
                      have p1363_1 := h1363c.2.1
                      have p1363_2 := h1363c.2.2.1
                      have p1363_3 := h1363c.2.2.2
                      linarith only [h1360, hlam, p1363_1]
                    · have p1363_0 := h1363c.1
                      have p1363_1 := h1363c.2.1
                      have p1363_2 := h1363c.2.2.1
                      have p1363_3 := h1363c.2.2.2
                      linarith only [hlam, p1363_0]
                  · linarith only [h1325, h1360, h1362, hlam]
                · linarith only [h1325, h1360, h1361, h2, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h1178, h1360, h2, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1392 | h1392
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1393 | h1393
      · linarith only [h0, h1393, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1395 | h1395
        · linarith only [h0, h1178, h1395, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1397 | h1397
          · linarith only [h1, h1397, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1399 | h1399
            · linarith only [h0, h1178, h1392, h1399, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1401 | h1401
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1402 | h1402
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1403 | h1403
                  · rcases h0bigk with h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c
                    · have p1404_0 := h1404c.1
                      have p1404_1 := h1404c.2.1
                      have p1404_2 := h1404c.2.2.1
                      have p1404_3 := h1404c.2.2.2
                      linarith only [hlam, p1404_0]
                    · have p1404_0 := h1404c.1
                      have p1404_1 := h1404c.2.1
                      have p1404_2 := h1404c.2.2.1
                      have p1404_3 := h1404c.2.2.2
                      linarith only [h1178, h1402, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1404_1]
                    · have p1404_0 := h1404c.1
                      have p1404_1 := h1404c.2.1
                      have p1404_2 := h1404c.2.2.1
                      have p1404_3 := h1404c.2.2.2
                      linarith only [h1178, h1402, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1404_1]
                    · have p1404_0 := h1404c.1
                      have p1404_1 := h1404c.2.1
                      have p1404_2 := h1404c.2.2.1
                      have p1404_3 := h1404c.2.2.2
                      linarith only [h2, hlam, p1404_1]
                    · have p1404_0 := h1404c.1
                      have p1404_1 := h1404c.2.1
                      have p1404_2 := h1404c.2.2.1
                      have p1404_3 := h1404c.2.2.2
                      linarith only [h1178, hlam, p1404_1]
                    · have p1404_0 := h1404c.1
                      have p1404_1 := h1404c.2.1
                      have p1404_2 := h1404c.2.2.1
                      have p1404_3 := h1404c.2.2.2
                      linarith only [h0, hlam, p1404_0]
                    · have p1404_0 := h1404c.1
                      have p1404_1 := h1404c.2.1
                      have p1404_2 := h1404c.2.2.1
                      have p1404_3 := h1404c.2.2.2
                      linarith only [hlam, p1404_0]
                    · have p1404_0 := h1404c.1
                      have p1404_1 := h1404c.2.1
                      have p1404_2 := h1404c.2.2.1
                      have p1404_3 := h1404c.2.2.2
                      linarith only [h1, h1393, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1404_1]
                    · have p1404_0 := h1404c.1
                      have p1404_1 := h1404c.2.1
                      have p1404_2 := h1404c.2.2.1
                      have p1404_3 := h1404c.2.2.2
                      linarith only [h1393, hlam, p1404_1]
                    · have p1404_0 := h1404c.1
                      have p1404_1 := h1404c.2.1
                      have p1404_2 := h1404c.2.2.1
                      have p1404_3 := h1404c.2.2.2
                      linarith only [h1395, hlam, p1404_0]
                    · have p1404_0 := h1404c.1
                      have p1404_1 := h1404c.2.1
                      have p1404_2 := h1404c.2.2.1
                      have p1404_3 := h1404c.2.2.2
                      linarith only [h1, hlam, p1404_1]
                    · have p1404_0 := h1404c.1
                      have p1404_1 := h1404c.2.1
                      have p1404_2 := h1404c.2.2.1
                      have p1404_3 := h1404c.2.2.2
                      linarith only [h1392, hlam, p1404_1]
                    · have p1404_0 := h1404c.1
                      have p1404_1 := h1404c.2.1
                      have p1404_2 := h1404c.2.2.1
                      have p1404_3 := h1404c.2.2.2
                      linarith only [hlam, p1404_0]
                    · have p1404_0 := h1404c.1
                      have p1404_1 := h1404c.2.1
                      have p1404_2 := h1404c.2.2.1
                      have p1404_3 := h1404c.2.2.2
                      linarith only [h1397, hlam, p1404_1]
                    · have p1404_0 := h1404c.1
                      have p1404_1 := h1404c.2.1
                      have p1404_2 := h1404c.2.2.1
                      have p1404_3 := h1404c.2.2.2
                      linarith only [h1399, hlam, p1404_1]
                    · have p1404_0 := h1404c.1
                      have p1404_1 := h1404c.2.1
                      have p1404_2 := h1404c.2.2.1
                      have p1404_3 := h1404c.2.2.2
                      linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1404_1]
                    · have p1404_0 := h1404c.1
                      have p1404_1 := h1404c.2.1
                      have p1404_2 := h1404c.2.2.1
                      have p1404_3 := h1404c.2.2.2
                      linarith only [h1393, hc02, hc24, hlam, hphi, p1404_1]
                    · have p1404_0 := h1404c.1
                      have p1404_1 := h1404c.2.1
                      have p1404_2 := h1404c.2.2.1
                      have p1404_3 := h1404c.2.2.2
                      linarith only [h1, h1397, hc13, hc34, hlam, hphi, p1404_1]
                    · have p1404_0 := h1404c.1
                      have p1404_1 := h1404c.2.1
                      have p1404_2 := h1404c.2.2.1
                      have p1404_3 := h1404c.2.2.2
                      linarith only [hlam, p1404_0]
                    · have p1404_0 := h1404c.1
                      have p1404_1 := h1404c.2.1
                      have p1404_2 := h1404c.2.2.1
                      have p1404_3 := h1404c.2.2.2
                      linarith only [h0, h1178, h1397, hc12, hc34, hlam, hphi, ht23, p1404_1]
                    · have p1404_0 := h1404c.1
                      have p1404_1 := h1404c.2.1
                      have p1404_2 := h1404c.2.2.1
                      have p1404_3 := h1404c.2.2.2
                      linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1404_1]
                    · have p1404_0 := h1404c.1
                      have p1404_1 := h1404c.2.1
                      have p1404_2 := h1404c.2.2.1
                      have p1404_3 := h1404c.2.2.2
                      linarith only [h1392, h1399, hc23, hc35, hlam, hphi, p1404_1]
                    · have p1404_0 := h1404c.1
                      have p1404_1 := h1404c.2.1
                      have p1404_2 := h1404c.2.2.1
                      have p1404_3 := h1404c.2.2.2
                      linarith only [h1, h1399, hc13, hc35, hlam, hphi, p1404_1]
                    · have p1404_0 := h1404c.1
                      have p1404_1 := h1404c.2.1
                      have p1404_2 := h1404c.2.2.1
                      have p1404_3 := h1404c.2.2.2
                      linarith only [h1401, hlam, p1404_1]
                    · have p1404_0 := h1404c.1
                      have p1404_1 := h1404c.2.1
                      have p1404_2 := h1404c.2.2.1
                      have p1404_3 := h1404c.2.2.2
                      linarith only [hlam, p1404_0]
                  · linarith only [h1397, h1401, h1403, hlam]
                · linarith only [h0, h1397, h1401, h1402, h2, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1432 | h1432
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1433 | h1433
                  · linarith only [h0, h1401, h1433, h2, hc12, hc34, hlam, hphi, ht23]
                  · rcases h0bigk with h1435c | h1435c | h1435c | h1435c | h1435c | h1435c | h1435c | h1435c | h1435c | h1435c | h1435c | h1435c | h1435c | h1435c | h1435c | h1435c | h1435c | h1435c | h1435c | h1435c | h1435c | h1435c | h1435c | h1435c | h1435c
                    · have p1435_0 := h1435c.1
                      have p1435_1 := h1435c.2.1
                      have p1435_2 := h1435c.2.2.1
                      have p1435_3 := h1435c.2.2.2
                      linarith only [hlam, p1435_0]
                    · have p1435_0 := h1435c.1
                      have p1435_1 := h1435c.2.1
                      have p1435_2 := h1435c.2.2.1
                      have p1435_3 := h1435c.2.2.2
                      linarith only [h1392, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1435_1]
                    · have p1435_0 := h1435c.1
                      have p1435_1 := h1435c.2.1
                      have p1435_2 := h1435c.2.2.1
                      have p1435_3 := h1435c.2.2.2
                      linarith only [h1, h1397, h1433, h2, hc13, hc45, hlam, hphi, ht34, p1435_1]
                    · have p1435_0 := h1435c.1
                      have p1435_1 := h1435c.2.1
                      have p1435_2 := h1435c.2.2.1
                      have p1435_3 := h1435c.2.2.2
                      linarith only [h2, hlam, p1435_1]
                    · have p1435_0 := h1435c.1
                      have p1435_1 := h1435c.2.1
                      have p1435_2 := h1435c.2.2.1
                      have p1435_3 := h1435c.2.2.2
                      linarith only [h1178, hlam, p1435_1]
                    · have p1435_0 := h1435c.1
                      have p1435_1 := h1435c.2.1
                      have p1435_2 := h1435c.2.2.1
                      have p1435_3 := h1435c.2.2.2
                      linarith only [h0, hlam, p1435_0]
                    · have p1435_0 := h1435c.1
                      have p1435_1 := h1435c.2.1
                      have p1435_2 := h1435c.2.2.1
                      have p1435_3 := h1435c.2.2.2
                      linarith only [hlam, p1435_0]
                    · have p1435_0 := h1435c.1
                      have p1435_1 := h1435c.2.1
                      have p1435_2 := h1435c.2.2.1
                      have p1435_3 := h1435c.2.2.2
                      linarith only [h0, h1, h1397, h1433, h2, hc13, hc45, hlam, hphi, ht34, p1435_1]
                    · have p1435_0 := h1435c.1
                      have p1435_1 := h1435c.2.1
                      have p1435_2 := h1435c.2.2.1
                      have p1435_3 := h1435c.2.2.2
                      linarith only [h1393, hlam, p1435_1]
                    · have p1435_0 := h1435c.1
                      have p1435_1 := h1435c.2.1
                      have p1435_2 := h1435c.2.2.1
                      have p1435_3 := h1435c.2.2.2
                      linarith only [h1395, hlam, p1435_0]
                    · have p1435_0 := h1435c.1
                      have p1435_1 := h1435c.2.1
                      have p1435_2 := h1435c.2.2.1
                      have p1435_3 := h1435c.2.2.2
                      linarith only [h1, hlam, p1435_1]
                    · have p1435_0 := h1435c.1
                      have p1435_1 := h1435c.2.1
                      have p1435_2 := h1435c.2.2.1
                      have p1435_3 := h1435c.2.2.2
                      linarith only [h1392, hlam, p1435_1]
                    · have p1435_0 := h1435c.1
                      have p1435_1 := h1435c.2.1
                      have p1435_2 := h1435c.2.2.1
                      have p1435_3 := h1435c.2.2.2
                      linarith only [hlam, p1435_0]
                    · have p1435_0 := h1435c.1
                      have p1435_1 := h1435c.2.1
                      have p1435_2 := h1435c.2.2.1
                      have p1435_3 := h1435c.2.2.2
                      linarith only [h1397, hlam, p1435_1]
                    · have p1435_0 := h1435c.1
                      have p1435_1 := h1435c.2.1
                      have p1435_2 := h1435c.2.2.1
                      have p1435_3 := h1435c.2.2.2
                      linarith only [h1399, hlam, p1435_1]
                    · have p1435_0 := h1435c.1
                      have p1435_1 := h1435c.2.1
                      have p1435_2 := h1435c.2.2.1
                      have p1435_3 := h1435c.2.2.2
                      linarith only [h1397, h1433, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1435_1]
                    · have p1435_0 := h1435c.1
                      have p1435_1 := h1435c.2.1
                      have p1435_2 := h1435c.2.2.1
                      have p1435_3 := h1435c.2.2.2
                      linarith only [h1397, h1433, hc02, hc45, hlam, hphi, ht23, ht34, p1435_1]
                    · have p1435_0 := h1435c.1
                      have p1435_1 := h1435c.2.1
                      have p1435_2 := h1435c.2.2.1
                      have p1435_3 := h1435c.2.2.2
                      linarith only [h1, h1397, h1433, hc13, hc45, hlam, hphi, ht34, p1435_1]
                    · have p1435_0 := h1435c.1
                      have p1435_1 := h1435c.2.1
                      have p1435_2 := h1435c.2.2.1
                      have p1435_3 := h1435c.2.2.2
                      linarith only [hlam, p1435_0]
                    · have p1435_0 := h1435c.1
                      have p1435_1 := h1435c.2.1
                      have p1435_2 := h1435c.2.2.1
                      have p1435_3 := h1435c.2.2.2
                      linarith only [h1401, hlam, p1435_0]
                    · have p1435_0 := h1435c.1
                      have p1435_1 := h1435c.2.1
                      have p1435_2 := h1435c.2.2.1
                      have p1435_3 := h1435c.2.2.2
                      linarith only [h1395, hc01, hc25, hlam, hphi, ht12, p1435_1]
                    · have p1435_0 := h1435c.1
                      have p1435_1 := h1435c.2.1
                      have p1435_2 := h1435c.2.2.1
                      have p1435_3 := h1435c.2.2.2
                      linarith only [h1392, h1395, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1435_1]
                    · have p1435_0 := h1435c.1
                      have p1435_1 := h1435c.2.1
                      have p1435_2 := h1435c.2.2.1
                      have p1435_3 := h1435c.2.2.2
                      linarith only [h1, h1399, hc13, hc35, hlam, hphi, p1435_1]
                    · have p1435_0 := h1435c.1
                      have p1435_1 := h1435c.2.1
                      have p1435_2 := h1435c.2.2.1
                      have p1435_3 := h1435c.2.2.2
                      linarith only [h1401, hc45, hlam, hphi, p1435_1, u4ehi0]
                    · have p1435_0 := h1435c.1
                      have p1435_1 := h1435c.2.1
                      have p1435_2 := h1435c.2.2.1
                      have p1435_3 := h1435c.2.2.2
                      linarith only [hlam, p1435_0]
                · linarith only [h0, h1432, h2, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1462 | h1462
      · linarith only [h1, h1392, h1462, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1464 | h1464
        · linarith only [h1, h1178, h1392, h1464, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1466 | h1466
          · linarith only [h1, h1466, h2, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1468 | h1468
            · linarith only [h1, h1178, h1468, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1470 | h1470
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1471 | h1471
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1472 | h1472
                  · rcases h0bigk with h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c
                    · have p1473_0 := h1473c.1
                      have p1473_1 := h1473c.2.1
                      have p1473_2 := h1473c.2.2.1
                      have p1473_3 := h1473c.2.2.2
                      linarith only [hlam, p1473_0]
                    · have p1473_0 := h1473c.1
                      have p1473_1 := h1473c.2.1
                      have p1473_2 := h1473c.2.2.1
                      have p1473_3 := h1473c.2.2.2
                      linarith only [h0, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1473_1]
                    · have p1473_0 := h1473c.1
                      have p1473_1 := h1473c.2.1
                      have p1473_2 := h1473c.2.2.1
                      have p1473_3 := h1473c.2.2.2
                      linarith only [h2, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1473_1]
                    · have p1473_0 := h1473c.1
                      have p1473_1 := h1473c.2.1
                      have p1473_2 := h1473c.2.2.1
                      have p1473_3 := h1473c.2.2.2
                      linarith only [h2, hlam, p1473_1]
                    · have p1473_0 := h1473c.1
                      have p1473_1 := h1473c.2.1
                      have p1473_2 := h1473c.2.2.1
                      have p1473_3 := h1473c.2.2.2
                      linarith only [h1178, hlam, p1473_1]
                    · have p1473_0 := h1473c.1
                      have p1473_1 := h1473c.2.1
                      have p1473_2 := h1473c.2.2.1
                      have p1473_3 := h1473c.2.2.2
                      linarith only [h0, hlam, p1473_0]
                    · have p1473_0 := h1473c.1
                      have p1473_1 := h1473c.2.1
                      have p1473_2 := h1473c.2.2.1
                      have p1473_3 := h1473c.2.2.2
                      linarith only [hlam, p1473_0]
                    · have p1473_0 := h1473c.1
                      have p1473_1 := h1473c.2.1
                      have p1473_2 := h1473c.2.2.1
                      have p1473_3 := h1473c.2.2.2
                      linarith only [h1392, hlam, p1473_0]
                    · have p1473_0 := h1473c.1
                      have p1473_1 := h1473c.2.1
                      have p1473_2 := h1473c.2.2.1
                      have p1473_3 := h1473c.2.2.2
                      linarith only [h1462, hlam, p1473_1]
                    · have p1473_0 := h1473c.1
                      have p1473_1 := h1473c.2.1
                      have p1473_2 := h1473c.2.2.1
                      have p1473_3 := h1473c.2.2.2
                      linarith only [h1464, hlam, p1473_0]
                    · have p1473_0 := h1473c.1
                      have p1473_1 := h1473c.2.1
                      have p1473_2 := h1473c.2.2.1
                      have p1473_3 := h1473c.2.2.2
                      linarith only [h1, hlam, p1473_1]
                    · have p1473_0 := h1473c.1
                      have p1473_1 := h1473c.2.1
                      have p1473_2 := h1473c.2.2.1
                      have p1473_3 := h1473c.2.2.2
                      linarith only [h0, h1, h1178, h1471, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1473_1]
                    · have p1473_0 := h1473c.1
                      have p1473_1 := h1473c.2.1
                      have p1473_2 := h1473c.2.2.1
                      have p1473_3 := h1473c.2.2.2
                      linarith only [hlam, p1473_0]
                    · have p1473_0 := h1473c.1
                      have p1473_1 := h1473c.2.1
                      have p1473_2 := h1473c.2.2.1
                      have p1473_3 := h1473c.2.2.2
                      linarith only [h1466, hlam, p1473_1]
                    · have p1473_0 := h1473c.1
                      have p1473_1 := h1473c.2.1
                      have p1473_2 := h1473c.2.2.1
                      have p1473_3 := h1473c.2.2.2
                      linarith only [h1468, hlam, p1473_1]
                    · have p1473_0 := h1473c.1
                      have p1473_1 := h1473c.2.1
                      have p1473_2 := h1473c.2.2.1
                      have p1473_3 := h1473c.2.2.2
                      linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1473_1]
                    · have p1473_0 := h1473c.1
                      have p1473_1 := h1473c.2.1
                      have p1473_2 := h1473c.2.2.1
                      have p1473_3 := h1473c.2.2.2
                      linarith only [h0, h1462, hc12, hc24, hlam, hphi, p1473_1]
                    · have p1473_0 := h1473c.1
                      have p1473_1 := h1473c.2.1
                      have p1473_2 := h1473c.2.2.1
                      have p1473_3 := h1473c.2.2.2
                      linarith only [h1466, hc03, hc34, hlam, hphi, p1473_1]
                    · have p1473_0 := h1473c.1
                      have p1473_1 := h1473c.2.1
                      have p1473_2 := h1473c.2.2.1
                      have p1473_3 := h1473c.2.2.2
                      linarith only [hlam, p1473_0]
                    · have p1473_0 := h1473c.1
                      have p1473_1 := h1473c.2.1
                      have p1473_2 := h1473c.2.2.1
                      have p1473_3 := h1473c.2.2.2
                      linarith only [h0, h1178, h1466, hc12, hc34, hlam, hphi, ht23, p1473_1]
                    · have p1473_0 := h1473c.1
                      have p1473_1 := h1473c.2.1
                      have p1473_2 := h1473c.2.2.1
                      have p1473_3 := h1473c.2.2.2
                      linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1473_1]
                    · have p1473_0 := h1473c.1
                      have p1473_1 := h1473c.2.1
                      have p1473_2 := h1473c.2.2.1
                      have p1473_3 := h1473c.2.2.2
                      linarith only [h0, h1464, hc12, hc25, hlam, hphi, p1473_1]
                    · have p1473_0 := h1473c.1
                      have p1473_1 := h1473c.2.1
                      have p1473_2 := h1473c.2.2.1
                      have p1473_3 := h1473c.2.2.2
                      linarith only [h0, h1392, h1468, h1472, hc12, hc34, hlam, hphi, ht23, p1473_1]
                    · have p1473_0 := h1473c.1
                      have p1473_1 := h1473c.2.1
                      have p1473_2 := h1473c.2.2.1
                      have p1473_3 := h1473c.2.2.2
                      linarith only [h1470, hlam, p1473_1]
                    · have p1473_0 := h1473c.1
                      have p1473_1 := h1473c.2.1
                      have p1473_2 := h1473c.2.2.1
                      have p1473_3 := h1473c.2.2.2
                      linarith only [hlam, p1473_0]
                  · linarith only [h1466, h1470, h1472, hlam]
                · linarith only [h0, h1466, h1470, h1471, h2, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1501 | h1501
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1502 | h1502
                  · linarith only [h0, h1470, h1502, h2, hc12, hc34, hlam, hphi, ht23]
                  · rcases h0bigk with h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c | h1504c
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [hlam, p1504_0]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h0, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1504_1]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h0, h1392, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1504_1]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h2, hlam, p1504_1]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h1178, hlam, p1504_1]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h0, hlam, p1504_0]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [hlam, p1504_0]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h1392, hlam, p1504_0]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h1462, hlam, p1504_1]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h1464, hlam, p1504_0]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h1, hlam, p1504_1]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h0, h1, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1504_1]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [hlam, p1504_0]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h1466, hlam, p1504_1]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h1468, hlam, p1504_1]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h2, hc01, hc14, hlam, hphi, p1504_1]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h0, h1462, hc12, hc24, hlam, hphi, p1504_1]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h1466, h1501, h1502, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1504_1]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [hlam, p1504_0]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h1470, hlam, p1504_0]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h0, h1468, h1501, h1502, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1504_1]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h0, h1468, h1501, h1502, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1504_1]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h0, h1392, h1468, h1501, h1502, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1504_1]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [h1468, h1501, h1502, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1504_1, u4ehi0]
                    · have p1504_0 := h1504c.1
                      have p1504_1 := h1504c.2.1
                      have p1504_2 := h1504c.2.2.1
                      have p1504_3 := h1504c.2.2.2
                      linarith only [hlam, p1504_0]
                · linarith only [h0, h1501, h2, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 7676000 in
set_option maxHeartbeats 7676000 in
theorem r1l7_20_12_14_H_I_L_I_L_R_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0bigk := hb0.1
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_20_12_14_H_I_L_I_L_R_x0_x0_x0 m hb0 hb2 hb4 h0 h1 h2
  · exact r1l7_20_12_14_H_I_L_I_L_R_x0_x0_x1 m hb0 hb2 hb4 h0 h1 h2

end R2N4
