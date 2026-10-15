import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4354000 in
set_option maxHeartbeats 4354000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_R_L_R_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1082 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h3ehi := hb3.1
  have h4ehi := hb4.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1083 | h1083
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1084 | h1084
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1085 | h1085
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1086 | h1086
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1087 | h1087
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1088 | h1088
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1089 | h1089
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1090 | h1090
                · rcases h0bigk with h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [hlam, p1091_0]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h0, hlam, p1091_1]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h1085, h1090, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1091_1, u3ehi4]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1091_1, u4ehi0]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1091_1]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h1084, hc02, hc15, hlam, hphi, ht0b, ht5b, p1091_1]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [hlam, p1091_0]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h0, h1085, h1090, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1091_1, u3ehi4]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h0, h1089, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1091_1, u4ehi4]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h0, h1086, h1090, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1091_1, u3ehi4]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h1082, hlam, p1091_1]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h1085, hlam, p1091_1]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [hlam, p1091_0]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h1082, h1089, hc01, hlam, hphi, ht0b, ht45, ht5b, p1091_1, u4ehi4]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h0, h1082, h1086, h1090, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1091_1, u3ehi4]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h1083, hlam, p1091_0]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h0, h1082, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1091_1, u3ehi0]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h1087, hlam, p1091_0]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [hlam, p1091_0]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h1082, h1086, h1087, h1090, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1091_1, u3ehi4]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h1084, hlam, p1091_0]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h1086, hlam, p1091_1]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h1088, hlam, p1091_0]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [h1089, hlam, p1091_1]
                  · have p1091_0 := h1091c.1
                    have p1091_1 := h1091c.2.1
                    have p1091_2 := h1091c.2.2.1
                    have p1091_3 := h1091c.2.2.2
                    linarith only [hlam, p1091_0]
                · linarith only [h0, h1082, h1088, h1090, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1118 | h1118
                · rcases h0bigk with h1119c | h1119c | h1119c | h1119c | h1119c | h1119c | h1119c | h1119c | h1119c | h1119c | h1119c | h1119c | h1119c | h1119c | h1119c | h1119c | h1119c | h1119c | h1119c | h1119c | h1119c | h1119c | h1119c | h1119c | h1119c
                  · have p1119_0 := h1119c.1
                    have p1119_1 := h1119c.2.1
                    have p1119_2 := h1119c.2.2.1
                    have p1119_3 := h1119c.2.2.2
                    linarith only [hlam, p1119_0]
                  · have p1119_0 := h1119c.1
                    have p1119_1 := h1119c.2.1
                    have p1119_2 := h1119c.2.2.1
                    have p1119_3 := h1119c.2.2.2
                    linarith only [h0, hlam, p1119_1]
                  · have p1119_0 := h1119c.1
                    have p1119_1 := h1119c.2.1
                    have p1119_2 := h1119c.2.2.1
                    have p1119_3 := h1119c.2.2.2
                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1119_1, u3ehi0]
                  · have p1119_0 := h1119c.1
                    have p1119_1 := h1119c.2.1
                    have p1119_2 := h1119c.2.2.1
                    have p1119_3 := h1119c.2.2.2
                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1119_1, u4ehi0]
                  · have p1119_0 := h1119c.1
                    have p1119_1 := h1119c.2.1
                    have p1119_2 := h1119c.2.2.1
                    have p1119_3 := h1119c.2.2.2
                    linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1119_1]
                  · have p1119_0 := h1119c.1
                    have p1119_1 := h1119c.2.1
                    have p1119_2 := h1119c.2.2.1
                    have p1119_3 := h1119c.2.2.2
                    linarith only [h0, hc01, hc12, hlam, hphi, p1119_1]
                  · have p1119_0 := h1119c.1
                    have p1119_1 := h1119c.2.1
                    have p1119_2 := h1119c.2.2.1
                    have p1119_3 := h1119c.2.2.2
                    linarith only [hlam, p1119_0]
                  · have p1119_0 := h1119c.1
                    have p1119_1 := h1119c.2.1
                    have p1119_2 := h1119c.2.2.1
                    have p1119_3 := h1119c.2.2.2
                    linarith only [h0, h1082, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1119_1, u3ehi1]
                  · have p1119_0 := h1119c.1
                    have p1119_1 := h1119c.2.1
                    have p1119_2 := h1119c.2.2.1
                    have p1119_3 := h1119c.2.2.2
                    linarith only [h0, h1087, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1119_1, u3ehi3]
                  · have p1119_0 := h1119c.1
                    have p1119_1 := h1119c.2.1
                    have p1119_2 := h1119c.2.2.1
                    have p1119_3 := h1119c.2.2.2
                    linarith only [h0, h1086, h1118, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1119_1, u3ehi4]
                  · have p1119_0 := h1119c.1
                    have p1119_1 := h1119c.2.1
                    have p1119_2 := h1119c.2.2.1
                    have p1119_3 := h1119c.2.2.2
                    linarith only [h1082, hlam, p1119_1]
                  · have p1119_0 := h1119c.1
                    have p1119_1 := h1119c.2.1
                    have p1119_2 := h1119c.2.2.1
                    have p1119_3 := h1119c.2.2.2
                    linarith only [h1085, hlam, p1119_1]
                  · have p1119_0 := h1119c.1
                    have p1119_1 := h1119c.2.1
                    have p1119_2 := h1119c.2.2.1
                    have p1119_3 := h1119c.2.2.2
                    linarith only [hlam, p1119_0]
                  · have p1119_0 := h1119c.1
                    have p1119_1 := h1119c.2.1
                    have p1119_2 := h1119c.2.2.1
                    have p1119_3 := h1119c.2.2.2
                    linarith only [h1082, h1087, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1119_1, u3ehi3]
                  · have p1119_0 := h1119c.1
                    have p1119_1 := h1119c.2.1
                    have p1119_2 := h1119c.2.2.1
                    have p1119_3 := h1119c.2.2.2
                    linarith only [h0, h1082, h1086, h1118, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1119_1, u3ehi4]
                  · have p1119_0 := h1119c.1
                    have p1119_1 := h1119c.2.1
                    have p1119_2 := h1119c.2.2.1
                    have p1119_3 := h1119c.2.2.2
                    linarith only [h1083, hlam, p1119_0]
                  · have p1119_0 := h1119c.1
                    have p1119_1 := h1119c.2.1
                    have p1119_2 := h1119c.2.2.1
                    have p1119_3 := h1119c.2.2.2
                    linarith only [h0, h1082, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1119_1, u3ehi0]
                  · have p1119_0 := h1119c.1
                    have p1119_1 := h1119c.2.1
                    have p1119_2 := h1119c.2.2.1
                    have p1119_3 := h1119c.2.2.2
                    linarith only [h1087, hlam, p1119_0]
                  · have p1119_0 := h1119c.1
                    have p1119_1 := h1119c.2.1
                    have p1119_2 := h1119c.2.2.1
                    have p1119_3 := h1119c.2.2.2
                    linarith only [hlam, p1119_0]
                  · have p1119_0 := h1119c.1
                    have p1119_1 := h1119c.2.1
                    have p1119_2 := h1119c.2.2.1
                    have p1119_3 := h1119c.2.2.2
                    linarith only [h1089, hlam, p1119_0]
                  · have p1119_0 := h1119c.1
                    have p1119_1 := h1119c.2.1
                    have p1119_2 := h1119c.2.2.1
                    have p1119_3 := h1119c.2.2.2
                    linarith only [h1084, hlam, p1119_0]
                  · have p1119_0 := h1119c.1
                    have p1119_1 := h1119c.2.1
                    have p1119_2 := h1119c.2.2.1
                    have p1119_3 := h1119c.2.2.2
                    linarith only [h1086, hlam, p1119_1]
                  · have p1119_0 := h1119c.1
                    have p1119_1 := h1119c.2.1
                    have p1119_2 := h1119c.2.2.1
                    have p1119_3 := h1119c.2.2.2
                    linarith only [h1088, hlam, p1119_0]
                  · have p1119_0 := h1119c.1
                    have p1119_1 := h1119c.2.1
                    have p1119_2 := h1119c.2.2.1
                    have p1119_3 := h1119c.2.2.2
                    linarith only [hc05, hlam, hphi, ht0b, ht45, ht5b, p1119_1, u4ehi0]
                  · have p1119_0 := h1119c.1
                    have p1119_1 := h1119c.2.1
                    have p1119_2 := h1119c.2.2.1
                    have p1119_3 := h1119c.2.2.2
                    linarith only [hlam, p1119_0]
                · linarith only [h0, h1082, h1088, h1118, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h1087, h1088, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1147 | h1147
            · linarith only [h1087, h1147, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1149 | h1149
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1150 | h1150
                · linarith only [h1085, h1147, h1150, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                · rcases h0bigk with h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c
                  · have p1152_0 := h1152c.1
                    have p1152_1 := h1152c.2.1
                    have p1152_2 := h1152c.2.2.1
                    have p1152_3 := h1152c.2.2.2
                    linarith only [hlam, p1152_0]
                  · have p1152_0 := h1152c.1
                    have p1152_1 := h1152c.2.1
                    have p1152_2 := h1152c.2.2.1
                    have p1152_3 := h1152c.2.2.2
                    linarith only [h0, hlam, p1152_1]
                  · have p1152_0 := h1152c.1
                    have p1152_1 := h1152c.2.1
                    have p1152_2 := h1152c.2.2.1
                    have p1152_3 := h1152c.2.2.2
                    linarith only [h0, h1082, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1152_1, u3ehi1]
                  · have p1152_0 := h1152c.1
                    have p1152_1 := h1152c.2.1
                    have p1152_2 := h1152c.2.2.1
                    have p1152_3 := h1152c.2.2.2
                    linarith only [h0, h1149, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1152_1, u4ehi4]
                  · have p1152_0 := h1152c.1
                    have p1152_1 := h1152c.2.1
                    have p1152_2 := h1152c.2.2.1
                    have p1152_3 := h1152c.2.2.2
                    linarith only [h0, h1082, h1147, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1152_1, u3ehi1]
                  · have p1152_0 := h1152c.1
                    have p1152_1 := h1152c.2.1
                    have p1152_2 := h1152c.2.2.1
                    have p1152_3 := h1152c.2.2.2
                    linarith only [h0, hc01, hc12, hlam, hphi, p1152_1]
                  · have p1152_0 := h1152c.1
                    have p1152_1 := h1152c.2.1
                    have p1152_2 := h1152c.2.2.1
                    have p1152_3 := h1152c.2.2.2
                    linarith only [hlam, p1152_0]
                  · have p1152_0 := h1152c.1
                    have p1152_1 := h1152c.2.1
                    have p1152_2 := h1152c.2.2.1
                    have p1152_3 := h1152c.2.2.2
                    linarith only [h0, h1082, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1152_1, u3ehi1]
                  · have p1152_0 := h1152c.1
                    have p1152_1 := h1152c.2.1
                    have p1152_2 := h1152c.2.2.1
                    have p1152_3 := h1152c.2.2.2
                    linarith only [h0, h1149, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1152_1, u4ehi4]
                  · have p1152_0 := h1152c.1
                    have p1152_1 := h1152c.2.1
                    have p1152_2 := h1152c.2.2.1
                    have p1152_3 := h1152c.2.2.2
                    linarith only [h0, h1082, h1147, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1152_1, u3ehi1]
                  · have p1152_0 := h1152c.1
                    have p1152_1 := h1152c.2.1
                    have p1152_2 := h1152c.2.2.1
                    have p1152_3 := h1152c.2.2.2
                    linarith only [h1082, hlam, p1152_1]
                  · have p1152_0 := h1152c.1
                    have p1152_1 := h1152c.2.1
                    have p1152_2 := h1152c.2.2.1
                    have p1152_3 := h1152c.2.2.2
                    linarith only [h1085, hlam, p1152_1]
                  · have p1152_0 := h1152c.1
                    have p1152_1 := h1152c.2.1
                    have p1152_2 := h1152c.2.2.1
                    have p1152_3 := h1152c.2.2.2
                    linarith only [hlam, p1152_0]
                  · have p1152_0 := h1152c.1
                    have p1152_1 := h1152c.2.1
                    have p1152_2 := h1152c.2.2.1
                    have p1152_3 := h1152c.2.2.2
                    linarith only [h1087, hlam, p1152_1]
                  · have p1152_0 := h1152c.1
                    have p1152_1 := h1152c.2.1
                    have p1152_2 := h1152c.2.2.1
                    have p1152_3 := h1152c.2.2.2
                    linarith only [h1147, hlam, p1152_1]
                  · have p1152_0 := h1152c.1
                    have p1152_1 := h1152c.2.1
                    have p1152_2 := h1152c.2.2.1
                    have p1152_3 := h1152c.2.2.2
                    linarith only [h1083, hlam, p1152_0]
                  · have p1152_0 := h1152c.1
                    have p1152_1 := h1152c.2.1
                    have p1152_2 := h1152c.2.2.1
                    have p1152_3 := h1152c.2.2.2
                    linarith only [h0, h1082, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1152_1, u3ehi1]
                  · have p1152_0 := h1152c.1
                    have p1152_1 := h1152c.2.1
                    have p1152_2 := h1152c.2.2.1
                    have p1152_3 := h1152c.2.2.2
                    linarith only [h1082, h1083, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1152_1, u3ehi1]
                  · have p1152_0 := h1152c.1
                    have p1152_1 := h1152c.2.1
                    have p1152_2 := h1152c.2.2.1
                    have p1152_3 := h1152c.2.2.2
                    linarith only [hlam, p1152_0]
                  · have p1152_0 := h1152c.1
                    have p1152_1 := h1152c.2.1
                    have p1152_2 := h1152c.2.2.1
                    have p1152_3 := h1152c.2.2.2
                    linarith only [h0, h1082, h1083, h1147, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1152_1, u3ehi1]
                  · have p1152_0 := h1152c.1
                    have p1152_1 := h1152c.2.1
                    have p1152_2 := h1152c.2.2.1
                    have p1152_3 := h1152c.2.2.2
                    linarith only [h1084, hlam, p1152_0]
                  · have p1152_0 := h1152c.1
                    have p1152_1 := h1152c.2.1
                    have p1152_2 := h1152c.2.2.1
                    have p1152_3 := h1152c.2.2.2
                    linarith only [h1086, hlam, p1152_1]
                  · have p1152_0 := h1152c.1
                    have p1152_1 := h1152c.2.1
                    have p1152_2 := h1152c.2.2.1
                    have p1152_3 := h1152c.2.2.2
                    linarith only [h1082, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1152_1, u3ehi1]
                  · have p1152_0 := h1152c.1
                    have p1152_1 := h1152c.2.1
                    have p1152_2 := h1152c.2.2.1
                    have p1152_3 := h1152c.2.2.2
                    linarith only [h1149, hlam, p1152_1]
                  · have p1152_0 := h1152c.1
                    have p1152_1 := h1152c.2.1
                    have p1152_2 := h1152c.2.2.1
                    have p1152_3 := h1152c.2.2.2
                    linarith only [hlam, p1152_0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1178 | h1178
                · linarith only [h1085, h1087, h1178, hc34, hlam, hphi, u3ehi4]
                · rcases h0bigk with h1180c | h1180c | h1180c | h1180c | h1180c | h1180c | h1180c | h1180c | h1180c | h1180c | h1180c | h1180c | h1180c | h1180c | h1180c | h1180c | h1180c | h1180c | h1180c | h1180c | h1180c | h1180c | h1180c | h1180c | h1180c
                  · have p1180_0 := h1180c.1
                    have p1180_1 := h1180c.2.1
                    have p1180_2 := h1180c.2.2.1
                    have p1180_3 := h1180c.2.2.2
                    linarith only [hlam, p1180_0]
                  · have p1180_0 := h1180c.1
                    have p1180_1 := h1180c.2.1
                    have p1180_2 := h1180c.2.2.1
                    have p1180_3 := h1180c.2.2.2
                    linarith only [h0, hlam, p1180_1]
                  · have p1180_0 := h1180c.1
                    have p1180_1 := h1180c.2.1
                    have p1180_2 := h1180c.2.2.1
                    have p1180_3 := h1180c.2.2.2
                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1180_1, u3ehi0]
                  · have p1180_0 := h1180c.1
                    have p1180_1 := h1180c.2.1
                    have p1180_2 := h1180c.2.2.1
                    have p1180_3 := h1180c.2.2.2
                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1180_1, u4ehi0]
                  · have p1180_0 := h1180c.1
                    have p1180_1 := h1180c.2.1
                    have p1180_2 := h1180c.2.2.1
                    have p1180_3 := h1180c.2.2.2
                    linarith only [h0, h1083, h1149, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1180_1, u4ehi1]
                  · have p1180_0 := h1180c.1
                    have p1180_1 := h1180c.2.1
                    have p1180_2 := h1180c.2.2.1
                    have p1180_3 := h1180c.2.2.2
                    linarith only [h0, hc01, hc12, hlam, hphi, p1180_1]
                  · have p1180_0 := h1180c.1
                    have p1180_1 := h1180c.2.1
                    have p1180_2 := h1180c.2.2.1
                    have p1180_3 := h1180c.2.2.2
                    linarith only [hlam, p1180_0]
                  · have p1180_0 := h1180c.1
                    have p1180_1 := h1180c.2.1
                    have p1180_2 := h1180c.2.2.1
                    have p1180_3 := h1180c.2.2.2
                    linarith only [h0, h1085, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1180_1, u3ehi2]
                  · have p1180_0 := h1180c.1
                    have p1180_1 := h1180c.2.1
                    have p1180_2 := h1180c.2.2.1
                    have p1180_3 := h1180c.2.2.2
                    linarith only [h0, h1085, h1087, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1180_1, u3ehi2]
                  · have p1180_0 := h1180c.1
                    have p1180_1 := h1180c.2.1
                    have p1180_2 := h1180c.2.2.1
                    have p1180_3 := h1180c.2.2.2
                    linarith only [h0, h1085, h1087, h1149, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1180_1, u3ehi2]
                  · have p1180_0 := h1180c.1
                    have p1180_1 := h1180c.2.1
                    have p1180_2 := h1180c.2.2.1
                    have p1180_3 := h1180c.2.2.2
                    linarith only [h1082, hlam, p1180_1]
                  · have p1180_0 := h1180c.1
                    have p1180_1 := h1180c.2.1
                    have p1180_2 := h1180c.2.2.1
                    have p1180_3 := h1180c.2.2.2
                    linarith only [h1085, hlam, p1180_1]
                  · have p1180_0 := h1180c.1
                    have p1180_1 := h1180c.2.1
                    have p1180_2 := h1180c.2.2.1
                    have p1180_3 := h1180c.2.2.2
                    linarith only [hlam, p1180_0]
                  · have p1180_0 := h1180c.1
                    have p1180_1 := h1180c.2.1
                    have p1180_2 := h1180c.2.2.1
                    have p1180_3 := h1180c.2.2.2
                    linarith only [h1087, hlam, p1180_1]
                  · have p1180_0 := h1180c.1
                    have p1180_1 := h1180c.2.1
                    have p1180_2 := h1180c.2.2.1
                    have p1180_3 := h1180c.2.2.2
                    linarith only [h1147, hlam, p1180_1]
                  · have p1180_0 := h1180c.1
                    have p1180_1 := h1180c.2.1
                    have p1180_2 := h1180c.2.2.1
                    have p1180_3 := h1180c.2.2.2
                    linarith only [h1083, hlam, p1180_0]
                  · have p1180_0 := h1180c.1
                    have p1180_1 := h1180c.2.1
                    have p1180_2 := h1180c.2.2.1
                    have p1180_3 := h1180c.2.2.2
                    linarith only [h0, h1082, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1180_1, u3ehi1]
                  · have p1180_0 := h1180c.1
                    have p1180_1 := h1180c.2.1
                    have p1180_2 := h1180c.2.2.1
                    have p1180_3 := h1180c.2.2.2
                    linarith only [h1084, h1085, h1149, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1180_1, u3ehi2]
                  · have p1180_0 := h1180c.1
                    have p1180_1 := h1180c.2.1
                    have p1180_2 := h1180c.2.2.1
                    have p1180_3 := h1180c.2.2.2
                    linarith only [hlam, p1180_0]
                  · have p1180_0 := h1180c.1
                    have p1180_1 := h1180c.2.1
                    have p1180_2 := h1180c.2.2.1
                    have p1180_3 := h1180c.2.2.2
                    linarith only [h1149, hlam, p1180_0]
                  · have p1180_0 := h1180c.1
                    have p1180_1 := h1180c.2.1
                    have p1180_2 := h1180c.2.2.1
                    have p1180_3 := h1180c.2.2.2
                    linarith only [h1084, hlam, p1180_0]
                  · have p1180_0 := h1180c.1
                    have p1180_1 := h1180c.2.1
                    have p1180_2 := h1180c.2.2.1
                    have p1180_3 := h1180c.2.2.2
                    linarith only [h1086, hlam, p1180_1]
                  · have p1180_0 := h1180c.1
                    have p1180_1 := h1180c.2.1
                    have p1180_2 := h1180c.2.2.1
                    have p1180_3 := h1180c.2.2.2
                    linarith only [h0, h1084, h1085, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1180_1, u3ehi2]
                  · have p1180_0 := h1180c.1
                    have p1180_1 := h1180c.2.1
                    have p1180_2 := h1180c.2.2.1
                    have p1180_3 := h1180c.2.2.2
                    linarith only [h0, h1084, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1180_1, u4ehi0]
                  · have p1180_0 := h1180c.1
                    have p1180_1 := h1180c.2.1
                    have p1180_2 := h1180c.2.2.1
                    have p1180_3 := h1180c.2.2.2
                    linarith only [hlam, p1180_0]
        · linarith only [h0, h1084, h1086, hlam]
      · linarith only [h0, h1082, h1085, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1208 | h1208
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1209 | h1209
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1210 | h1210
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1211 | h1211
            · linarith only [h1082, h1084, h1211, hlam]
            · linarith only [h1210, h1211, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1214 | h1214
            · linarith only [h1210, h1214, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1216 | h1216
              · linarith only [h1083, h1084, h1216, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1218 | h1218
                · linarith only [h1208, h1214, h1218, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                · rcases h0bigk with h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [hlam, p1220_0]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h0, hlam, p1220_1]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h1082, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1220_1, u3ehi1]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h1084, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p1220_1, u4ehi0]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h1084, hlam, p1220_1]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h0, hc01, hc12, hlam, hphi, p1220_1]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [hlam, p1220_0]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h0, h1082, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1220_1, u3ehi1]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h0, h1082, h1210, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1220_1, u3ehi1]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h0, h1082, h1084, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1220_1, u3ehi1]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h1082, hlam, p1220_1]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h1208, hlam, p1220_1]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [hlam, p1220_0]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h1210, hlam, p1220_1]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h1214, hlam, p1220_1]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h1083, hlam, p1220_0]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h0, h1082, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1220_1, u3ehi1]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h1082, h1083, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1220_1, u3ehi1]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [hlam, p1220_0]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h1216, hlam, p1220_0]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h1083, h1209, hc02, hlam, hphi, ht0b, ht45, ht5b, p1220_1, u4ehi0]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h1209, hlam, p1220_1]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h1082, h1214, hc35, hlam, hphi, p1220_1, u3ehi1]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [h1082, h1210, h1216, hc45, hlam, hphi, ht34, p1220_1, u3ehi1]
                  · have p1220_0 := h1220c.1
                    have p1220_1 := h1220c.2.1
                    have p1220_2 := h1220c.2.2.1
                    have p1220_3 := h1220c.2.2.2
                    linarith only [hlam, p1220_0]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1246 | h1246
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1247 | h1247
            · linarith only [h1082, h1084, h1247, hlam]
            · linarith only [h1246, h1247, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1250 | h1250
            · linarith only [h1246, h1250, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1252 | h1252
              · linarith only [h0, h1083, h1209, h1252, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1254 | h1254
                · linarith only [h1208, h1209, h1250, h1254, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                · linarith only [h0, h1082, h1209, h1254, hc35, hlam, hphi, u3ehi1]
      · linarith only [h0, h1082, h1208, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1258 | h1258
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1259 | h1259
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1260 | h1260
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1261 | h1261
          · linarith only [h1082, h1083, h1261, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1263 | h1263
            · linarith only [h1261, h1263, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1265 | h1265
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1266 | h1266
                · linarith only [h1259, h1263, h1266, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                · rcases h0bigk with h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c | h1268c
                  · have p1268_0 := h1268c.1
                    have p1268_1 := h1268c.2.1
                    have p1268_2 := h1268c.2.2.1
                    have p1268_3 := h1268c.2.2.2
                    linarith only [hlam, p1268_0]
                  · have p1268_0 := h1268c.1
                    have p1268_1 := h1268c.2.1
                    have p1268_2 := h1268c.2.2.1
                    have p1268_3 := h1268c.2.2.2
                    linarith only [h0, hlam, p1268_1]
                  · have p1268_0 := h1268c.1
                    have p1268_1 := h1268c.2.1
                    have p1268_2 := h1268c.2.2.1
                    have p1268_3 := h1268c.2.2.2
                    linarith only [h1082, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1268_1, u3ehi1]
                  · have p1268_0 := h1268c.1
                    have p1268_1 := h1268c.2.1
                    have p1268_2 := h1268c.2.2.1
                    have p1268_3 := h1268c.2.2.2
                    linarith only [h1083, hlam, p1268_1]
                  · have p1268_0 := h1268c.1
                    have p1268_1 := h1268c.2.1
                    have p1268_2 := h1268c.2.2.1
                    have p1268_3 := h1268c.2.2.2
                    linarith only [h1082, h1083, h1263, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1268_1, u3ehi1]
                  · have p1268_0 := h1268c.1
                    have p1268_1 := h1268c.2.1
                    have p1268_2 := h1268c.2.2.1
                    have p1268_3 := h1268c.2.2.2
                    linarith only [h0, hc01, hc12, hlam, hphi, p1268_1]
                  · have p1268_0 := h1268c.1
                    have p1268_1 := h1268c.2.1
                    have p1268_2 := h1268c.2.2.1
                    have p1268_3 := h1268c.2.2.2
                    linarith only [hlam, p1268_0]
                  · have p1268_0 := h1268c.1
                    have p1268_1 := h1268c.2.1
                    have p1268_2 := h1268c.2.2.1
                    have p1268_3 := h1268c.2.2.2
                    linarith only [h0, h1082, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1268_1, u3ehi1]
                  · have p1268_0 := h1268c.1
                    have p1268_1 := h1268c.2.1
                    have p1268_2 := h1268c.2.2.1
                    have p1268_3 := h1268c.2.2.2
                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1268_1, u4ehi0]
                  · have p1268_0 := h1268c.1
                    have p1268_1 := h1268c.2.1
                    have p1268_2 := h1268c.2.2.1
                    have p1268_3 := h1268c.2.2.2
                    linarith only [h0, h1082, h1263, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1268_1, u3ehi1]
                  · have p1268_0 := h1268c.1
                    have p1268_1 := h1268c.2.1
                    have p1268_2 := h1268c.2.2.1
                    have p1268_3 := h1268c.2.2.2
                    linarith only [h1082, hlam, p1268_1]
                  · have p1268_0 := h1268c.1
                    have p1268_1 := h1268c.2.1
                    have p1268_2 := h1268c.2.2.1
                    have p1268_3 := h1268c.2.2.2
                    linarith only [h1259, hlam, p1268_1]
                  · have p1268_0 := h1268c.1
                    have p1268_1 := h1268c.2.1
                    have p1268_2 := h1268c.2.2.1
                    have p1268_3 := h1268c.2.2.2
                    linarith only [hlam, p1268_0]
                  · have p1268_0 := h1268c.1
                    have p1268_1 := h1268c.2.1
                    have p1268_2 := h1268c.2.2.1
                    have p1268_3 := h1268c.2.2.2
                    linarith only [h1261, hlam, p1268_1]
                  · have p1268_0 := h1268c.1
                    have p1268_1 := h1268c.2.1
                    have p1268_2 := h1268c.2.2.1
                    have p1268_3 := h1268c.2.2.2
                    linarith only [h1263, hlam, p1268_1]
                  · have p1268_0 := h1268c.1
                    have p1268_1 := h1268c.2.1
                    have p1268_2 := h1268c.2.2.1
                    have p1268_3 := h1268c.2.2.2
                    linarith only [h1082, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1268_1, u3ehi1]
                  · have p1268_0 := h1268c.1
                    have p1268_1 := h1268c.2.1
                    have p1268_2 := h1268c.2.2.1
                    have p1268_3 := h1268c.2.2.2
                    linarith only [h1261, hc02, hc34, hlam, hphi, ht23, p1268_1]
                  · have p1268_0 := h1268c.1
                    have p1268_1 := h1268c.2.1
                    have p1268_2 := h1268c.2.2.1
                    have p1268_3 := h1268c.2.2.2
                    linarith only [h1082, h1261, hc34, hlam, hphi, p1268_1, u3ehi1]
                  · have p1268_0 := h1268c.1
                    have p1268_1 := h1268c.2.1
                    have p1268_2 := h1268c.2.2.1
                    have p1268_3 := h1268c.2.2.2
                    linarith only [hlam, p1268_0]
                  · have p1268_0 := h1268c.1
                    have p1268_1 := h1268c.2.1
                    have p1268_2 := h1268c.2.2.1
                    have p1268_3 := h1268c.2.2.2
                    linarith only [h1082, h1261, h1263, hc34, hlam, hphi, p1268_1, u3ehi1]
                  · have p1268_0 := h1268c.1
                    have p1268_1 := h1268c.2.1
                    have p1268_2 := h1268c.2.2.1
                    have p1268_3 := h1268c.2.2.2
                    linarith only [h1258, hlam, p1268_0]
                  · have p1268_0 := h1268c.1
                    have p1268_1 := h1268c.2.1
                    have p1268_2 := h1268c.2.2.1
                    have p1268_3 := h1268c.2.2.2
                    linarith only [h1260, hlam, p1268_1]
                  · have p1268_0 := h1268c.1
                    have p1268_1 := h1268c.2.1
                    have p1268_2 := h1268c.2.2.1
                    have p1268_3 := h1268c.2.2.2
                    linarith only [h1082, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1268_1, u3ehi1]
                  · have p1268_0 := h1268c.1
                    have p1268_1 := h1268c.2.1
                    have p1268_2 := h1268c.2.2.1
                    have p1268_3 := h1268c.2.2.2
                    linarith only [h1265, hlam, p1268_1]
                  · have p1268_0 := h1268c.1
                    have p1268_1 := h1268c.2.1
                    have p1268_2 := h1268c.2.2.1
                    have p1268_3 := h1268c.2.2.2
                    linarith only [hlam, p1268_0]
              · linarith only [h1082, h1083, h1265, hc45, hlam, hphi, ht34, u3ehi1]
        · linarith only [h0, h1258, h1260, hlam]
      · linarith only [h0, h1082, h1259, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1297 | h1297
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1298 | h1298
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1299 | h1299
          · linarith only [h1082, h1083, h1299, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1301 | h1301
            · linarith only [h1299, h1301, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1303 | h1303
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1304 | h1304
                · linarith only [h1297, h1301, h1304, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                · rcases h0bigk with h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c
                  · have p1306_0 := h1306c.1
                    have p1306_1 := h1306c.2.1
                    have p1306_2 := h1306c.2.2.1
                    have p1306_3 := h1306c.2.2.2
                    linarith only [hlam, p1306_0]
                  · have p1306_0 := h1306c.1
                    have p1306_1 := h1306c.2.1
                    have p1306_2 := h1306c.2.2.1
                    have p1306_3 := h1306c.2.2.2
                    linarith only [h0, hlam, p1306_1]
                  · have p1306_0 := h1306c.1
                    have p1306_1 := h1306c.2.1
                    have p1306_2 := h1306c.2.2.1
                    have p1306_3 := h1306c.2.2.2
                    linarith only [h1082, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1306_1, u3ehi1]
                  · have p1306_0 := h1306c.1
                    have p1306_1 := h1306c.2.1
                    have p1306_2 := h1306c.2.2.1
                    have p1306_3 := h1306c.2.2.2
                    linarith only [h1083, hlam, p1306_1]
                  · have p1306_0 := h1306c.1
                    have p1306_1 := h1306c.2.1
                    have p1306_2 := h1306c.2.2.1
                    have p1306_3 := h1306c.2.2.2
                    linarith only [h1258, hlam, p1306_1]
                  · have p1306_0 := h1306c.1
                    have p1306_1 := h1306c.2.1
                    have p1306_2 := h1306c.2.2.1
                    have p1306_3 := h1306c.2.2.2
                    linarith only [h0, hc01, hc12, hlam, hphi, p1306_1]
                  · have p1306_0 := h1306c.1
                    have p1306_1 := h1306c.2.1
                    have p1306_2 := h1306c.2.2.1
                    have p1306_3 := h1306c.2.2.2
                    linarith only [hlam, p1306_0]
                  · have p1306_0 := h1306c.1
                    have p1306_1 := h1306c.2.1
                    have p1306_2 := h1306c.2.2.1
                    have p1306_3 := h1306c.2.2.2
                    linarith only [h0, h1082, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1306_1, u3ehi1]
                  · have p1306_0 := h1306c.1
                    have p1306_1 := h1306c.2.1
                    have p1306_2 := h1306c.2.2.1
                    have p1306_3 := h1306c.2.2.2
                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1306_1, u4ehi0]
                  · have p1306_0 := h1306c.1
                    have p1306_1 := h1306c.2.1
                    have p1306_2 := h1306c.2.2.1
                    have p1306_3 := h1306c.2.2.2
                    linarith only [h0, h1082, h1258, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1306_1, u3ehi1]
                  · have p1306_0 := h1306c.1
                    have p1306_1 := h1306c.2.1
                    have p1306_2 := h1306c.2.2.1
                    have p1306_3 := h1306c.2.2.2
                    linarith only [h1082, hlam, p1306_1]
                  · have p1306_0 := h1306c.1
                    have p1306_1 := h1306c.2.1
                    have p1306_2 := h1306c.2.2.1
                    have p1306_3 := h1306c.2.2.2
                    linarith only [h1297, hlam, p1306_1]
                  · have p1306_0 := h1306c.1
                    have p1306_1 := h1306c.2.1
                    have p1306_2 := h1306c.2.2.1
                    have p1306_3 := h1306c.2.2.2
                    linarith only [hlam, p1306_0]
                  · have p1306_0 := h1306c.1
                    have p1306_1 := h1306c.2.1
                    have p1306_2 := h1306c.2.2.1
                    have p1306_3 := h1306c.2.2.2
                    linarith only [h1299, hlam, p1306_1]
                  · have p1306_0 := h1306c.1
                    have p1306_1 := h1306c.2.1
                    have p1306_2 := h1306c.2.2.1
                    have p1306_3 := h1306c.2.2.2
                    linarith only [h1301, hlam, p1306_1]
                  · have p1306_0 := h1306c.1
                    have p1306_1 := h1306c.2.1
                    have p1306_2 := h1306c.2.2.1
                    have p1306_3 := h1306c.2.2.2
                    linarith only [h1082, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1306_1, u3ehi1]
                  · have p1306_0 := h1306c.1
                    have p1306_1 := h1306c.2.1
                    have p1306_2 := h1306c.2.2.1
                    have p1306_3 := h1306c.2.2.2
                    linarith only [h1299, hc02, hc34, hlam, hphi, ht23, p1306_1]
                  · have p1306_0 := h1306c.1
                    have p1306_1 := h1306c.2.1
                    have p1306_2 := h1306c.2.2.1
                    have p1306_3 := h1306c.2.2.2
                    linarith only [h1082, h1299, hc34, hlam, hphi, p1306_1, u3ehi1]
                  · have p1306_0 := h1306c.1
                    have p1306_1 := h1306c.2.1
                    have p1306_2 := h1306c.2.2.1
                    have p1306_3 := h1306c.2.2.2
                    linarith only [hlam, p1306_0]
                  · have p1306_0 := h1306c.1
                    have p1306_1 := h1306c.2.1
                    have p1306_2 := h1306c.2.2.1
                    have p1306_3 := h1306c.2.2.2
                    linarith only [h1082, h1258, h1299, hc34, hlam, hphi, p1306_1, u3ehi1]
                  · have p1306_0 := h1306c.1
                    have p1306_1 := h1306c.2.1
                    have p1306_2 := h1306c.2.2.1
                    have p1306_3 := h1306c.2.2.2
                    linarith only [h1082, h1298, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1306_1, u3ehi1]
                  · have p1306_0 := h1306c.1
                    have p1306_1 := h1306c.2.1
                    have p1306_2 := h1306c.2.2.1
                    have p1306_3 := h1306c.2.2.2
                    linarith only [h1298, hlam, p1306_1]
                  · have p1306_0 := h1306c.1
                    have p1306_1 := h1306c.2.1
                    have p1306_2 := h1306c.2.2.1
                    have p1306_3 := h1306c.2.2.2
                    linarith only [h1082, h1301, hc35, hlam, hphi, p1306_1, u3ehi1]
                  · have p1306_0 := h1306c.1
                    have p1306_1 := h1306c.2.1
                    have p1306_2 := h1306c.2.2.1
                    have p1306_3 := h1306c.2.2.2
                    linarith only [h1303, hlam, p1306_1]
                  · have p1306_0 := h1306c.1
                    have p1306_1 := h1306c.2.1
                    have p1306_2 := h1306c.2.2.1
                    have p1306_3 := h1306c.2.2.2
                    linarith only [hlam, p1306_0]
              · linarith only [h1082, h1083, h1303, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1333 | h1333
          · linarith only [h1082, h1083, h1333, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1335 | h1335
            · linarith only [h1333, h1335, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1337 | h1337
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1338 | h1338
                · linarith only [h1297, h1335, h1338, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                · linarith only [h0, h1082, h1298, h1338, hc35, hlam, hphi, u3ehi1]
              · linarith only [h1082, h1083, h1337, hc45, hlam, hphi, ht34, u3ehi1]
      · linarith only [h0, h1082, h1297, hlam]

set_option maxHeartbeats 4354000 in
set_option maxHeartbeats 4354000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_R_L_R_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1082 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1343 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h3ehi := hb3.1
  have h4ehi := hb4.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1344 | h1344
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1345 | h1345
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1346 | h1346
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1347 | h1347
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1348 | h1348
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1349 | h1349
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1350 | h1350
              · rcases h0bigk with h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c | h1351c
                · have p1351_0 := h1351c.1
                  have p1351_1 := h1351c.2.1
                  have p1351_2 := h1351c.2.2.1
                  have p1351_3 := h1351c.2.2.2
                  linarith only [hlam, p1351_0]
                · have p1351_0 := h1351c.1
                  have p1351_1 := h1351c.2.1
                  have p1351_2 := h1351c.2.2.1
                  have p1351_3 := h1351c.2.2.2
                  linarith only [h0, hlam, p1351_1]
                · have p1351_0 := h1351c.1
                  have p1351_1 := h1351c.2.1
                  have p1351_2 := h1351c.2.2.1
                  have p1351_3 := h1351c.2.2.2
                  linarith only [h1082, hlam, p1351_0]
                · have p1351_0 := h1351c.1
                  have p1351_1 := h1351c.2.1
                  have p1351_2 := h1351c.2.2.1
                  have p1351_3 := h1351c.2.2.2
                  linarith only [h1082, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1351_1, u4ehi0]
                · have p1351_0 := h1351c.1
                  have p1351_1 := h1351c.2.1
                  have p1351_2 := h1351c.2.2.1
                  have p1351_3 := h1351c.2.2.2
                  linarith only [h1082, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p1351_1]
                · have p1351_0 := h1351c.1
                  have p1351_1 := h1351c.2.1
                  have p1351_2 := h1351c.2.2.1
                  have p1351_3 := h1351c.2.2.2
                  linarith only [h1343, hc02, hlam, hphi, ht0b, ht45, ht5b, p1351_1, u4ehi1]
                · have p1351_0 := h1351c.1
                  have p1351_1 := h1351c.2.1
                  have p1351_2 := h1351c.2.2.1
                  have p1351_3 := h1351c.2.2.2
                  linarith only [hlam, p1351_0]
                · have p1351_0 := h1351c.1
                  have p1351_1 := h1351c.2.1
                  have p1351_2 := h1351c.2.2.1
                  have p1351_3 := h1351c.2.2.2
                  linarith only [hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1351_1, u3ehi0]
                · have p1351_0 := h1351c.1
                  have p1351_1 := h1351c.2.1
                  have p1351_2 := h1351c.2.2.1
                  have p1351_3 := h1351c.2.2.2
                  linarith only [h0, h1349, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1351_1, u4ehi4]
                · have p1351_0 := h1351c.1
                  have p1351_1 := h1351c.2.1
                  have p1351_2 := h1351c.2.2.1
                  have p1351_3 := h1351c.2.2.2
                  linarith only [h0, h1346, h1350, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1351_1, u3ehi4]
                · have p1351_0 := h1351c.1
                  have p1351_1 := h1351c.2.1
                  have p1351_2 := h1351c.2.2.1
                  have p1351_3 := h1351c.2.2.2
                  linarith only [h1343, h1349, hc03, hlam, hphi, ht0b, ht45, ht5b, p1351_1, u4ehi4]
                · have p1351_0 := h1351c.1
                  have p1351_1 := h1351c.2.1
                  have p1351_2 := h1351c.2.2.1
                  have p1351_3 := h1351c.2.2.2
                  linarith only [h1345, hlam, p1351_1]
                · have p1351_0 := h1351c.1
                  have p1351_1 := h1351c.2.1
                  have p1351_2 := h1351c.2.2.1
                  have p1351_3 := h1351c.2.2.2
                  linarith only [hlam, p1351_0]
                · have p1351_0 := h1351c.1
                  have p1351_1 := h1351c.2.1
                  have p1351_2 := h1351c.2.2.1
                  have p1351_3 := h1351c.2.2.2
                  linarith only [h0, h1345, h1349, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1351_1, u4ehi4]
                · have p1351_0 := h1351c.1
                  have p1351_1 := h1351c.2.1
                  have p1351_2 := h1351c.2.2.1
                  have p1351_3 := h1351c.2.2.2
                  linarith only [h0, h1345, h1346, h1350, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1351_1, u3ehi4]
                · have p1351_0 := h1351c.1
                  have p1351_1 := h1351c.2.1
                  have p1351_2 := h1351c.2.2.1
                  have p1351_3 := h1351c.2.2.2
                  linarith only [h1343, hlam, p1351_0]
                · have p1351_0 := h1351c.1
                  have p1351_1 := h1351c.2.1
                  have p1351_2 := h1351c.2.2.1
                  have p1351_3 := h1351c.2.2.2
                  linarith only [h1343, h1345, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1351_1, u3ehi0]
                · have p1351_0 := h1351c.1
                  have p1351_1 := h1351c.2.1
                  have p1351_2 := h1351c.2.2.1
                  have p1351_3 := h1351c.2.2.2
                  linarith only [h1347, hlam, p1351_0]
                · have p1351_0 := h1351c.1
                  have p1351_1 := h1351c.2.1
                  have p1351_2 := h1351c.2.2.1
                  have p1351_3 := h1351c.2.2.2
                  linarith only [hlam, p1351_0]
                · have p1351_0 := h1351c.1
                  have p1351_1 := h1351c.2.1
                  have p1351_2 := h1351c.2.2.1
                  have p1351_3 := h1351c.2.2.2
                  linarith only [h0, h1343, h1346, h1350, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1351_1, u3ehi4]
                · have p1351_0 := h1351c.1
                  have p1351_1 := h1351c.2.1
                  have p1351_2 := h1351c.2.2.1
                  have p1351_3 := h1351c.2.2.2
                  linarith only [h1344, hlam, p1351_0]
                · have p1351_0 := h1351c.1
                  have p1351_1 := h1351c.2.1
                  have p1351_2 := h1351c.2.2.1
                  have p1351_3 := h1351c.2.2.2
                  linarith only [h1346, hlam, p1351_1]
                · have p1351_0 := h1351c.1
                  have p1351_1 := h1351c.2.1
                  have p1351_2 := h1351c.2.2.1
                  have p1351_3 := h1351c.2.2.2
                  linarith only [h1348, hlam, p1351_0]
                · have p1351_0 := h1351c.1
                  have p1351_1 := h1351c.2.1
                  have p1351_2 := h1351c.2.2.1
                  have p1351_3 := h1351c.2.2.2
                  linarith only [h1349, hlam, p1351_1]
                · have p1351_0 := h1351c.1
                  have p1351_1 := h1351c.2.1
                  have p1351_2 := h1351c.2.2.1
                  have p1351_3 := h1351c.2.2.2
                  linarith only [hlam, p1351_0]
              · rcases h0bigk with h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c | h1377c
                · have p1377_0 := h1377c.1
                  have p1377_1 := h1377c.2.1
                  have p1377_2 := h1377c.2.2.1
                  have p1377_3 := h1377c.2.2.2
                  linarith only [hlam, p1377_0]
                · have p1377_0 := h1377c.1
                  have p1377_1 := h1377c.2.1
                  have p1377_2 := h1377c.2.2.1
                  have p1377_3 := h1377c.2.2.2
                  linarith only [h0, hlam, p1377_1]
                · have p1377_0 := h1377c.1
                  have p1377_1 := h1377c.2.1
                  have p1377_2 := h1377c.2.2.1
                  have p1377_3 := h1377c.2.2.2
                  linarith only [h1082, hlam, p1377_0]
                · have p1377_0 := h1377c.1
                  have p1377_1 := h1377c.2.1
                  have p1377_2 := h1377c.2.2.1
                  have p1377_3 := h1377c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1377_1, u4ehi0]
                · have p1377_0 := h1377c.1
                  have p1377_1 := h1377c.2.1
                  have p1377_2 := h1377c.2.2.1
                  have p1377_3 := h1377c.2.2.2
                  linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1377_1]
                · have p1377_0 := h1377c.1
                  have p1377_1 := h1377c.2.1
                  have p1377_2 := h1377c.2.2.1
                  have p1377_3 := h1377c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p1377_1]
                · have p1377_0 := h1377c.1
                  have p1377_1 := h1377c.2.1
                  have p1377_2 := h1377c.2.2.1
                  have p1377_3 := h1377c.2.2.2
                  linarith only [hlam, p1377_0]
                · have p1377_0 := h1377c.1
                  have p1377_1 := h1377c.2.1
                  have p1377_2 := h1377c.2.2.1
                  have p1377_3 := h1377c.2.2.2
                  linarith only [h0, h1348, h1350, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1377_1, u3ehi2]
                · have p1377_0 := h1377c.1
                  have p1377_1 := h1377c.2.1
                  have p1377_2 := h1377c.2.2.1
                  have p1377_3 := h1377c.2.2.2
                  linarith only [h0, h1348, h1349, h1350, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1377_1, u3ehi2]
                · have p1377_0 := h1377c.1
                  have p1377_1 := h1377c.2.1
                  have p1377_2 := h1377c.2.2.1
                  have p1377_3 := h1377c.2.2.2
                  linarith only [h0, h1348, h1350, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1377_1, u3ehi2]
                · have p1377_0 := h1377c.1
                  have p1377_1 := h1377c.2.1
                  have p1377_2 := h1377c.2.2.1
                  have p1377_3 := h1377c.2.2.2
                  linarith only [h1343, h1348, h1349, h1350, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1377_1, u3ehi2]
                · have p1377_0 := h1377c.1
                  have p1377_1 := h1377c.2.1
                  have p1377_2 := h1377c.2.2.1
                  have p1377_3 := h1377c.2.2.2
                  linarith only [h1345, hlam, p1377_1]
                · have p1377_0 := h1377c.1
                  have p1377_1 := h1377c.2.1
                  have p1377_2 := h1377c.2.2.1
                  have p1377_3 := h1377c.2.2.2
                  linarith only [hlam, p1377_0]
                · have p1377_0 := h1377c.1
                  have p1377_1 := h1377c.2.1
                  have p1377_2 := h1377c.2.2.1
                  have p1377_3 := h1377c.2.2.2
                  linarith only [h0, h1345, h1348, h1349, h1350, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1377_1, u3ehi2]
                · have p1377_0 := h1377c.1
                  have p1377_1 := h1377c.2.1
                  have p1377_2 := h1377c.2.2.1
                  have p1377_3 := h1377c.2.2.2
                  linarith only [h0, h1345, h1348, h1350, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1377_1, u3ehi2]
                · have p1377_0 := h1377c.1
                  have p1377_1 := h1377c.2.1
                  have p1377_2 := h1377c.2.2.1
                  have p1377_3 := h1377c.2.2.2
                  linarith only [h1343, hlam, p1377_0]
                · have p1377_0 := h1377c.1
                  have p1377_1 := h1377c.2.1
                  have p1377_2 := h1377c.2.2.1
                  have p1377_3 := h1377c.2.2.2
                  linarith only [h1343, h1345, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1377_1, u3ehi0]
                · have p1377_0 := h1377c.1
                  have p1377_1 := h1377c.2.1
                  have p1377_2 := h1377c.2.2.1
                  have p1377_3 := h1377c.2.2.2
                  linarith only [h1347, hlam, p1377_0]
                · have p1377_0 := h1377c.1
                  have p1377_1 := h1377c.2.1
                  have p1377_2 := h1377c.2.2.1
                  have p1377_3 := h1377c.2.2.2
                  linarith only [hlam, p1377_0]
                · have p1377_0 := h1377c.1
                  have p1377_1 := h1377c.2.1
                  have p1377_2 := h1377c.2.2.1
                  have p1377_3 := h1377c.2.2.2
                  linarith only [h0, h1343, h1348, h1350, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1377_1, u3ehi2]
                · have p1377_0 := h1377c.1
                  have p1377_1 := h1377c.2.1
                  have p1377_2 := h1377c.2.2.1
                  have p1377_3 := h1377c.2.2.2
                  linarith only [h1344, hlam, p1377_0]
                · have p1377_0 := h1377c.1
                  have p1377_1 := h1377c.2.1
                  have p1377_2 := h1377c.2.2.1
                  have p1377_3 := h1377c.2.2.2
                  linarith only [h1346, hlam, p1377_1]
                · have p1377_0 := h1377c.1
                  have p1377_1 := h1377c.2.1
                  have p1377_2 := h1377c.2.2.1
                  have p1377_3 := h1377c.2.2.2
                  linarith only [h1348, hlam, p1377_0]
                · have p1377_0 := h1377c.1
                  have p1377_1 := h1377c.2.1
                  have p1377_2 := h1377c.2.2.1
                  have p1377_3 := h1377c.2.2.2
                  linarith only [h1349, hlam, p1377_1]
                · have p1377_0 := h1377c.1
                  have p1377_1 := h1377c.2.1
                  have p1377_2 := h1377c.2.2.1
                  have p1377_3 := h1377c.2.2.2
                  linarith only [hlam, p1377_0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1403 | h1403
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
                  linarith only [h0, hlam, p1404_1]
                · have p1404_0 := h1404c.1
                  have p1404_1 := h1404c.2.1
                  have p1404_2 := h1404c.2.2.1
                  have p1404_3 := h1404c.2.2.2
                  linarith only [h1082, hlam, p1404_0]
                · have p1404_0 := h1404c.1
                  have p1404_1 := h1404c.2.1
                  have p1404_2 := h1404c.2.2.1
                  have p1404_3 := h1404c.2.2.2
                  linarith only [h0, h1347, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1404_1, u3ehi3]
                · have p1404_0 := h1404c.1
                  have p1404_1 := h1404c.2.1
                  have p1404_2 := h1404c.2.2.1
                  have p1404_3 := h1404c.2.2.2
                  linarith only [h0, h1347, h1349, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1404_1, u3ehi3]
                · have p1404_0 := h1404c.1
                  have p1404_1 := h1404c.2.1
                  have p1404_2 := h1404c.2.2.1
                  have p1404_3 := h1404c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p1404_1]
                · have p1404_0 := h1404c.1
                  have p1404_1 := h1404c.2.1
                  have p1404_2 := h1404c.2.2.1
                  have p1404_3 := h1404c.2.2.2
                  linarith only [hlam, p1404_0]
                · have p1404_0 := h1404c.1
                  have p1404_1 := h1404c.2.1
                  have p1404_2 := h1404c.2.2.1
                  have p1404_3 := h1404c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1404_1, u3ehi0]
                · have p1404_0 := h1404c.1
                  have p1404_1 := h1404c.2.1
                  have p1404_2 := h1404c.2.2.1
                  have p1404_3 := h1404c.2.2.2
                  linarith only [h0, h1347, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1404_1, u3ehi3]
                · have p1404_0 := h1404c.1
                  have p1404_1 := h1404c.2.1
                  have p1404_2 := h1404c.2.2.1
                  have p1404_3 := h1404c.2.2.2
                  linarith only [h0, h1347, h1349, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1404_1, u3ehi3]
                · have p1404_0 := h1404c.1
                  have p1404_1 := h1404c.2.1
                  have p1404_2 := h1404c.2.2.1
                  have p1404_3 := h1404c.2.2.2
                  linarith only [h1343, hc03, hlam, hphi, ht0b, ht45, ht5b, p1404_1, u4ehi1]
                · have p1404_0 := h1404c.1
                  have p1404_1 := h1404c.2.1
                  have p1404_2 := h1404c.2.2.1
                  have p1404_3 := h1404c.2.2.2
                  linarith only [h1345, hlam, p1404_1]
                · have p1404_0 := h1404c.1
                  have p1404_1 := h1404c.2.1
                  have p1404_2 := h1404c.2.2.1
                  have p1404_3 := h1404c.2.2.2
                  linarith only [hlam, p1404_0]
                · have p1404_0 := h1404c.1
                  have p1404_1 := h1404c.2.1
                  have p1404_2 := h1404c.2.2.1
                  have p1404_3 := h1404c.2.2.2
                  linarith only [h0, h1345, h1347, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1404_1, u3ehi3]
                · have p1404_0 := h1404c.1
                  have p1404_1 := h1404c.2.1
                  have p1404_2 := h1404c.2.2.1
                  have p1404_3 := h1404c.2.2.2
                  linarith only [h0, h1345, h1347, h1349, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1404_1, u3ehi3]
                · have p1404_0 := h1404c.1
                  have p1404_1 := h1404c.2.1
                  have p1404_2 := h1404c.2.2.1
                  have p1404_3 := h1404c.2.2.2
                  linarith only [h1343, hlam, p1404_0]
                · have p1404_0 := h1404c.1
                  have p1404_1 := h1404c.2.1
                  have p1404_2 := h1404c.2.2.1
                  have p1404_3 := h1404c.2.2.2
                  linarith only [h1345, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1404_1, u3ehi0]
                · have p1404_0 := h1404c.1
                  have p1404_1 := h1404c.2.1
                  have p1404_2 := h1404c.2.2.1
                  have p1404_3 := h1404c.2.2.2
                  linarith only [h1347, hlam, p1404_0]
                · have p1404_0 := h1404c.1
                  have p1404_1 := h1404c.2.1
                  have p1404_2 := h1404c.2.2.1
                  have p1404_3 := h1404c.2.2.2
                  linarith only [hlam, p1404_0]
                · have p1404_0 := h1404c.1
                  have p1404_1 := h1404c.2.1
                  have p1404_2 := h1404c.2.2.1
                  have p1404_3 := h1404c.2.2.2
                  linarith only [h1349, hlam, p1404_0]
                · have p1404_0 := h1404c.1
                  have p1404_1 := h1404c.2.1
                  have p1404_2 := h1404c.2.2.1
                  have p1404_3 := h1404c.2.2.2
                  linarith only [h1344, hlam, p1404_0]
                · have p1404_0 := h1404c.1
                  have p1404_1 := h1404c.2.1
                  have p1404_2 := h1404c.2.2.1
                  have p1404_3 := h1404c.2.2.2
                  linarith only [h1346, hlam, p1404_1]
                · have p1404_0 := h1404c.1
                  have p1404_1 := h1404c.2.1
                  have p1404_2 := h1404c.2.2.1
                  have p1404_3 := h1404c.2.2.2
                  linarith only [h1348, hlam, p1404_0]
                · have p1404_0 := h1404c.1
                  have p1404_1 := h1404c.2.1
                  have p1404_2 := h1404c.2.2.1
                  have p1404_3 := h1404c.2.2.2
                  linarith only [h1345, h1348, hc02, hlam, hphi, ht0b, ht45, ht5b, p1404_1, u4ehi0]
                · have p1404_0 := h1404c.1
                  have p1404_1 := h1404c.2.1
                  have p1404_2 := h1404c.2.2.1
                  have p1404_3 := h1404c.2.2.2
                  linarith only [hlam, p1404_0]
              · rcases h0bigk with h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c | h1430c
                · have p1430_0 := h1430c.1
                  have p1430_1 := h1430c.2.1
                  have p1430_2 := h1430c.2.2.1
                  have p1430_3 := h1430c.2.2.2
                  linarith only [hlam, p1430_0]
                · have p1430_0 := h1430c.1
                  have p1430_1 := h1430c.2.1
                  have p1430_2 := h1430c.2.2.1
                  have p1430_3 := h1430c.2.2.2
                  linarith only [h0, hlam, p1430_1]
                · have p1430_0 := h1430c.1
                  have p1430_1 := h1430c.2.1
                  have p1430_2 := h1430c.2.2.1
                  have p1430_3 := h1430c.2.2.2
                  linarith only [h1082, hlam, p1430_0]
                · have p1430_0 := h1430c.1
                  have p1430_1 := h1430c.2.1
                  have p1430_2 := h1430c.2.2.1
                  have p1430_3 := h1430c.2.2.2
                  linarith only [h0, h1347, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1430_1, u3ehi3]
                · have p1430_0 := h1430c.1
                  have p1430_1 := h1430c.2.1
                  have p1430_2 := h1430c.2.2.1
                  have p1430_3 := h1430c.2.2.2
                  linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1430_1]
                · have p1430_0 := h1430c.1
                  have p1430_1 := h1430c.2.1
                  have p1430_2 := h1430c.2.2.1
                  have p1430_3 := h1430c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p1430_1]
                · have p1430_0 := h1430c.1
                  have p1430_1 := h1430c.2.1
                  have p1430_2 := h1430c.2.2.1
                  have p1430_3 := h1430c.2.2.2
                  linarith only [hlam, p1430_0]
                · have p1430_0 := h1430c.1
                  have p1430_1 := h1430c.2.1
                  have p1430_2 := h1430c.2.2.1
                  have p1430_3 := h1430c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1430_1, u3ehi0]
                · have p1430_0 := h1430c.1
                  have p1430_1 := h1430c.2.1
                  have p1430_2 := h1430c.2.2.1
                  have p1430_3 := h1430c.2.2.2
                  linarith only [h0, h1347, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1430_1, u3ehi3]
                · have p1430_0 := h1430c.1
                  have p1430_1 := h1430c.2.1
                  have p1430_2 := h1430c.2.2.1
                  have p1430_3 := h1430c.2.2.2
                  linarith only [h0, h1348, h1403, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1430_1, u3ehi2]
                · have p1430_0 := h1430c.1
                  have p1430_1 := h1430c.2.1
                  have p1430_2 := h1430c.2.2.1
                  have p1430_3 := h1430c.2.2.2
                  linarith only [h1344, h1348, h1403, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1430_1, u3ehi2]
                · have p1430_0 := h1430c.1
                  have p1430_1 := h1430c.2.1
                  have p1430_2 := h1430c.2.2.1
                  have p1430_3 := h1430c.2.2.2
                  linarith only [h1345, hlam, p1430_1]
                · have p1430_0 := h1430c.1
                  have p1430_1 := h1430c.2.1
                  have p1430_2 := h1430c.2.2.1
                  have p1430_3 := h1430c.2.2.2
                  linarith only [hlam, p1430_0]
                · have p1430_0 := h1430c.1
                  have p1430_1 := h1430c.2.1
                  have p1430_2 := h1430c.2.2.1
                  have p1430_3 := h1430c.2.2.2
                  linarith only [h0, h1345, h1347, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1430_1, u3ehi3]
                · have p1430_0 := h1430c.1
                  have p1430_1 := h1430c.2.1
                  have p1430_2 := h1430c.2.2.1
                  have p1430_3 := h1430c.2.2.2
                  linarith only [h0, h1345, h1348, h1403, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1430_1, u3ehi2]
                · have p1430_0 := h1430c.1
                  have p1430_1 := h1430c.2.1
                  have p1430_2 := h1430c.2.2.1
                  have p1430_3 := h1430c.2.2.2
                  linarith only [h1343, hlam, p1430_0]
                · have p1430_0 := h1430c.1
                  have p1430_1 := h1430c.2.1
                  have p1430_2 := h1430c.2.2.1
                  have p1430_3 := h1430c.2.2.2
                  linarith only [h1345, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1430_1, u3ehi0]
                · have p1430_0 := h1430c.1
                  have p1430_1 := h1430c.2.1
                  have p1430_2 := h1430c.2.2.1
                  have p1430_3 := h1430c.2.2.2
                  linarith only [h1347, hlam, p1430_0]
                · have p1430_0 := h1430c.1
                  have p1430_1 := h1430c.2.1
                  have p1430_2 := h1430c.2.2.1
                  have p1430_3 := h1430c.2.2.2
                  linarith only [hlam, p1430_0]
                · have p1430_0 := h1430c.1
                  have p1430_1 := h1430c.2.1
                  have p1430_2 := h1430c.2.2.1
                  have p1430_3 := h1430c.2.2.2
                  linarith only [h1349, hlam, p1430_0]
                · have p1430_0 := h1430c.1
                  have p1430_1 := h1430c.2.1
                  have p1430_2 := h1430c.2.2.1
                  have p1430_3 := h1430c.2.2.2
                  linarith only [h1344, hlam, p1430_0]
                · have p1430_0 := h1430c.1
                  have p1430_1 := h1430c.2.1
                  have p1430_2 := h1430c.2.2.1
                  have p1430_3 := h1430c.2.2.2
                  linarith only [h1346, hlam, p1430_1]
                · have p1430_0 := h1430c.1
                  have p1430_1 := h1430c.2.1
                  have p1430_2 := h1430c.2.2.1
                  have p1430_3 := h1430c.2.2.2
                  linarith only [h1348, hlam, p1430_0]
                · have p1430_0 := h1430c.1
                  have p1430_1 := h1430c.2.1
                  have p1430_2 := h1430c.2.2.1
                  have p1430_3 := h1430c.2.2.2
                  linarith only [h1344, hc01, hlam, hphi, ht0b, ht45, ht5b, p1430_1, u4ehi0]
                · have p1430_0 := h1430c.1
                  have p1430_1 := h1430c.2.1
                  have p1430_2 := h1430c.2.2.1
                  have p1430_3 := h1430c.2.2.2
                  linarith only [hlam, p1430_0]
          · linarith only [h1347, h1348, hc35, hlam, hphi, u3ehi3]
        · linarith only [h1082, h1343, h1347, hlam]
      · linarith only [h0, h1344, h1346, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1459 | h1459
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1460 | h1460
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1461 | h1461
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1462 | h1462
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1463 | h1463
              · rcases h0bigk with h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c
                · have p1464_0 := h1464c.1
                  have p1464_1 := h1464c.2.1
                  have p1464_2 := h1464c.2.2.1
                  have p1464_3 := h1464c.2.2.2
                  linarith only [hlam, p1464_0]
                · have p1464_0 := h1464c.1
                  have p1464_1 := h1464c.2.1
                  have p1464_2 := h1464c.2.2.1
                  have p1464_3 := h1464c.2.2.2
                  linarith only [h0, hlam, p1464_1]
                · have p1464_0 := h1464c.1
                  have p1464_1 := h1464c.2.1
                  have p1464_2 := h1464c.2.2.1
                  have p1464_3 := h1464c.2.2.2
                  linarith only [h1082, hlam, p1464_0]
                · have p1464_0 := h1464c.1
                  have p1464_1 := h1464c.2.1
                  have p1464_2 := h1464c.2.2.1
                  have p1464_3 := h1464c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p1464_1, u4ehi0]
                · have p1464_0 := h1464c.1
                  have p1464_1 := h1464c.2.1
                  have p1464_2 := h1464c.2.2.1
                  have p1464_3 := h1464c.2.2.2
                  linarith only [h0, h1345, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1464_1]
                · have p1464_0 := h1464c.1
                  have p1464_1 := h1464c.2.1
                  have p1464_2 := h1464c.2.2.1
                  have p1464_3 := h1464c.2.2.2
                  linarith only [h1345, hc01, hc23, hlam, hphi, ht12, p1464_1]
                · have p1464_0 := h1464c.1
                  have p1464_1 := h1464c.2.1
                  have p1464_2 := h1464c.2.2.1
                  have p1464_3 := h1464c.2.2.2
                  linarith only [hlam, p1464_0]
                · have p1464_0 := h1464c.1
                  have p1464_1 := h1464c.2.1
                  have p1464_2 := h1464c.2.2.1
                  have p1464_3 := h1464c.2.2.2
                  linarith only [h1345, hlam, p1464_0]
                · have p1464_0 := h1464c.1
                  have p1464_1 := h1464c.2.1
                  have p1464_2 := h1464c.2.2.1
                  have p1464_3 := h1464c.2.2.2
                  linarith only [h1345, h1462, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1464_1, u4ehi4]
                · have p1464_0 := h1464c.1
                  have p1464_1 := h1464c.2.1
                  have p1464_2 := h1464c.2.2.1
                  have p1464_3 := h1464c.2.2.2
                  linarith only [h1345, h1459, h1463, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1464_1, u3ehi4]
                · have p1464_0 := h1464c.1
                  have p1464_1 := h1464c.2.1
                  have p1464_2 := h1464c.2.2.1
                  have p1464_3 := h1464c.2.2.2
                  linarith only [h1343, h1345, h1462, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1464_1, u4ehi4]
                · have p1464_0 := h1464c.1
                  have p1464_1 := h1464c.2.1
                  have p1464_2 := h1464c.2.2.1
                  have p1464_3 := h1464c.2.2.2
                  linarith only [h1345, hc02, hc23, hlam, hphi, p1464_1]
                · have p1464_0 := h1464c.1
                  have p1464_1 := h1464c.2.1
                  have p1464_2 := h1464c.2.2.1
                  have p1464_3 := h1464c.2.2.2
                  linarith only [hlam, p1464_0]
                · have p1464_0 := h1464c.1
                  have p1464_1 := h1464c.2.1
                  have p1464_2 := h1464c.2.2.1
                  have p1464_3 := h1464c.2.2.2
                  linarith only [h1345, h1462, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1464_1, u4ehi4]
                · have p1464_0 := h1464c.1
                  have p1464_1 := h1464c.2.1
                  have p1464_2 := h1464c.2.2.1
                  have p1464_3 := h1464c.2.2.2
                  linarith only [h1345, h1459, h1463, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1464_1, u3ehi4]
                · have p1464_0 := h1464c.1
                  have p1464_1 := h1464c.2.1
                  have p1464_2 := h1464c.2.2.1
                  have p1464_3 := h1464c.2.2.2
                  linarith only [h1343, hlam, p1464_0]
                · have p1464_0 := h1464c.1
                  have p1464_1 := h1464c.2.1
                  have p1464_2 := h1464c.2.2.1
                  have p1464_3 := h1464c.2.2.2
                  linarith only [h0, h1343, hlam, p1464_1]
                · have p1464_0 := h1464c.1
                  have p1464_1 := h1464c.2.1
                  have p1464_2 := h1464c.2.2.1
                  have p1464_3 := h1464c.2.2.2
                  linarith only [h1460, hlam, p1464_0]
                · have p1464_0 := h1464c.1
                  have p1464_1 := h1464c.2.1
                  have p1464_2 := h1464c.2.2.1
                  have p1464_3 := h1464c.2.2.2
                  linarith only [hlam, p1464_0]
                · have p1464_0 := h1464c.1
                  have p1464_1 := h1464c.2.1
                  have p1464_2 := h1464c.2.2.1
                  have p1464_3 := h1464c.2.2.2
                  linarith only [h1343, h1459, h1463, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1464_1, u3ehi4]
                · have p1464_0 := h1464c.1
                  have p1464_1 := h1464c.2.1
                  have p1464_2 := h1464c.2.2.1
                  have p1464_3 := h1464c.2.2.2
                  linarith only [h1344, hlam, p1464_0]
                · have p1464_0 := h1464c.1
                  have p1464_1 := h1464c.2.1
                  have p1464_2 := h1464c.2.2.1
                  have p1464_3 := h1464c.2.2.2
                  linarith only [h1459, hlam, p1464_1]
                · have p1464_0 := h1464c.1
                  have p1464_1 := h1464c.2.1
                  have p1464_2 := h1464c.2.2.1
                  have p1464_3 := h1464c.2.2.2
                  linarith only [h1461, hlam, p1464_0]
                · have p1464_0 := h1464c.1
                  have p1464_1 := h1464c.2.1
                  have p1464_2 := h1464c.2.2.1
                  have p1464_3 := h1464c.2.2.2
                  linarith only [h1462, hlam, p1464_1]
                · have p1464_0 := h1464c.1
                  have p1464_1 := h1464c.2.1
                  have p1464_2 := h1464c.2.2.1
                  have p1464_3 := h1464c.2.2.2
                  linarith only [hlam, p1464_0]
              · linarith only [h0, h1343, h1345, h1460, h1463, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1491 | h1491
              · rcases h0bigk with h1492c | h1492c | h1492c | h1492c | h1492c | h1492c | h1492c | h1492c | h1492c | h1492c | h1492c | h1492c | h1492c | h1492c | h1492c | h1492c | h1492c | h1492c | h1492c | h1492c | h1492c | h1492c | h1492c | h1492c | h1492c
                · have p1492_0 := h1492c.1
                  have p1492_1 := h1492c.2.1
                  have p1492_2 := h1492c.2.2.1
                  have p1492_3 := h1492c.2.2.2
                  linarith only [hlam, p1492_0]
                · have p1492_0 := h1492c.1
                  have p1492_1 := h1492c.2.1
                  have p1492_2 := h1492c.2.2.1
                  have p1492_3 := h1492c.2.2.2
                  linarith only [h0, hlam, p1492_1]
                · have p1492_0 := h1492c.1
                  have p1492_1 := h1492c.2.1
                  have p1492_2 := h1492c.2.2.1
                  have p1492_3 := h1492c.2.2.2
                  linarith only [h1082, hlam, p1492_0]
                · have p1492_0 := h1492c.1
                  have p1492_1 := h1492c.2.1
                  have p1492_2 := h1492c.2.2.1
                  have p1492_3 := h1492c.2.2.2
                  linarith only [h0, h1345, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1492_1, u4ehi0]
                · have p1492_0 := h1492c.1
                  have p1492_1 := h1492c.2.1
                  have p1492_2 := h1492c.2.2.1
                  have p1492_3 := h1492c.2.2.2
                  linarith only [h0, h1345, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1492_1]
                · have p1492_0 := h1492c.1
                  have p1492_1 := h1492c.2.1
                  have p1492_2 := h1492c.2.2.1
                  have p1492_3 := h1492c.2.2.2
                  linarith only [h1345, hc01, hc23, hlam, hphi, ht12, p1492_1]
                · have p1492_0 := h1492c.1
                  have p1492_1 := h1492c.2.1
                  have p1492_2 := h1492c.2.2.1
                  have p1492_3 := h1492c.2.2.2
                  linarith only [hlam, p1492_0]
                · have p1492_0 := h1492c.1
                  have p1492_1 := h1492c.2.1
                  have p1492_2 := h1492c.2.2.1
                  have p1492_3 := h1492c.2.2.2
                  linarith only [h1345, hlam, p1492_0]
                · have p1492_0 := h1492c.1
                  have p1492_1 := h1492c.2.1
                  have p1492_2 := h1492c.2.2.1
                  have p1492_3 := h1492c.2.2.2
                  linarith only [h1345, h1460, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1492_1, u3ehi3]
                · have p1492_0 := h1492c.1
                  have p1492_1 := h1492c.2.1
                  have p1492_2 := h1492c.2.2.1
                  have p1492_3 := h1492c.2.2.2
                  linarith only [h1345, h1459, h1491, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1492_1, u3ehi4]
                · have p1492_0 := h1492c.1
                  have p1492_1 := h1492c.2.1
                  have p1492_2 := h1492c.2.2.1
                  have p1492_3 := h1492c.2.2.2
                  linarith only [h1343, h1345, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1492_1, u4ehi1]
                · have p1492_0 := h1492c.1
                  have p1492_1 := h1492c.2.1
                  have p1492_2 := h1492c.2.2.1
                  have p1492_3 := h1492c.2.2.2
                  linarith only [h1345, hc02, hc23, hlam, hphi, p1492_1]
                · have p1492_0 := h1492c.1
                  have p1492_1 := h1492c.2.1
                  have p1492_2 := h1492c.2.2.1
                  have p1492_3 := h1492c.2.2.2
                  linarith only [hlam, p1492_0]
                · have p1492_0 := h1492c.1
                  have p1492_1 := h1492c.2.1
                  have p1492_2 := h1492c.2.2.1
                  have p1492_3 := h1492c.2.2.2
                  linarith only [h1345, h1460, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1492_1, u3ehi3]
                · have p1492_0 := h1492c.1
                  have p1492_1 := h1492c.2.1
                  have p1492_2 := h1492c.2.2.1
                  have p1492_3 := h1492c.2.2.2
                  linarith only [h1345, h1459, h1491, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1492_1, u3ehi4]
                · have p1492_0 := h1492c.1
                  have p1492_1 := h1492c.2.1
                  have p1492_2 := h1492c.2.2.1
                  have p1492_3 := h1492c.2.2.2
                  linarith only [h1343, hlam, p1492_0]
                · have p1492_0 := h1492c.1
                  have p1492_1 := h1492c.2.1
                  have p1492_2 := h1492c.2.2.1
                  have p1492_3 := h1492c.2.2.2
                  linarith only [h1459, h1491, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1492_1, u3ehi4]
                · have p1492_0 := h1492c.1
                  have p1492_1 := h1492c.2.1
                  have p1492_2 := h1492c.2.2.1
                  have p1492_3 := h1492c.2.2.2
                  linarith only [h1460, hlam, p1492_0]
                · have p1492_0 := h1492c.1
                  have p1492_1 := h1492c.2.1
                  have p1492_2 := h1492c.2.2.1
                  have p1492_3 := h1492c.2.2.2
                  linarith only [hlam, p1492_0]
                · have p1492_0 := h1492c.1
                  have p1492_1 := h1492c.2.1
                  have p1492_2 := h1492c.2.2.1
                  have p1492_3 := h1492c.2.2.2
                  linarith only [h1462, hlam, p1492_0]
                · have p1492_0 := h1492c.1
                  have p1492_1 := h1492c.2.1
                  have p1492_2 := h1492c.2.2.1
                  have p1492_3 := h1492c.2.2.2
                  linarith only [h1344, hlam, p1492_0]
                · have p1492_0 := h1492c.1
                  have p1492_1 := h1492c.2.1
                  have p1492_2 := h1492c.2.2.1
                  have p1492_3 := h1492c.2.2.2
                  linarith only [h1459, hlam, p1492_1]
                · have p1492_0 := h1492c.1
                  have p1492_1 := h1492c.2.1
                  have p1492_2 := h1492c.2.2.1
                  have p1492_3 := h1492c.2.2.2
                  linarith only [h1461, hlam, p1492_0]
                · have p1492_0 := h1492c.1
                  have p1492_1 := h1492c.2.1
                  have p1492_2 := h1492c.2.2.1
                  have p1492_3 := h1492c.2.2.2
                  linarith only [hc05, hlam, hphi, ht0b, ht45, ht5b, p1492_1, u4ehi0]
                · have p1492_0 := h1492c.1
                  have p1492_1 := h1492c.2.1
                  have p1492_2 := h1492c.2.2.1
                  have p1492_3 := h1492c.2.2.2
                  linarith only [hlam, p1492_0]
              · linarith only [h0, h1343, h1345, h1491, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
          · linarith only [h1460, h1461, hc35, hlam, hphi, u3ehi3]
        · linarith only [h1082, h1343, h1460, hlam]
      · linarith only [h0, h1344, h1459, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1522 | h1522
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1523 | h1523
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1524 | h1524
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1525 | h1525
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1526 | h1526
            · linarith only [h1343, h1344, h1526, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1528 | h1528
              · rcases h0bigk with h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c
                · have p1529_0 := h1529c.1
                  have p1529_1 := h1529c.2.1
                  have p1529_2 := h1529c.2.2.1
                  have p1529_3 := h1529c.2.2.2
                  linarith only [hlam, p1529_0]
                · have p1529_0 := h1529c.1
                  have p1529_1 := h1529c.2.1
                  have p1529_2 := h1529c.2.2.1
                  have p1529_3 := h1529c.2.2.2
                  linarith only [h0, hlam, p1529_1]
                · have p1529_0 := h1529c.1
                  have p1529_1 := h1529c.2.1
                  have p1529_2 := h1529c.2.2.1
                  have p1529_3 := h1529c.2.2.2
                  linarith only [h1082, hlam, p1529_0]
                · have p1529_0 := h1529c.1
                  have p1529_1 := h1529c.2.1
                  have p1529_2 := h1529c.2.2.1
                  have p1529_3 := h1529c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p1529_1, u4ehi0]
                · have p1529_0 := h1529c.1
                  have p1529_1 := h1529c.2.1
                  have p1529_2 := h1529c.2.2.1
                  have p1529_3 := h1529c.2.2.2
                  linarith only [h1344, hlam, p1529_1]
                · have p1529_0 := h1529c.1
                  have p1529_1 := h1529c.2.1
                  have p1529_2 := h1529c.2.2.1
                  have p1529_3 := h1529c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p1529_1]
                · have p1529_0 := h1529c.1
                  have p1529_1 := h1529c.2.1
                  have p1529_2 := h1529c.2.2.1
                  have p1529_3 := h1529c.2.2.2
                  linarith only [hlam, p1529_0]
                · have p1529_0 := h1529c.1
                  have p1529_1 := h1529c.2.1
                  have p1529_2 := h1529c.2.2.1
                  have p1529_3 := h1529c.2.2.2
                  linarith only [hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1529_1, u3ehi0]
                · have p1529_0 := h1529c.1
                  have p1529_1 := h1529c.2.1
                  have p1529_2 := h1529c.2.2.1
                  have p1529_3 := h1529c.2.2.2
                  linarith only [h0, h1524, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1529_1, u3ehi3]
                · have p1529_0 := h1529c.1
                  have p1529_1 := h1529c.2.1
                  have p1529_2 := h1529c.2.2.1
                  have p1529_3 := h1529c.2.2.2
                  linarith only [h0, h1343, h1344, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1529_1, u4ehi1]
                · have p1529_0 := h1529c.1
                  have p1529_1 := h1529c.2.1
                  have p1529_2 := h1529c.2.2.1
                  have p1529_3 := h1529c.2.2.2
                  linarith only [h1343, hc03, hlam, hphi, ht0b, ht45, ht5b, p1529_1, u4ehi1]
                · have p1529_0 := h1529c.1
                  have p1529_1 := h1529c.2.1
                  have p1529_2 := h1529c.2.2.1
                  have p1529_3 := h1529c.2.2.2
                  linarith only [h1522, hlam, p1529_1]
                · have p1529_0 := h1529c.1
                  have p1529_1 := h1529c.2.1
                  have p1529_2 := h1529c.2.2.1
                  have p1529_3 := h1529c.2.2.2
                  linarith only [hlam, p1529_0]
                · have p1529_0 := h1529c.1
                  have p1529_1 := h1529c.2.1
                  have p1529_2 := h1529c.2.2.1
                  have p1529_3 := h1529c.2.2.2
                  linarith only [h0, h1522, h1524, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1529_1, u3ehi3]
                · have p1529_0 := h1529c.1
                  have p1529_1 := h1529c.2.1
                  have p1529_2 := h1529c.2.2.1
                  have p1529_3 := h1529c.2.2.2
                  linarith only [h0, h1343, h1344, h1522, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1529_1, u4ehi1]
                · have p1529_0 := h1529c.1
                  have p1529_1 := h1529c.2.1
                  have p1529_2 := h1529c.2.2.1
                  have p1529_3 := h1529c.2.2.2
                  linarith only [h1343, hlam, p1529_0]
                · have p1529_0 := h1529c.1
                  have p1529_1 := h1529c.2.1
                  have p1529_2 := h1529c.2.2.1
                  have p1529_3 := h1529c.2.2.2
                  linarith only [h1522, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1529_1, u3ehi0]
                · have p1529_0 := h1529c.1
                  have p1529_1 := h1529c.2.1
                  have p1529_2 := h1529c.2.2.1
                  have p1529_3 := h1529c.2.2.2
                  linarith only [h1524, hlam, p1529_0]
                · have p1529_0 := h1529c.1
                  have p1529_1 := h1529c.2.1
                  have p1529_2 := h1529c.2.2.1
                  have p1529_3 := h1529c.2.2.2
                  linarith only [hlam, p1529_0]
                · have p1529_0 := h1529c.1
                  have p1529_1 := h1529c.2.1
                  have p1529_2 := h1529c.2.2.1
                  have p1529_3 := h1529c.2.2.2
                  linarith only [h1526, hlam, p1529_0]
                · have p1529_0 := h1529c.1
                  have p1529_1 := h1529c.2.1
                  have p1529_2 := h1529c.2.2.1
                  have p1529_3 := h1529c.2.2.2
                  linarith only [h1343, hc05, hlam, hphi, ht0b, ht45, ht5b, p1529_1, u4ehi1]
                · have p1529_0 := h1529c.1
                  have p1529_1 := h1529c.2.1
                  have p1529_2 := h1529c.2.2.1
                  have p1529_3 := h1529c.2.2.2
                  linarith only [h1523, hlam, p1529_1]
                · have p1529_0 := h1529c.1
                  have p1529_1 := h1529c.2.1
                  have p1529_2 := h1529c.2.2.1
                  have p1529_3 := h1529c.2.2.2
                  linarith only [h1525, hlam, p1529_0]
                · have p1529_0 := h1529c.1
                  have p1529_1 := h1529c.2.1
                  have p1529_2 := h1529c.2.2.1
                  have p1529_3 := h1529c.2.2.2
                  linarith only [h1526, hc45, hlam, hphi, p1529_1, u4ehi0]
                · have p1529_0 := h1529c.1
                  have p1529_1 := h1529c.2.1
                  have p1529_2 := h1529c.2.2.1
                  have p1529_3 := h1529c.2.2.2
                  linarith only [hlam, p1529_0]
              · rcases h0bigk with h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c | h1555c
                · have p1555_0 := h1555c.1
                  have p1555_1 := h1555c.2.1
                  have p1555_2 := h1555c.2.2.1
                  have p1555_3 := h1555c.2.2.2
                  linarith only [hlam, p1555_0]
                · have p1555_0 := h1555c.1
                  have p1555_1 := h1555c.2.1
                  have p1555_2 := h1555c.2.2.1
                  have p1555_3 := h1555c.2.2.2
                  linarith only [h0, hlam, p1555_1]
                · have p1555_0 := h1555c.1
                  have p1555_1 := h1555c.2.1
                  have p1555_2 := h1555c.2.2.1
                  have p1555_3 := h1555c.2.2.2
                  linarith only [h1082, hlam, p1555_0]
                · have p1555_0 := h1555c.1
                  have p1555_1 := h1555c.2.1
                  have p1555_2 := h1555c.2.2.1
                  have p1555_3 := h1555c.2.2.2
                  linarith only [h1524, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1555_1, u3ehi3]
                · have p1555_0 := h1555c.1
                  have p1555_1 := h1555c.2.1
                  have p1555_2 := h1555c.2.2.1
                  have p1555_3 := h1555c.2.2.2
                  linarith only [h1344, hlam, p1555_1]
                · have p1555_0 := h1555c.1
                  have p1555_1 := h1555c.2.1
                  have p1555_2 := h1555c.2.2.1
                  have p1555_3 := h1555c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p1555_1]
                · have p1555_0 := h1555c.1
                  have p1555_1 := h1555c.2.1
                  have p1555_2 := h1555c.2.2.1
                  have p1555_3 := h1555c.2.2.2
                  linarith only [hlam, p1555_0]
                · have p1555_0 := h1555c.1
                  have p1555_1 := h1555c.2.1
                  have p1555_2 := h1555c.2.2.1
                  have p1555_3 := h1555c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1555_1, u3ehi0]
                · have p1555_0 := h1555c.1
                  have p1555_1 := h1555c.2.1
                  have p1555_2 := h1555c.2.2.1
                  have p1555_3 := h1555c.2.2.2
                  linarith only [h0, h1524, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1555_1, u3ehi3]
                · have p1555_0 := h1555c.1
                  have p1555_1 := h1555c.2.1
                  have p1555_2 := h1555c.2.2.1
                  have p1555_3 := h1555c.2.2.2
                  linarith only [h0, h1343, h1344, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1555_1, u4ehi1]
                · have p1555_0 := h1555c.1
                  have p1555_1 := h1555c.2.1
                  have p1555_2 := h1555c.2.2.1
                  have p1555_3 := h1555c.2.2.2
                  linarith only [h1343, hc03, hlam, hphi, ht0b, ht45, ht5b, p1555_1, u4ehi1]
                · have p1555_0 := h1555c.1
                  have p1555_1 := h1555c.2.1
                  have p1555_2 := h1555c.2.2.1
                  have p1555_3 := h1555c.2.2.2
                  linarith only [h1522, hlam, p1555_1]
                · have p1555_0 := h1555c.1
                  have p1555_1 := h1555c.2.1
                  have p1555_2 := h1555c.2.2.1
                  have p1555_3 := h1555c.2.2.2
                  linarith only [hlam, p1555_0]
                · have p1555_0 := h1555c.1
                  have p1555_1 := h1555c.2.1
                  have p1555_2 := h1555c.2.2.1
                  have p1555_3 := h1555c.2.2.2
                  linarith only [h0, h1522, h1524, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1555_1, u3ehi3]
                · have p1555_0 := h1555c.1
                  have p1555_1 := h1555c.2.1
                  have p1555_2 := h1555c.2.2.1
                  have p1555_3 := h1555c.2.2.2
                  linarith only [h0, h1343, h1344, h1522, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1555_1, u4ehi1]
                · have p1555_0 := h1555c.1
                  have p1555_1 := h1555c.2.1
                  have p1555_2 := h1555c.2.2.1
                  have p1555_3 := h1555c.2.2.2
                  linarith only [h1343, hlam, p1555_0]
                · have p1555_0 := h1555c.1
                  have p1555_1 := h1555c.2.1
                  have p1555_2 := h1555c.2.2.1
                  have p1555_3 := h1555c.2.2.2
                  linarith only [h1522, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1555_1, u3ehi0]
                · have p1555_0 := h1555c.1
                  have p1555_1 := h1555c.2.1
                  have p1555_2 := h1555c.2.2.1
                  have p1555_3 := h1555c.2.2.2
                  linarith only [h1524, hlam, p1555_0]
                · have p1555_0 := h1555c.1
                  have p1555_1 := h1555c.2.1
                  have p1555_2 := h1555c.2.2.1
                  have p1555_3 := h1555c.2.2.2
                  linarith only [hlam, p1555_0]
                · have p1555_0 := h1555c.1
                  have p1555_1 := h1555c.2.1
                  have p1555_2 := h1555c.2.2.1
                  have p1555_3 := h1555c.2.2.2
                  linarith only [h1526, hlam, p1555_0]
                · have p1555_0 := h1555c.1
                  have p1555_1 := h1555c.2.1
                  have p1555_2 := h1555c.2.2.1
                  have p1555_3 := h1555c.2.2.2
                  linarith only [h1343, hc05, hlam, hphi, ht0b, ht45, ht5b, p1555_1, u4ehi1]
                · have p1555_0 := h1555c.1
                  have p1555_1 := h1555c.2.1
                  have p1555_2 := h1555c.2.2.1
                  have p1555_3 := h1555c.2.2.2
                  linarith only [h1523, hlam, p1555_1]
                · have p1555_0 := h1555c.1
                  have p1555_1 := h1555c.2.1
                  have p1555_2 := h1555c.2.2.1
                  have p1555_3 := h1555c.2.2.2
                  linarith only [h1525, hlam, p1555_0]
                · have p1555_0 := h1555c.1
                  have p1555_1 := h1555c.2.1
                  have p1555_2 := h1555c.2.2.1
                  have p1555_3 := h1555c.2.2.2
                  linarith only [h1526, hc45, hlam, hphi, p1555_1, u4ehi0]
                · have p1555_0 := h1555c.1
                  have p1555_1 := h1555c.2.1
                  have p1555_2 := h1555c.2.2.1
                  have p1555_3 := h1555c.2.2.2
                  linarith only [hlam, p1555_0]
          · linarith only [h1524, h1525, hc35, hlam, hphi, u3ehi3]
        · linarith only [h1082, h1343, h1524, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1583 | h1583
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1584 | h1584
          · linarith only [h1522, h1523, h1584, hlam]
          · linarith only [h1583, h1584, hc35, hlam, hphi, u3ehi3]
        · linarith only [h1082, h1343, h1583, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1588 | h1588
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1589 | h1589
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1590 | h1590
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1591 | h1591
            · linarith only [h1343, h1344, h1591, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1593 | h1593
              · rcases h0bigk with h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [hlam, p1594_0]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h0, hlam, p1594_1]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h1082, hlam, p1594_0]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p1594_1, u4ehi0]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h1344, hlam, p1594_1]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h1522, hc01, hc23, hlam, hphi, ht12, p1594_1]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [hlam, p1594_0]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h1522, hlam, p1594_0]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h1522, h1589, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1594_1, u3ehi3]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h1522, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1594_1]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h1343, h1522, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1594_1, u4ehi1]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h1522, hc02, hc23, hlam, hphi, p1594_1]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [hlam, p1594_0]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h1522, h1589, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1594_1, u3ehi3]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h1343, h1344, h1522, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1594_1, u4ehi1]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h1343, hlam, p1594_0]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h1588, h1593, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1594_1, u3ehi4]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h1589, hlam, p1594_0]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [hlam, p1594_0]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h1591, hlam, p1594_0]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h1343, hc05, hlam, hphi, ht0b, ht45, ht5b, p1594_1, u4ehi1]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h1588, hlam, p1594_1]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h1590, hlam, p1594_0]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [h1522, h1588, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1594_1, u4ehi0]
                · have p1594_0 := h1594c.1
                  have p1594_1 := h1594c.2.1
                  have p1594_2 := h1594c.2.2.1
                  have p1594_3 := h1594c.2.2.2
                  linarith only [hlam, p1594_0]
              · linarith only [h0, h1343, h1522, h1593, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
          · linarith only [h1589, h1590, hc35, hlam, hphi, u3ehi3]
        · linarith only [h1082, h1343, h1589, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1623 | h1623
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1624 | h1624
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1625 | h1625
            · linarith only [h0, h1343, h1588, h1625, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1627 | h1627
              · rcases h0bigk with h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c
                · have p1628_0 := h1628c.1
                  have p1628_1 := h1628c.2.1
                  have p1628_2 := h1628c.2.2.1
                  have p1628_3 := h1628c.2.2.2
                  linarith only [hlam, p1628_0]
                · have p1628_0 := h1628c.1
                  have p1628_1 := h1628c.2.1
                  have p1628_2 := h1628c.2.2.1
                  have p1628_3 := h1628c.2.2.2
                  linarith only [h0, hlam, p1628_1]
                · have p1628_0 := h1628c.1
                  have p1628_1 := h1628c.2.1
                  have p1628_2 := h1628c.2.2.1
                  have p1628_3 := h1628c.2.2.2
                  linarith only [h1082, hlam, p1628_0]
                · have p1628_0 := h1628c.1
                  have p1628_1 := h1628c.2.1
                  have p1628_2 := h1628c.2.2.1
                  have p1628_3 := h1628c.2.2.2
                  linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p1628_1, u4ehi0]
                · have p1628_0 := h1628c.1
                  have p1628_1 := h1628c.2.1
                  have p1628_2 := h1628c.2.2.1
                  have p1628_3 := h1628c.2.2.2
                  linarith only [h1344, hlam, p1628_1]
                · have p1628_0 := h1628c.1
                  have p1628_1 := h1628c.2.1
                  have p1628_2 := h1628c.2.2.1
                  have p1628_3 := h1628c.2.2.2
                  linarith only [h1588, hc01, hc25, hlam, hphi, ht12, p1628_1]
                · have p1628_0 := h1628c.1
                  have p1628_1 := h1628c.2.1
                  have p1628_2 := h1628c.2.2.1
                  have p1628_3 := h1628c.2.2.2
                  linarith only [hlam, p1628_0]
                · have p1628_0 := h1628c.1
                  have p1628_1 := h1628c.2.1
                  have p1628_2 := h1628c.2.2.1
                  have p1628_3 := h1628c.2.2.2
                  linarith only [h1522, hlam, p1628_0]
                · have p1628_0 := h1628c.1
                  have p1628_1 := h1628c.2.1
                  have p1628_2 := h1628c.2.2.1
                  have p1628_3 := h1628c.2.2.2
                  linarith only [h1588, h1623, h1627, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1628_1, u3ehi3]
                · have p1628_0 := h1628c.1
                  have p1628_1 := h1628c.2.1
                  have p1628_2 := h1628c.2.2.1
                  have p1628_3 := h1628c.2.2.2
                  linarith only [h1588, hlam, p1628_0]
                · have p1628_0 := h1628c.1
                  have p1628_1 := h1628c.2.1
                  have p1628_2 := h1628c.2.2.1
                  have p1628_3 := h1628c.2.2.2
                  linarith only [h1343, hc03, hlam, hphi, ht0b, ht45, ht5b, p1628_1, u4ehi1]
                · have p1628_0 := h1628c.1
                  have p1628_1 := h1628c.2.1
                  have p1628_2 := h1628c.2.2.1
                  have p1628_3 := h1628c.2.2.2
                  linarith only [h1522, hc02, hc23, hlam, hphi, p1628_1]
                · have p1628_0 := h1628c.1
                  have p1628_1 := h1628c.2.1
                  have p1628_2 := h1628c.2.2.1
                  have p1628_3 := h1628c.2.2.2
                  linarith only [hlam, p1628_0]
                · have p1628_0 := h1628c.1
                  have p1628_1 := h1628c.2.1
                  have p1628_2 := h1628c.2.2.1
                  have p1628_3 := h1628c.2.2.2
                  linarith only [h1522, h1623, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1628_1, u3ehi3]
                · have p1628_0 := h1628c.1
                  have p1628_1 := h1628c.2.1
                  have p1628_2 := h1628c.2.2.1
                  have p1628_3 := h1628c.2.2.2
                  linarith only [h0, h1343, h1522, h1588, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1628_1, u4ehi1]
                · have p1628_0 := h1628c.1
                  have p1628_1 := h1628c.2.1
                  have p1628_2 := h1628c.2.2.1
                  have p1628_3 := h1628c.2.2.2
                  linarith only [h1343, hlam, p1628_0]
                · have p1628_0 := h1628c.1
                  have p1628_1 := h1628c.2.1
                  have p1628_2 := h1628c.2.2.1
                  have p1628_3 := h1628c.2.2.2
                  linarith only [h0, h1343, hc04, hlam, hphi, ht0b, ht45, ht5b, p1628_1, u4ehi1]
                · have p1628_0 := h1628c.1
                  have p1628_1 := h1628c.2.1
                  have p1628_2 := h1628c.2.2.1
                  have p1628_3 := h1628c.2.2.2
                  linarith only [h1623, hlam, p1628_0]
                · have p1628_0 := h1628c.1
                  have p1628_1 := h1628c.2.1
                  have p1628_2 := h1628c.2.2.1
                  have p1628_3 := h1628c.2.2.2
                  linarith only [hlam, p1628_0]
                · have p1628_0 := h1628c.1
                  have p1628_1 := h1628c.2.1
                  have p1628_2 := h1628c.2.2.1
                  have p1628_3 := h1628c.2.2.2
                  linarith only [h1625, hlam, p1628_0]
                · have p1628_0 := h1628c.1
                  have p1628_1 := h1628c.2.1
                  have p1628_2 := h1628c.2.2.1
                  have p1628_3 := h1628c.2.2.2
                  linarith only [h1343, hc05, hlam, hphi, ht0b, ht45, ht5b, p1628_1, u4ehi1]
                · have p1628_0 := h1628c.1
                  have p1628_1 := h1628c.2.1
                  have p1628_2 := h1628c.2.2.1
                  have p1628_3 := h1628c.2.2.2
                  linarith only [h0, h1343, h1625, hc45, hlam, hphi, p1628_1, u4ehi1]
                · have p1628_0 := h1628c.1
                  have p1628_1 := h1628c.2.1
                  have p1628_2 := h1628c.2.2.1
                  have p1628_3 := h1628c.2.2.2
                  linarith only [h1624, hlam, p1628_0]
                · have p1628_0 := h1628c.1
                  have p1628_1 := h1628c.2.1
                  have p1628_2 := h1628c.2.2.1
                  have p1628_3 := h1628c.2.2.2
                  linarith only [h1625, hc45, hlam, hphi, p1628_1, u4ehi0]
                · have p1628_0 := h1628c.1
                  have p1628_1 := h1628c.2.1
                  have p1628_2 := h1628c.2.2.1
                  have p1628_3 := h1628c.2.2.2
                  linarith only [hlam, p1628_0]
              · linarith only [h1522, h1624, h1627, hlam]
          · linarith only [h1623, h1624, hc35, hlam, hphi, u3ehi3]
        · linarith only [h0, h1343, h1522, h1623, hlam]

end R2N4
