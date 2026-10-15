import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4238000 in
set_option maxHeartbeats 4238000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_R_L_I_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1078 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h3ehi := hb3.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1079 | h1079
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1080 | h1080
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1081 | h1081
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1082 | h1082
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1083 | h1083
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1084 | h1084
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1085 | h1085
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1086 | h1086
                · rcases h0bigk with h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c | h1087c
                  · have p1087_0 := h1087c.1
                    have p1087_1 := h1087c.2.1
                    have p1087_2 := h1087c.2.2.1
                    have p1087_3 := h1087c.2.2.2
                    linarith only [hlam, p1087_0]
                  · have p1087_0 := h1087c.1
                    have p1087_1 := h1087c.2.1
                    have p1087_2 := h1087c.2.2.1
                    have p1087_3 := h1087c.2.2.2
                    linarith only [h0, hlam, p1087_1]
                  · have p1087_0 := h1087c.1
                    have p1087_1 := h1087c.2.1
                    have p1087_2 := h1087c.2.2.1
                    have p1087_3 := h1087c.2.2.2
                    linarith only [h0, h1080, h1086, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1087_1, u3ehi4]
                  · have p1087_0 := h1087c.1
                    have p1087_1 := h1087c.2.1
                    have p1087_2 := h1087c.2.2.1
                    have p1087_3 := h1087c.2.2.2
                    linarith only [h0, h1082, h1085, h1086, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1087_1, u3ehi4]
                  · have p1087_0 := h1087c.1
                    have p1087_1 := h1087c.2.1
                    have p1087_2 := h1087c.2.2.1
                    have p1087_3 := h1087c.2.2.2
                    linarith only [h0, h1082, h1086, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1087_1, u3ehi4]
                  · have p1087_0 := h1087c.1
                    have p1087_1 := h1087c.2.1
                    have p1087_2 := h1087c.2.2.1
                    have p1087_3 := h1087c.2.2.2
                    linarith only [h0, hc01, hc12, hlam, hphi, p1087_1]
                  · have p1087_0 := h1087c.1
                    have p1087_1 := h1087c.2.1
                    have p1087_2 := h1087c.2.2.1
                    have p1087_3 := h1087c.2.2.2
                    linarith only [hlam, p1087_0]
                  · have p1087_0 := h1087c.1
                    have p1087_1 := h1087c.2.1
                    have p1087_2 := h1087c.2.2.1
                    have p1087_3 := h1087c.2.2.2
                    linarith only [h0, h1080, h1086, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1087_1, u3ehi4]
                  · have p1087_0 := h1087c.1
                    have p1087_1 := h1087c.2.1
                    have p1087_2 := h1087c.2.2.1
                    have p1087_3 := h1087c.2.2.2
                    linarith only [h0, h1082, h1085, h1086, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1087_1, u3ehi4]
                  · have p1087_0 := h1087c.1
                    have p1087_1 := h1087c.2.1
                    have p1087_2 := h1087c.2.2.1
                    have p1087_3 := h1087c.2.2.2
                    linarith only [h0, h1082, h1086, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1087_1, u3ehi4]
                  · have p1087_0 := h1087c.1
                    have p1087_1 := h1087c.2.1
                    have p1087_2 := h1087c.2.2.1
                    have p1087_3 := h1087c.2.2.2
                    linarith only [h1078, hlam, p1087_1]
                  · have p1087_0 := h1087c.1
                    have p1087_1 := h1087c.2.1
                    have p1087_2 := h1087c.2.2.1
                    have p1087_3 := h1087c.2.2.2
                    linarith only [h1080, hlam, p1087_1]
                  · have p1087_0 := h1087c.1
                    have p1087_1 := h1087c.2.1
                    have p1087_2 := h1087c.2.2.1
                    have p1087_3 := h1087c.2.2.2
                    linarith only [hlam, p1087_0]
                  · have p1087_0 := h1087c.1
                    have p1087_1 := h1087c.2.1
                    have p1087_2 := h1087c.2.2.1
                    have p1087_3 := h1087c.2.2.2
                    linarith only [h1078, h1082, h1085, h1086, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1087_1, u3ehi4]
                  · have p1087_0 := h1087c.1
                    have p1087_1 := h1087c.2.1
                    have p1087_2 := h1087c.2.2.1
                    have p1087_3 := h1087c.2.2.2
                    linarith only [h0, h1078, h1082, h1086, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1087_1, u3ehi4]
                  · have p1087_0 := h1087c.1
                    have p1087_1 := h1087c.2.1
                    have p1087_2 := h1087c.2.2.1
                    have p1087_3 := h1087c.2.2.2
                    linarith only [h1078, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1087_1, u3ehi0]
                  · have p1087_0 := h1087c.1
                    have p1087_1 := h1087c.2.1
                    have p1087_2 := h1087c.2.2.1
                    have p1087_3 := h1087c.2.2.2
                    linarith only [h1081, hlam, p1087_0]
                  · have p1087_0 := h1087c.1
                    have p1087_1 := h1087c.2.1
                    have p1087_2 := h1087c.2.2.1
                    have p1087_3 := h1087c.2.2.2
                    linarith only [h1083, hlam, p1087_0]
                  · have p1087_0 := h1087c.1
                    have p1087_1 := h1087c.2.1
                    have p1087_2 := h1087c.2.2.1
                    have p1087_3 := h1087c.2.2.2
                    linarith only [hlam, p1087_0]
                  · have p1087_0 := h1087c.1
                    have p1087_1 := h1087c.2.1
                    have p1087_2 := h1087c.2.2.1
                    have p1087_3 := h1087c.2.2.2
                    linarith only [h1078, h1082, h1083, h1086, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1087_1, u3ehi4]
                  · have p1087_0 := h1087c.1
                    have p1087_1 := h1087c.2.1
                    have p1087_2 := h1087c.2.2.1
                    have p1087_3 := h1087c.2.2.2
                    linarith only [h1079, hlam, p1087_0]
                  · have p1087_0 := h1087c.1
                    have p1087_1 := h1087c.2.1
                    have p1087_2 := h1087c.2.2.1
                    have p1087_3 := h1087c.2.2.2
                    linarith only [h1082, hlam, p1087_1]
                  · have p1087_0 := h1087c.1
                    have p1087_1 := h1087c.2.1
                    have p1087_2 := h1087c.2.2.1
                    have p1087_3 := h1087c.2.2.2
                    linarith only [h1084, hlam, p1087_0]
                  · have p1087_0 := h1087c.1
                    have p1087_1 := h1087c.2.1
                    have p1087_2 := h1087c.2.2.1
                    have p1087_3 := h1087c.2.2.2
                    linarith only [h1085, hlam, p1087_1]
                  · have p1087_0 := h1087c.1
                    have p1087_1 := h1087c.2.1
                    have p1087_2 := h1087c.2.2.1
                    have p1087_3 := h1087c.2.2.2
                    linarith only [hlam, p1087_0]
                · linarith only [h0, h1078, h1084, h1086, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1114 | h1114
                · rcases h0bigk with h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c | h1115c
                  · have p1115_0 := h1115c.1
                    have p1115_1 := h1115c.2.1
                    have p1115_2 := h1115c.2.2.1
                    have p1115_3 := h1115c.2.2.2
                    linarith only [hlam, p1115_0]
                  · have p1115_0 := h1115c.1
                    have p1115_1 := h1115c.2.1
                    have p1115_2 := h1115c.2.2.1
                    have p1115_3 := h1115c.2.2.2
                    linarith only [h0, hlam, p1115_1]
                  · have p1115_0 := h1115c.1
                    have p1115_1 := h1115c.2.1
                    have p1115_2 := h1115c.2.2.1
                    have p1115_3 := h1115c.2.2.2
                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1115_1, u3ehi0]
                  · have p1115_0 := h1115c.1
                    have p1115_1 := h1115c.2.1
                    have p1115_2 := h1115c.2.2.1
                    have p1115_3 := h1115c.2.2.2
                    linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1115_1]
                  · have p1115_0 := h1115c.1
                    have p1115_1 := h1115c.2.1
                    have p1115_2 := h1115c.2.2.1
                    have p1115_3 := h1115c.2.2.2
                    linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1115_1]
                  · have p1115_0 := h1115c.1
                    have p1115_1 := h1115c.2.1
                    have p1115_2 := h1115c.2.2.1
                    have p1115_3 := h1115c.2.2.2
                    linarith only [h0, hc01, hc12, hlam, hphi, p1115_1]
                  · have p1115_0 := h1115c.1
                    have p1115_1 := h1115c.2.1
                    have p1115_2 := h1115c.2.2.1
                    have p1115_3 := h1115c.2.2.2
                    linarith only [hlam, p1115_0]
                  · have p1115_0 := h1115c.1
                    have p1115_1 := h1115c.2.1
                    have p1115_2 := h1115c.2.2.1
                    have p1115_3 := h1115c.2.2.2
                    linarith only [h0, h1080, h1114, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1115_1, u3ehi4]
                  · have p1115_0 := h1115c.1
                    have p1115_1 := h1115c.2.1
                    have p1115_2 := h1115c.2.2.1
                    have p1115_3 := h1115c.2.2.2
                    linarith only [h0, h1083, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1115_1, u3ehi3]
                  · have p1115_0 := h1115c.1
                    have p1115_1 := h1115c.2.1
                    have p1115_2 := h1115c.2.2.1
                    have p1115_3 := h1115c.2.2.2
                    linarith only [h0, h1084, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1115_1, u3ehi4]
                  · have p1115_0 := h1115c.1
                    have p1115_1 := h1115c.2.1
                    have p1115_2 := h1115c.2.2.1
                    have p1115_3 := h1115c.2.2.2
                    linarith only [h1078, hlam, p1115_1]
                  · have p1115_0 := h1115c.1
                    have p1115_1 := h1115c.2.1
                    have p1115_2 := h1115c.2.2.1
                    have p1115_3 := h1115c.2.2.2
                    linarith only [h1080, hlam, p1115_1]
                  · have p1115_0 := h1115c.1
                    have p1115_1 := h1115c.2.1
                    have p1115_2 := h1115c.2.2.1
                    have p1115_3 := h1115c.2.2.2
                    linarith only [hlam, p1115_0]
                  · have p1115_0 := h1115c.1
                    have p1115_1 := h1115c.2.1
                    have p1115_2 := h1115c.2.2.1
                    have p1115_3 := h1115c.2.2.2
                    linarith only [h1078, h1083, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1115_1, u3ehi3]
                  · have p1115_0 := h1115c.1
                    have p1115_1 := h1115c.2.1
                    have p1115_2 := h1115c.2.2.1
                    have p1115_3 := h1115c.2.2.2
                    linarith only [h0, h1078, h1084, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1115_1, u3ehi4]
                  · have p1115_0 := h1115c.1
                    have p1115_1 := h1115c.2.1
                    have p1115_2 := h1115c.2.2.1
                    have p1115_3 := h1115c.2.2.2
                    linarith only [h1078, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1115_1, u3ehi0]
                  · have p1115_0 := h1115c.1
                    have p1115_1 := h1115c.2.1
                    have p1115_2 := h1115c.2.2.1
                    have p1115_3 := h1115c.2.2.2
                    linarith only [h1081, hlam, p1115_0]
                  · have p1115_0 := h1115c.1
                    have p1115_1 := h1115c.2.1
                    have p1115_2 := h1115c.2.2.1
                    have p1115_3 := h1115c.2.2.2
                    linarith only [h1083, hlam, p1115_0]
                  · have p1115_0 := h1115c.1
                    have p1115_1 := h1115c.2.1
                    have p1115_2 := h1115c.2.2.1
                    have p1115_3 := h1115c.2.2.2
                    linarith only [hlam, p1115_0]
                  · have p1115_0 := h1115c.1
                    have p1115_1 := h1115c.2.1
                    have p1115_2 := h1115c.2.2.1
                    have p1115_3 := h1115c.2.2.2
                    linarith only [h1085, hlam, p1115_0]
                  · have p1115_0 := h1115c.1
                    have p1115_1 := h1115c.2.1
                    have p1115_2 := h1115c.2.2.1
                    have p1115_3 := h1115c.2.2.2
                    linarith only [h1079, hlam, p1115_0]
                  · have p1115_0 := h1115c.1
                    have p1115_1 := h1115c.2.1
                    have p1115_2 := h1115c.2.2.1
                    have p1115_3 := h1115c.2.2.2
                    linarith only [h1082, hlam, p1115_1]
                  · have p1115_0 := h1115c.1
                    have p1115_1 := h1115c.2.1
                    have p1115_2 := h1115c.2.2.1
                    have p1115_3 := h1115c.2.2.2
                    linarith only [h1084, hlam, p1115_0]
                  · have p1115_0 := h1115c.1
                    have p1115_1 := h1115c.2.1
                    have p1115_2 := h1115c.2.2.1
                    have p1115_3 := h1115c.2.2.2
                    linarith only [h0, h1079, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1115_1]
                  · have p1115_0 := h1115c.1
                    have p1115_1 := h1115c.2.1
                    have p1115_2 := h1115c.2.2.1
                    have p1115_3 := h1115c.2.2.2
                    linarith only [hlam, p1115_0]
                · linarith only [h0, h1078, h1084, h1114, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h1083, h1084, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1143 | h1143
            · linarith only [h1083, h1143, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1145 | h1145
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1146 | h1146
                · linarith only [h0, h1080, h1143, h1146, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                · rcases h0bigk with h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c | h1148c
                  · have p1148_0 := h1148c.1
                    have p1148_1 := h1148c.2.1
                    have p1148_2 := h1148c.2.2.1
                    have p1148_3 := h1148c.2.2.2
                    linarith only [hlam, p1148_0]
                  · have p1148_0 := h1148c.1
                    have p1148_1 := h1148c.2.1
                    have p1148_2 := h1148c.2.2.1
                    have p1148_3 := h1148c.2.2.2
                    linarith only [h0, hlam, p1148_1]
                  · have p1148_0 := h1148c.1
                    have p1148_1 := h1148c.2.1
                    have p1148_2 := h1148c.2.2.1
                    have p1148_3 := h1148c.2.2.2
                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1148_1, u3ehi0]
                  · have p1148_0 := h1148c.1
                    have p1148_1 := h1148c.2.1
                    have p1148_2 := h1148c.2.2.1
                    have p1148_3 := h1148c.2.2.2
                    linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1148_1]
                  · have p1148_0 := h1148c.1
                    have p1148_1 := h1148c.2.1
                    have p1148_2 := h1148c.2.2.1
                    have p1148_3 := h1148c.2.2.2
                    linarith only [h0, h1079, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1148_1]
                  · have p1148_0 := h1148c.1
                    have p1148_1 := h1148c.2.1
                    have p1148_2 := h1148c.2.2.1
                    have p1148_3 := h1148c.2.2.2
                    linarith only [h0, hc01, hc12, hlam, hphi, p1148_1]
                  · have p1148_0 := h1148c.1
                    have p1148_1 := h1148c.2.1
                    have p1148_2 := h1148c.2.2.1
                    have p1148_3 := h1148c.2.2.2
                    linarith only [hlam, p1148_0]
                  · have p1148_0 := h1148c.1
                    have p1148_1 := h1148c.2.1
                    have p1148_2 := h1148c.2.2.1
                    have p1148_3 := h1148c.2.2.2
                    linarith only [h0, h1080, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1148_1, u3ehi2]
                  · have p1148_0 := h1148c.1
                    have p1148_1 := h1148c.2.1
                    have p1148_2 := h1148c.2.2.1
                    have p1148_3 := h1148c.2.2.2
                    linarith only [h0, h1145, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1148_1]
                  · have p1148_0 := h1148c.1
                    have p1148_1 := h1148c.2.1
                    have p1148_2 := h1148c.2.2.1
                    have p1148_3 := h1148c.2.2.2
                    linarith only [h0, h1080, h1143, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1148_1, u3ehi2]
                  · have p1148_0 := h1148c.1
                    have p1148_1 := h1148c.2.1
                    have p1148_2 := h1148c.2.2.1
                    have p1148_3 := h1148c.2.2.2
                    linarith only [h1078, hlam, p1148_1]
                  · have p1148_0 := h1148c.1
                    have p1148_1 := h1148c.2.1
                    have p1148_2 := h1148c.2.2.1
                    have p1148_3 := h1148c.2.2.2
                    linarith only [h1080, hlam, p1148_1]
                  · have p1148_0 := h1148c.1
                    have p1148_1 := h1148c.2.1
                    have p1148_2 := h1148c.2.2.1
                    have p1148_3 := h1148c.2.2.2
                    linarith only [hlam, p1148_0]
                  · have p1148_0 := h1148c.1
                    have p1148_1 := h1148c.2.1
                    have p1148_2 := h1148c.2.2.1
                    have p1148_3 := h1148c.2.2.2
                    linarith only [h1083, hlam, p1148_1]
                  · have p1148_0 := h1148c.1
                    have p1148_1 := h1148c.2.1
                    have p1148_2 := h1148c.2.2.1
                    have p1148_3 := h1148c.2.2.2
                    linarith only [h1143, hlam, p1148_1]
                  · have p1148_0 := h1148c.1
                    have p1148_1 := h1148c.2.1
                    have p1148_2 := h1148c.2.2.1
                    have p1148_3 := h1148c.2.2.2
                    linarith only [h1078, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1148_1, u3ehi1]
                  · have p1148_0 := h1148c.1
                    have p1148_1 := h1148c.2.1
                    have p1148_2 := h1148c.2.2.1
                    have p1148_3 := h1148c.2.2.2
                    linarith only [h1081, hlam, p1148_0]
                  · have p1148_0 := h1148c.1
                    have p1148_1 := h1148c.2.1
                    have p1148_2 := h1148c.2.2.1
                    have p1148_3 := h1148c.2.2.2
                    linarith only [h1080, h1083, hc34, hlam, hphi, p1148_1, u3ehi2]
                  · have p1148_0 := h1148c.1
                    have p1148_1 := h1148c.2.1
                    have p1148_2 := h1148c.2.2.1
                    have p1148_3 := h1148c.2.2.2
                    linarith only [hlam, p1148_0]
                  · have p1148_0 := h1148c.1
                    have p1148_1 := h1148c.2.1
                    have p1148_2 := h1148c.2.2.1
                    have p1148_3 := h1148c.2.2.2
                    linarith only [h1080, h1083, h1143, hc34, hlam, hphi, p1148_1, u3ehi2]
                  · have p1148_0 := h1148c.1
                    have p1148_1 := h1148c.2.1
                    have p1148_2 := h1148c.2.2.1
                    have p1148_3 := h1148c.2.2.2
                    linarith only [h1079, hlam, p1148_0]
                  · have p1148_0 := h1148c.1
                    have p1148_1 := h1148c.2.1
                    have p1148_2 := h1148c.2.2.1
                    have p1148_3 := h1148c.2.2.2
                    linarith only [h1082, hlam, p1148_1]
                  · have p1148_0 := h1148c.1
                    have p1148_1 := h1148c.2.1
                    have p1148_2 := h1148c.2.2.1
                    have p1148_3 := h1148c.2.2.2
                    linarith only [h1080, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1148_1, u3ehi2]
                  · have p1148_0 := h1148c.1
                    have p1148_1 := h1148c.2.1
                    have p1148_2 := h1148c.2.2.1
                    have p1148_3 := h1148c.2.2.2
                    linarith only [h1145, hlam, p1148_1]
                  · have p1148_0 := h1148c.1
                    have p1148_1 := h1148c.2.1
                    have p1148_2 := h1148c.2.2.1
                    have p1148_3 := h1148c.2.2.2
                    linarith only [hlam, p1148_0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1174 | h1174
                · linarith only [h1080, h1083, h1174, hc34, hlam, hphi, u3ehi4]
                · rcases h0bigk with h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c
                  · have p1176_0 := h1176c.1
                    have p1176_1 := h1176c.2.1
                    have p1176_2 := h1176c.2.2.1
                    have p1176_3 := h1176c.2.2.2
                    linarith only [hlam, p1176_0]
                  · have p1176_0 := h1176c.1
                    have p1176_1 := h1176c.2.1
                    have p1176_2 := h1176c.2.2.1
                    have p1176_3 := h1176c.2.2.2
                    linarith only [h0, hlam, p1176_1]
                  · have p1176_0 := h1176c.1
                    have p1176_1 := h1176c.2.1
                    have p1176_2 := h1176c.2.2.1
                    have p1176_3 := h1176c.2.2.2
                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1176_1, u3ehi0]
                  · have p1176_0 := h1176c.1
                    have p1176_1 := h1176c.2.1
                    have p1176_2 := h1176c.2.2.1
                    have p1176_3 := h1176c.2.2.2
                    linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1176_1]
                  · have p1176_0 := h1176c.1
                    have p1176_1 := h1176c.2.1
                    have p1176_2 := h1176c.2.2.1
                    have p1176_3 := h1176c.2.2.2
                    linarith only [h0, h1145, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1176_1]
                  · have p1176_0 := h1176c.1
                    have p1176_1 := h1176c.2.1
                    have p1176_2 := h1176c.2.2.1
                    have p1176_3 := h1176c.2.2.2
                    linarith only [h0, hc01, hc12, hlam, hphi, p1176_1]
                  · have p1176_0 := h1176c.1
                    have p1176_1 := h1176c.2.1
                    have p1176_2 := h1176c.2.2.1
                    have p1176_3 := h1176c.2.2.2
                    linarith only [hlam, p1176_0]
                  · have p1176_0 := h1176c.1
                    have p1176_1 := h1176c.2.1
                    have p1176_2 := h1176c.2.2.1
                    have p1176_3 := h1176c.2.2.2
                    linarith only [h0, h1080, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1176_1, u3ehi2]
                  · have p1176_0 := h1176c.1
                    have p1176_1 := h1176c.2.1
                    have p1176_2 := h1176c.2.2.1
                    have p1176_3 := h1176c.2.2.2
                    linarith only [h0, h1080, h1083, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1176_1, u3ehi2]
                  · have p1176_0 := h1176c.1
                    have p1176_1 := h1176c.2.1
                    have p1176_2 := h1176c.2.2.1
                    have p1176_3 := h1176c.2.2.2
                    linarith only [h0, h1080, h1083, h1145, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1176_1, u3ehi2]
                  · have p1176_0 := h1176c.1
                    have p1176_1 := h1176c.2.1
                    have p1176_2 := h1176c.2.2.1
                    have p1176_3 := h1176c.2.2.2
                    linarith only [h1078, hlam, p1176_1]
                  · have p1176_0 := h1176c.1
                    have p1176_1 := h1176c.2.1
                    have p1176_2 := h1176c.2.2.1
                    have p1176_3 := h1176c.2.2.2
                    linarith only [h1080, hlam, p1176_1]
                  · have p1176_0 := h1176c.1
                    have p1176_1 := h1176c.2.1
                    have p1176_2 := h1176c.2.2.1
                    have p1176_3 := h1176c.2.2.2
                    linarith only [hlam, p1176_0]
                  · have p1176_0 := h1176c.1
                    have p1176_1 := h1176c.2.1
                    have p1176_2 := h1176c.2.2.1
                    have p1176_3 := h1176c.2.2.2
                    linarith only [h1083, hlam, p1176_1]
                  · have p1176_0 := h1176c.1
                    have p1176_1 := h1176c.2.1
                    have p1176_2 := h1176c.2.2.1
                    have p1176_3 := h1176c.2.2.2
                    linarith only [h1143, hlam, p1176_1]
                  · have p1176_0 := h1176c.1
                    have p1176_1 := h1176c.2.1
                    have p1176_2 := h1176c.2.2.1
                    have p1176_3 := h1176c.2.2.2
                    linarith only [h1078, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1176_1, u3ehi1]
                  · have p1176_0 := h1176c.1
                    have p1176_1 := h1176c.2.1
                    have p1176_2 := h1176c.2.2.1
                    have p1176_3 := h1176c.2.2.2
                    linarith only [h1081, hlam, p1176_0]
                  · have p1176_0 := h1176c.1
                    have p1176_1 := h1176c.2.1
                    have p1176_2 := h1176c.2.2.1
                    have p1176_3 := h1176c.2.2.2
                    linarith only [h0, h1079, h1080, h1145, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1176_1, u3ehi2]
                  · have p1176_0 := h1176c.1
                    have p1176_1 := h1176c.2.1
                    have p1176_2 := h1176c.2.2.1
                    have p1176_3 := h1176c.2.2.2
                    linarith only [hlam, p1176_0]
                  · have p1176_0 := h1176c.1
                    have p1176_1 := h1176c.2.1
                    have p1176_2 := h1176c.2.2.1
                    have p1176_3 := h1176c.2.2.2
                    linarith only [h1145, hlam, p1176_0]
                  · have p1176_0 := h1176c.1
                    have p1176_1 := h1176c.2.1
                    have p1176_2 := h1176c.2.2.1
                    have p1176_3 := h1176c.2.2.2
                    linarith only [h1079, hlam, p1176_0]
                  · have p1176_0 := h1176c.1
                    have p1176_1 := h1176c.2.1
                    have p1176_2 := h1176c.2.2.1
                    have p1176_3 := h1176c.2.2.2
                    linarith only [h1082, hlam, p1176_1]
                  · have p1176_0 := h1176c.1
                    have p1176_1 := h1176c.2.1
                    have p1176_2 := h1176c.2.2.1
                    have p1176_3 := h1176c.2.2.2
                    linarith only [h0, h1079, h1080, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1176_1, u3ehi2]
                  · have p1176_0 := h1176c.1
                    have p1176_1 := h1176c.2.1
                    have p1176_2 := h1176c.2.2.1
                    have p1176_3 := h1176c.2.2.2
                    linarith only [h0, h1079, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1176_1]
                  · have p1176_0 := h1176c.1
                    have p1176_1 := h1176c.2.1
                    have p1176_2 := h1176c.2.2.1
                    have p1176_3 := h1176c.2.2.2
                    linarith only [hlam, p1176_0]
        · linarith only [h0, h1079, h1082, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1203 | h1203
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1204 | h1204
          · linarith only [h0, h1078, h1081, h1204, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1206 | h1206
            · linarith only [h1204, h1206, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1208 | h1208
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1209 | h1209
                · linarith only [h1080, h1206, h1209, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                · rcases h0bigk with h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c
                  · have p1211_0 := h1211c.1
                    have p1211_1 := h1211c.2.1
                    have p1211_2 := h1211c.2.2.1
                    have p1211_3 := h1211c.2.2.2
                    linarith only [hlam, p1211_0]
                  · have p1211_0 := h1211c.1
                    have p1211_1 := h1211c.2.1
                    have p1211_2 := h1211c.2.2.1
                    have p1211_3 := h1211c.2.2.2
                    linarith only [h0, hlam, p1211_1]
                  · have p1211_0 := h1211c.1
                    have p1211_1 := h1211c.2.1
                    have p1211_2 := h1211c.2.2.1
                    have p1211_3 := h1211c.2.2.2
                    linarith only [h0, h1078, h1081, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1211_1, u3ehi1]
                  · have p1211_0 := h1211c.1
                    have p1211_1 := h1211c.2.1
                    have p1211_2 := h1211c.2.2.1
                    have p1211_3 := h1211c.2.2.2
                    linarith only [h0, h1081, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1211_1]
                  · have p1211_0 := h1211c.1
                    have p1211_1 := h1211c.2.1
                    have p1211_2 := h1211c.2.2.1
                    have p1211_3 := h1211c.2.2.2
                    linarith only [h0, h1081, hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1211_1]
                  · have p1211_0 := h1211c.1
                    have p1211_1 := h1211c.2.1
                    have p1211_2 := h1211c.2.2.1
                    have p1211_3 := h1211c.2.2.2
                    linarith only [h1081, hc01, hc24, hlam, hphi, ht12, p1211_1]
                  · have p1211_0 := h1211c.1
                    have p1211_1 := h1211c.2.1
                    have p1211_2 := h1211c.2.2.1
                    have p1211_3 := h1211c.2.2.2
                    linarith only [hlam, p1211_0]
                  · have p1211_0 := h1211c.1
                    have p1211_1 := h1211c.2.1
                    have p1211_2 := h1211c.2.2.1
                    have p1211_3 := h1211c.2.2.2
                    linarith only [h1078, h1081, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1211_1, u3ehi1]
                  · have p1211_0 := h1211c.1
                    have p1211_1 := h1211c.2.1
                    have p1211_2 := h1211c.2.2.1
                    have p1211_3 := h1211c.2.2.2
                    linarith only [h1081, hlam, p1211_1]
                  · have p1211_0 := h1211c.1
                    have p1211_1 := h1211c.2.1
                    have p1211_2 := h1211c.2.2.1
                    have p1211_3 := h1211c.2.2.2
                    linarith only [h1079, h1081, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1211_1]
                  · have p1211_0 := h1211c.1
                    have p1211_1 := h1211c.2.1
                    have p1211_2 := h1211c.2.2.1
                    have p1211_3 := h1211c.2.2.2
                    linarith only [h1078, hlam, p1211_1]
                  · have p1211_0 := h1211c.1
                    have p1211_1 := h1211c.2.1
                    have p1211_2 := h1211c.2.2.1
                    have p1211_3 := h1211c.2.2.2
                    linarith only [h1080, hlam, p1211_1]
                  · have p1211_0 := h1211c.1
                    have p1211_1 := h1211c.2.1
                    have p1211_2 := h1211c.2.2.1
                    have p1211_3 := h1211c.2.2.2
                    linarith only [hlam, p1211_0]
                  · have p1211_0 := h1211c.1
                    have p1211_1 := h1211c.2.1
                    have p1211_2 := h1211c.2.2.1
                    have p1211_3 := h1211c.2.2.2
                    linarith only [h1204, hlam, p1211_1]
                  · have p1211_0 := h1211c.1
                    have p1211_1 := h1211c.2.1
                    have p1211_2 := h1211c.2.2.1
                    have p1211_3 := h1211c.2.2.2
                    linarith only [h1206, hlam, p1211_1]
                  · have p1211_0 := h1211c.1
                    have p1211_1 := h1211c.2.1
                    have p1211_2 := h1211c.2.2.1
                    have p1211_3 := h1211c.2.2.2
                    linarith only [h1078, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1211_1, u3ehi1]
                  · have p1211_0 := h1211c.1
                    have p1211_1 := h1211c.2.1
                    have p1211_2 := h1211c.2.2.1
                    have p1211_3 := h1211c.2.2.2
                    linarith only [h0, h1078, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1211_1, u3ehi1]
                  · have p1211_0 := h1211c.1
                    have p1211_1 := h1211c.2.1
                    have p1211_2 := h1211c.2.2.1
                    have p1211_3 := h1211c.2.2.2
                    linarith only [h1078, h1204, hc34, hlam, hphi, p1211_1, u3ehi1]
                  · have p1211_0 := h1211c.1
                    have p1211_1 := h1211c.2.1
                    have p1211_2 := h1211c.2.2.1
                    have p1211_3 := h1211c.2.2.2
                    linarith only [hlam, p1211_0]
                  · have p1211_0 := h1211c.1
                    have p1211_1 := h1211c.2.1
                    have p1211_2 := h1211c.2.2.1
                    have p1211_3 := h1211c.2.2.2
                    linarith only [h1078, h1204, h1206, hc34, hlam, hphi, p1211_1, u3ehi1]
                  · have p1211_0 := h1211c.1
                    have p1211_1 := h1211c.2.1
                    have p1211_2 := h1211c.2.2.1
                    have p1211_3 := h1211c.2.2.2
                    linarith only [h1079, hlam, p1211_0]
                  · have p1211_0 := h1211c.1
                    have p1211_1 := h1211c.2.1
                    have p1211_2 := h1211c.2.2.1
                    have p1211_3 := h1211c.2.2.2
                    linarith only [h1203, hlam, p1211_1]
                  · have p1211_0 := h1211c.1
                    have p1211_1 := h1211c.2.1
                    have p1211_2 := h1211c.2.2.1
                    have p1211_3 := h1211c.2.2.2
                    linarith only [h1078, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1211_1, u3ehi1]
                  · have p1211_0 := h1211c.1
                    have p1211_1 := h1211c.2.1
                    have p1211_2 := h1211c.2.2.1
                    have p1211_3 := h1211c.2.2.2
                    linarith only [h1208, hlam, p1211_1]
                  · have p1211_0 := h1211c.1
                    have p1211_1 := h1211c.2.1
                    have p1211_2 := h1211c.2.2.1
                    have p1211_3 := h1211c.2.2.2
                    linarith only [hlam, p1211_0]
              · linarith only [h0, h1078, h1081, h1208, hc45, hlam, hphi, ht34, u3ehi1]
        · linarith only [h0, h1079, h1203, hlam]
    · linarith only [h0, h1078, h1080, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1240 | h1240
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1241 | h1241
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1242 | h1242
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1243 | h1243
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1244 | h1244
            · linarith only [h1078, h1079, h1244, hlam]
            · linarith only [h1243, h1244, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1247 | h1247
            · linarith only [h1243, h1247, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1249 | h1249
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1250 | h1250
                · linarith only [h1240, h1247, h1250, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                · rcases h0bigk with h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c | h1252c
                  · have p1252_0 := h1252c.1
                    have p1252_1 := h1252c.2.1
                    have p1252_2 := h1252c.2.2.1
                    have p1252_3 := h1252c.2.2.2
                    linarith only [hlam, p1252_0]
                  · have p1252_0 := h1252c.1
                    have p1252_1 := h1252c.2.1
                    have p1252_2 := h1252c.2.2.1
                    have p1252_3 := h1252c.2.2.2
                    linarith only [h0, hlam, p1252_1]
                  · have p1252_0 := h1252c.1
                    have p1252_1 := h1252c.2.1
                    have p1252_2 := h1252c.2.2.1
                    have p1252_3 := h1252c.2.2.2
                    linarith only [h1240, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1252_1, u3ehi2]
                  · have p1252_0 := h1252c.1
                    have p1252_1 := h1252c.2.1
                    have p1252_2 := h1252c.2.2.1
                    have p1252_3 := h1252c.2.2.2
                    linarith only [h1079, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p1252_1]
                  · have p1252_0 := h1252c.1
                    have p1252_1 := h1252c.2.1
                    have p1252_2 := h1252c.2.2.1
                    have p1252_3 := h1252c.2.2.2
                    linarith only [h1079, hlam, p1252_1]
                  · have p1252_0 := h1252c.1
                    have p1252_1 := h1252c.2.1
                    have p1252_2 := h1252c.2.2.1
                    have p1252_3 := h1252c.2.2.2
                    linarith only [h0, hc01, hc12, hlam, hphi, p1252_1]
                  · have p1252_0 := h1252c.1
                    have p1252_1 := h1252c.2.1
                    have p1252_2 := h1252c.2.2.1
                    have p1252_3 := h1252c.2.2.2
                    linarith only [hlam, p1252_0]
                  · have p1252_0 := h1252c.1
                    have p1252_1 := h1252c.2.1
                    have p1252_2 := h1252c.2.2.1
                    have p1252_3 := h1252c.2.2.2
                    linarith only [h0, h1240, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1252_1, u3ehi2]
                  · have p1252_0 := h1252c.1
                    have p1252_1 := h1252c.2.1
                    have p1252_2 := h1252c.2.2.1
                    have p1252_3 := h1252c.2.2.2
                    linarith only [h0, h1078, h1079, h1249, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1252_1, u3ehi1]
                  · have p1252_0 := h1252c.1
                    have p1252_1 := h1252c.2.1
                    have p1252_2 := h1252c.2.2.1
                    have p1252_3 := h1252c.2.2.2
                    linarith only [h0, h1078, h1079, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1252_1, u3ehi1]
                  · have p1252_0 := h1252c.1
                    have p1252_1 := h1252c.2.1
                    have p1252_2 := h1252c.2.2.1
                    have p1252_3 := h1252c.2.2.2
                    linarith only [h1078, hlam, p1252_1]
                  · have p1252_0 := h1252c.1
                    have p1252_1 := h1252c.2.1
                    have p1252_2 := h1252c.2.2.1
                    have p1252_3 := h1252c.2.2.2
                    linarith only [h1240, hlam, p1252_1]
                  · have p1252_0 := h1252c.1
                    have p1252_1 := h1252c.2.1
                    have p1252_2 := h1252c.2.2.1
                    have p1252_3 := h1252c.2.2.2
                    linarith only [hlam, p1252_0]
                  · have p1252_0 := h1252c.1
                    have p1252_1 := h1252c.2.1
                    have p1252_2 := h1252c.2.2.1
                    have p1252_3 := h1252c.2.2.2
                    linarith only [h1243, hlam, p1252_1]
                  · have p1252_0 := h1252c.1
                    have p1252_1 := h1252c.2.1
                    have p1252_2 := h1252c.2.2.1
                    have p1252_3 := h1252c.2.2.2
                    linarith only [h1247, hlam, p1252_1]
                  · have p1252_0 := h1252c.1
                    have p1252_1 := h1252c.2.1
                    have p1252_2 := h1252c.2.2.1
                    have p1252_3 := h1252c.2.2.2
                    linarith only [h1078, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1252_1, u3ehi1]
                  · have p1252_0 := h1252c.1
                    have p1252_1 := h1252c.2.1
                    have p1252_2 := h1252c.2.2.1
                    have p1252_3 := h1252c.2.2.2
                    linarith only [h1241, hlam, p1252_0]
                  · have p1252_0 := h1252c.1
                    have p1252_1 := h1252c.2.1
                    have p1252_2 := h1252c.2.2.1
                    have p1252_3 := h1252c.2.2.2
                    linarith only [h1240, h1243, hc34, hlam, hphi, p1252_1, u3ehi2]
                  · have p1252_0 := h1252c.1
                    have p1252_1 := h1252c.2.1
                    have p1252_2 := h1252c.2.2.1
                    have p1252_3 := h1252c.2.2.2
                    linarith only [hlam, p1252_0]
                  · have p1252_0 := h1252c.1
                    have p1252_1 := h1252c.2.1
                    have p1252_2 := h1252c.2.2.1
                    have p1252_3 := h1252c.2.2.2
                    linarith only [h1078, h1079, h1243, hc34, hlam, hphi, p1252_1, u3ehi1]
                  · have p1252_0 := h1252c.1
                    have p1252_1 := h1252c.2.1
                    have p1252_2 := h1252c.2.2.1
                    have p1252_3 := h1252c.2.2.2
                    linarith only [h1078, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1252_1, u3ehi1]
                  · have p1252_0 := h1252c.1
                    have p1252_1 := h1252c.2.1
                    have p1252_2 := h1252c.2.2.1
                    have p1252_3 := h1252c.2.2.2
                    linarith only [h1242, hlam, p1252_1]
                  · have p1252_0 := h1252c.1
                    have p1252_1 := h1252c.2.1
                    have p1252_2 := h1252c.2.2.1
                    have p1252_3 := h1252c.2.2.2
                    linarith only [h1240, h1247, hc35, hlam, hphi, p1252_1, u3ehi2]
                  · have p1252_0 := h1252c.1
                    have p1252_1 := h1252c.2.1
                    have p1252_2 := h1252c.2.2.1
                    have p1252_3 := h1252c.2.2.2
                    linarith only [h1249, hlam, p1252_1]
                  · have p1252_0 := h1252c.1
                    have p1252_1 := h1252c.2.1
                    have p1252_2 := h1252c.2.2.1
                    have p1252_3 := h1252c.2.2.2
                    linarith only [hlam, p1252_0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1278 | h1278
                · linarith only [h1240, h1243, h1278, hc34, hlam, hphi, u3ehi4]
                · rcases h0bigk with h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c | h1280c
                  · have p1280_0 := h1280c.1
                    have p1280_1 := h1280c.2.1
                    have p1280_2 := h1280c.2.2.1
                    have p1280_3 := h1280c.2.2.2
                    linarith only [hlam, p1280_0]
                  · have p1280_0 := h1280c.1
                    have p1280_1 := h1280c.2.1
                    have p1280_2 := h1280c.2.2.1
                    have p1280_3 := h1280c.2.2.2
                    linarith only [h0, hlam, p1280_1]
                  · have p1280_0 := h1280c.1
                    have p1280_1 := h1280c.2.1
                    have p1280_2 := h1280c.2.2.1
                    have p1280_3 := h1280c.2.2.2
                    linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1280_1, u3ehi0]
                  · have p1280_0 := h1280c.1
                    have p1280_1 := h1280c.2.1
                    have p1280_2 := h1280c.2.2.1
                    have p1280_3 := h1280c.2.2.2
                    linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1280_1]
                  · have p1280_0 := h1280c.1
                    have p1280_1 := h1280c.2.1
                    have p1280_2 := h1280c.2.2.1
                    have p1280_3 := h1280c.2.2.2
                    linarith only [h1079, hlam, p1280_1]
                  · have p1280_0 := h1280c.1
                    have p1280_1 := h1280c.2.1
                    have p1280_2 := h1280c.2.2.1
                    have p1280_3 := h1280c.2.2.2
                    linarith only [h0, hc01, hc12, hlam, hphi, p1280_1]
                  · have p1280_0 := h1280c.1
                    have p1280_1 := h1280c.2.1
                    have p1280_2 := h1280c.2.2.1
                    have p1280_3 := h1280c.2.2.2
                    linarith only [hlam, p1280_0]
                  · have p1280_0 := h1280c.1
                    have p1280_1 := h1280c.2.1
                    have p1280_2 := h1280c.2.2.1
                    have p1280_3 := h1280c.2.2.2
                    linarith only [h0, h1240, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1280_1, u3ehi2]
                  · have p1280_0 := h1280c.1
                    have p1280_1 := h1280c.2.1
                    have p1280_2 := h1280c.2.2.1
                    have p1280_3 := h1280c.2.2.2
                    linarith only [h0, h1240, h1243, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1280_1, u3ehi2]
                  · have p1280_0 := h1280c.1
                    have p1280_1 := h1280c.2.1
                    have p1280_2 := h1280c.2.2.1
                    have p1280_3 := h1280c.2.2.2
                    linarith only [h0, h1078, h1079, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1280_1, u3ehi1]
                  · have p1280_0 := h1280c.1
                    have p1280_1 := h1280c.2.1
                    have p1280_2 := h1280c.2.2.1
                    have p1280_3 := h1280c.2.2.2
                    linarith only [h1078, hlam, p1280_1]
                  · have p1280_0 := h1280c.1
                    have p1280_1 := h1280c.2.1
                    have p1280_2 := h1280c.2.2.1
                    have p1280_3 := h1280c.2.2.2
                    linarith only [h1240, hlam, p1280_1]
                  · have p1280_0 := h1280c.1
                    have p1280_1 := h1280c.2.1
                    have p1280_2 := h1280c.2.2.1
                    have p1280_3 := h1280c.2.2.2
                    linarith only [hlam, p1280_0]
                  · have p1280_0 := h1280c.1
                    have p1280_1 := h1280c.2.1
                    have p1280_2 := h1280c.2.2.1
                    have p1280_3 := h1280c.2.2.2
                    linarith only [h1243, hlam, p1280_1]
                  · have p1280_0 := h1280c.1
                    have p1280_1 := h1280c.2.1
                    have p1280_2 := h1280c.2.2.1
                    have p1280_3 := h1280c.2.2.2
                    linarith only [h1247, hlam, p1280_1]
                  · have p1280_0 := h1280c.1
                    have p1280_1 := h1280c.2.1
                    have p1280_2 := h1280c.2.2.1
                    have p1280_3 := h1280c.2.2.2
                    linarith only [h1078, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1280_1, u3ehi1]
                  · have p1280_0 := h1280c.1
                    have p1280_1 := h1280c.2.1
                    have p1280_2 := h1280c.2.2.1
                    have p1280_3 := h1280c.2.2.2
                    linarith only [h1241, hlam, p1280_0]
                  · have p1280_0 := h1280c.1
                    have p1280_1 := h1280c.2.1
                    have p1280_2 := h1280c.2.2.1
                    have p1280_3 := h1280c.2.2.2
                    linarith only [h1240, h1243, hc34, hlam, hphi, p1280_1, u3ehi2]
                  · have p1280_0 := h1280c.1
                    have p1280_1 := h1280c.2.1
                    have p1280_2 := h1280c.2.2.1
                    have p1280_3 := h1280c.2.2.2
                    linarith only [hlam, p1280_0]
                  · have p1280_0 := h1280c.1
                    have p1280_1 := h1280c.2.1
                    have p1280_2 := h1280c.2.2.1
                    have p1280_3 := h1280c.2.2.2
                    linarith only [h1249, hlam, p1280_0]
                  · have p1280_0 := h1280c.1
                    have p1280_1 := h1280c.2.1
                    have p1280_2 := h1280c.2.2.1
                    have p1280_3 := h1280c.2.2.2
                    linarith only [h1078, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1280_1, u3ehi1]
                  · have p1280_0 := h1280c.1
                    have p1280_1 := h1280c.2.1
                    have p1280_2 := h1280c.2.2.1
                    have p1280_3 := h1280c.2.2.2
                    linarith only [h1242, hlam, p1280_1]
                  · have p1280_0 := h1280c.1
                    have p1280_1 := h1280c.2.1
                    have p1280_2 := h1280c.2.2.1
                    have p1280_3 := h1280c.2.2.2
                    linarith only [h1240, h1247, hc35, hlam, hphi, p1280_1, u3ehi2]
                  · have p1280_0 := h1280c.1
                    have p1280_1 := h1280c.2.1
                    have p1280_2 := h1280c.2.2.1
                    have p1280_3 := h1280c.2.2.2
                    linarith only [h1249, hc04, hc45, hlam, hphi, p1280_1]
                  · have p1280_0 := h1280c.1
                    have p1280_1 := h1280c.2.1
                    have p1280_2 := h1280c.2.2.1
                    have p1280_3 := h1280c.2.2.2
                    linarith only [hlam, p1280_0]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1306 | h1306
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1307 | h1307
            · linarith only [h1078, h1079, h1307, hlam]
            · linarith only [h1306, h1307, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1310 | h1310
            · linarith only [h1306, h1310, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1312 | h1312
              · linarith only [h1241, h1242, h1312, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1314 | h1314
                · linarith only [h1240, h1242, h1310, h1314, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                · linarith only [h0, h1078, h1242, h1314, hc35, hlam, hphi, u3ehi1]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1317 | h1317
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1318 | h1318
          · linarith only [h1078, h1079, h1241, h1317, h1318, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1320 | h1320
            · linarith only [h1318, h1320, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1322 | h1322
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1323 | h1323
                · linarith only [h1240, h1241, h1320, h1323, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                · rcases h0bigk with h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c | h1325c
                  · have p1325_0 := h1325c.1
                    have p1325_1 := h1325c.2.1
                    have p1325_2 := h1325c.2.2.1
                    have p1325_3 := h1325c.2.2.2
                    linarith only [hlam, p1325_0]
                  · have p1325_0 := h1325c.1
                    have p1325_1 := h1325c.2.1
                    have p1325_2 := h1325c.2.2.1
                    have p1325_3 := h1325c.2.2.2
                    linarith only [h0, hlam, p1325_1]
                  · have p1325_0 := h1325c.1
                    have p1325_1 := h1325c.2.1
                    have p1325_2 := h1325c.2.2.1
                    have p1325_3 := h1325c.2.2.2
                    linarith only [h1078, h1079, h1241, h1317, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1325_1, u3ehi1]
                  · have p1325_0 := h1325c.1
                    have p1325_1 := h1325c.2.1
                    have p1325_2 := h1325c.2.2.1
                    have p1325_3 := h1325c.2.2.2
                    linarith only [h1079, h1241, h1317, hlam, p1325_1]
                  · have p1325_0 := h1325c.1
                    have p1325_1 := h1325c.2.1
                    have p1325_2 := h1325c.2.2.1
                    have p1325_3 := h1325c.2.2.2
                    linarith only [h1079, hlam, p1325_1]
                  · have p1325_0 := h1325c.1
                    have p1325_1 := h1325c.2.1
                    have p1325_2 := h1325c.2.2.1
                    have p1325_3 := h1325c.2.2.2
                    linarith only [h1241, hc01, hc24, hlam, hphi, ht12, p1325_1]
                  · have p1325_0 := h1325c.1
                    have p1325_1 := h1325c.2.1
                    have p1325_2 := h1325c.2.2.1
                    have p1325_3 := h1325c.2.2.2
                    linarith only [hlam, p1325_0]
                  · have p1325_0 := h1325c.1
                    have p1325_1 := h1325c.2.1
                    have p1325_2 := h1325c.2.2.1
                    have p1325_3 := h1325c.2.2.2
                    linarith only [h1078, h1241, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1325_1, u3ehi1]
                  · have p1325_0 := h1325c.1
                    have p1325_1 := h1325c.2.1
                    have p1325_2 := h1325c.2.2.1
                    have p1325_3 := h1325c.2.2.2
                    linarith only [h1241, hlam, p1325_1]
                  · have p1325_0 := h1325c.1
                    have p1325_1 := h1325c.2.1
                    have p1325_2 := h1325c.2.2.1
                    have p1325_3 := h1325c.2.2.2
                    linarith only [h1241, hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1325_1]
                  · have p1325_0 := h1325c.1
                    have p1325_1 := h1325c.2.1
                    have p1325_2 := h1325c.2.2.1
                    have p1325_3 := h1325c.2.2.2
                    linarith only [h1078, hlam, p1325_1]
                  · have p1325_0 := h1325c.1
                    have p1325_1 := h1325c.2.1
                    have p1325_2 := h1325c.2.2.1
                    have p1325_3 := h1325c.2.2.2
                    linarith only [h1240, hlam, p1325_1]
                  · have p1325_0 := h1325c.1
                    have p1325_1 := h1325c.2.1
                    have p1325_2 := h1325c.2.2.1
                    have p1325_3 := h1325c.2.2.2
                    linarith only [hlam, p1325_0]
                  · have p1325_0 := h1325c.1
                    have p1325_1 := h1325c.2.1
                    have p1325_2 := h1325c.2.2.1
                    have p1325_3 := h1325c.2.2.2
                    linarith only [h1318, hlam, p1325_1]
                  · have p1325_0 := h1325c.1
                    have p1325_1 := h1325c.2.1
                    have p1325_2 := h1325c.2.2.1
                    have p1325_3 := h1325c.2.2.2
                    linarith only [h1320, hlam, p1325_1]
                  · have p1325_0 := h1325c.1
                    have p1325_1 := h1325c.2.1
                    have p1325_2 := h1325c.2.2.1
                    have p1325_3 := h1325c.2.2.2
                    linarith only [h1078, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1325_1, u3ehi1]
                  · have p1325_0 := h1325c.1
                    have p1325_1 := h1325c.2.1
                    have p1325_2 := h1325c.2.2.1
                    have p1325_3 := h1325c.2.2.2
                    linarith only [h1317, hc04, hc25, hlam, hphi, ht0b, ht5b, p1325_1]
                  · have p1325_0 := h1325c.1
                    have p1325_1 := h1325c.2.1
                    have p1325_2 := h1325c.2.2.1
                    have p1325_3 := h1325c.2.2.2
                    linarith only [h1078, h1318, hc34, hlam, hphi, p1325_1, u3ehi1]
                  · have p1325_0 := h1325c.1
                    have p1325_1 := h1325c.2.1
                    have p1325_2 := h1325c.2.2.1
                    have p1325_3 := h1325c.2.2.2
                    linarith only [hlam, p1325_0]
                  · have p1325_0 := h1325c.1
                    have p1325_1 := h1325c.2.1
                    have p1325_2 := h1325c.2.2.1
                    have p1325_3 := h1325c.2.2.2
                    linarith only [h1078, h1079, h1318, hc34, hlam, hphi, p1325_1, u3ehi1]
                  · have p1325_0 := h1325c.1
                    have p1325_1 := h1325c.2.1
                    have p1325_2 := h1325c.2.2.1
                    have p1325_3 := h1325c.2.2.2
                    linarith only [h1078, h1317, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1325_1, u3ehi1]
                  · have p1325_0 := h1325c.1
                    have p1325_1 := h1325c.2.1
                    have p1325_2 := h1325c.2.2.1
                    have p1325_3 := h1325c.2.2.2
                    linarith only [h1317, hlam, p1325_1]
                  · have p1325_0 := h1325c.1
                    have p1325_1 := h1325c.2.1
                    have p1325_2 := h1325c.2.2.1
                    have p1325_3 := h1325c.2.2.2
                    linarith only [h1078, h1241, h1317, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1325_1, u3ehi1]
                  · have p1325_0 := h1325c.1
                    have p1325_1 := h1325c.2.1
                    have p1325_2 := h1325c.2.2.1
                    have p1325_3 := h1325c.2.2.2
                    linarith only [h1322, hlam, p1325_1]
                  · have p1325_0 := h1325c.1
                    have p1325_1 := h1325c.2.1
                    have p1325_2 := h1325c.2.2.1
                    have p1325_3 := h1325c.2.2.2
                    linarith only [hlam, p1325_0]
              · linarith only [h0, h1078, h1241, h1322, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1352 | h1352
          · linarith only [h0, h1078, h1241, h1352, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1354 | h1354
            · linarith only [h1352, h1354, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1356 | h1356
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1357 | h1357
                · linarith only [h1240, h1354, h1357, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                · linarith only [h0, h1078, h1317, h1357, hc35, hlam, hphi, u3ehi1]
              · linarith only [h0, h1078, h1241, h1356, hc45, hlam, hphi, ht34, u3ehi1]
    · linarith only [h0, h1078, h1240, hlam]

set_option maxHeartbeats 4238000 in
set_option maxHeartbeats 4238000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_R_L_I_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1078 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1362 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h3ehi := hb3.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1363 | h1363
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1364 | h1364
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1365 | h1365
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1366 | h1366
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1367 | h1367
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1368 | h1368
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1369 | h1369
              · rcases h0bigk with h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c | h1370c
                · have p1370_0 := h1370c.1
                  have p1370_1 := h1370c.2.1
                  have p1370_2 := h1370c.2.2.1
                  have p1370_3 := h1370c.2.2.2
                  linarith only [hlam, p1370_0]
                · have p1370_0 := h1370c.1
                  have p1370_1 := h1370c.2.1
                  have p1370_2 := h1370c.2.2.1
                  have p1370_3 := h1370c.2.2.2
                  linarith only [h0, hlam, p1370_1]
                · have p1370_0 := h1370c.1
                  have p1370_1 := h1370c.2.1
                  have p1370_2 := h1370c.2.2.1
                  have p1370_3 := h1370c.2.2.2
                  linarith only [h1078, hlam, p1370_0]
                · have p1370_0 := h1370c.1
                  have p1370_1 := h1370c.2.1
                  have p1370_2 := h1370c.2.2.1
                  have p1370_3 := h1370c.2.2.2
                  linarith only [h1078, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1370_1]
                · have p1370_0 := h1370c.1
                  have p1370_1 := h1370c.2.1
                  have p1370_2 := h1370c.2.2.1
                  have p1370_3 := h1370c.2.2.2
                  linarith only [h1078, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p1370_1]
                · have p1370_0 := h1370c.1
                  have p1370_1 := h1370c.2.1
                  have p1370_2 := h1370c.2.2.1
                  have p1370_3 := h1370c.2.2.2
                  linarith only [h1362, hc02, hc15, hlam, hphi, ht0b, ht5b, p1370_1]
                · have p1370_0 := h1370c.1
                  have p1370_1 := h1370c.2.1
                  have p1370_2 := h1370c.2.2.1
                  have p1370_3 := h1370c.2.2.2
                  linarith only [hlam, p1370_0]
                · have p1370_0 := h1370c.1
                  have p1370_1 := h1370c.2.1
                  have p1370_2 := h1370c.2.2.1
                  have p1370_3 := h1370c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1370_1, u3ehi0]
                · have p1370_0 := h1370c.1
                  have p1370_1 := h1370c.2.1
                  have p1370_2 := h1370c.2.2.1
                  have p1370_3 := h1370c.2.2.2
                  linarith only [h0, h1368, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1370_1]
                · have p1370_0 := h1370c.1
                  have p1370_1 := h1370c.2.1
                  have p1370_2 := h1370c.2.2.1
                  have p1370_3 := h1370c.2.2.2
                  linarith only [h0, h1367, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1370_1, u3ehi4]
                · have p1370_0 := h1370c.1
                  have p1370_1 := h1370c.2.1
                  have p1370_2 := h1370c.2.2.1
                  have p1370_3 := h1370c.2.2.2
                  linarith only [h1362, h1367, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1370_1, u3ehi4]
                · have p1370_0 := h1370c.1
                  have p1370_1 := h1370c.2.1
                  have p1370_2 := h1370c.2.2.1
                  have p1370_3 := h1370c.2.2.2
                  linarith only [h1363, hlam, p1370_1]
                · have p1370_0 := h1370c.1
                  have p1370_1 := h1370c.2.1
                  have p1370_2 := h1370c.2.2.1
                  have p1370_3 := h1370c.2.2.2
                  linarith only [hlam, p1370_0]
                · have p1370_0 := h1370c.1
                  have p1370_1 := h1370c.2.1
                  have p1370_2 := h1370c.2.2.1
                  have p1370_3 := h1370c.2.2.2
                  linarith only [h0, h1363, h1366, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1370_1, u3ehi3]
                · have p1370_0 := h1370c.1
                  have p1370_1 := h1370c.2.1
                  have p1370_2 := h1370c.2.2.1
                  have p1370_3 := h1370c.2.2.2
                  linarith only [h0, h1363, h1367, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1370_1, u3ehi4]
                · have p1370_0 := h1370c.1
                  have p1370_1 := h1370c.2.1
                  have p1370_2 := h1370c.2.2.1
                  have p1370_3 := h1370c.2.2.2
                  linarith only [h1362, h1365, h1369, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1370_1, u3ehi4]
                · have p1370_0 := h1370c.1
                  have p1370_1 := h1370c.2.1
                  have p1370_2 := h1370c.2.2.1
                  have p1370_3 := h1370c.2.2.2
                  linarith only [h1364, hlam, p1370_0]
                · have p1370_0 := h1370c.1
                  have p1370_1 := h1370c.2.1
                  have p1370_2 := h1370c.2.2.1
                  have p1370_3 := h1370c.2.2.2
                  linarith only [h1366, hlam, p1370_0]
                · have p1370_0 := h1370c.1
                  have p1370_1 := h1370c.2.1
                  have p1370_2 := h1370c.2.2.1
                  have p1370_3 := h1370c.2.2.2
                  linarith only [hlam, p1370_0]
                · have p1370_0 := h1370c.1
                  have p1370_1 := h1370c.2.1
                  have p1370_2 := h1370c.2.2.1
                  have p1370_3 := h1370c.2.2.2
                  linarith only [h0, h1363, h1365, h1366, h1369, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1370_1, u3ehi4]
                · have p1370_0 := h1370c.1
                  have p1370_1 := h1370c.2.1
                  have p1370_2 := h1370c.2.2.1
                  have p1370_3 := h1370c.2.2.2
                  linarith only [h1362, hlam, p1370_0]
                · have p1370_0 := h1370c.1
                  have p1370_1 := h1370c.2.1
                  have p1370_2 := h1370c.2.2.1
                  have p1370_3 := h1370c.2.2.2
                  linarith only [h1365, hlam, p1370_1]
                · have p1370_0 := h1370c.1
                  have p1370_1 := h1370c.2.1
                  have p1370_2 := h1370c.2.2.1
                  have p1370_3 := h1370c.2.2.2
                  linarith only [h1367, hlam, p1370_0]
                · have p1370_0 := h1370c.1
                  have p1370_1 := h1370c.2.1
                  have p1370_2 := h1370c.2.2.1
                  have p1370_3 := h1370c.2.2.2
                  linarith only [h1368, hlam, p1370_1]
                · have p1370_0 := h1370c.1
                  have p1370_1 := h1370c.2.1
                  have p1370_2 := h1370c.2.2.1
                  have p1370_3 := h1370c.2.2.2
                  linarith only [hlam, p1370_0]
              · rcases h0bigk with h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c
                · have p1396_0 := h1396c.1
                  have p1396_1 := h1396c.2.1
                  have p1396_2 := h1396c.2.2.1
                  have p1396_3 := h1396c.2.2.2
                  linarith only [hlam, p1396_0]
                · have p1396_0 := h1396c.1
                  have p1396_1 := h1396c.2.1
                  have p1396_2 := h1396c.2.2.1
                  have p1396_3 := h1396c.2.2.2
                  linarith only [h0, hlam, p1396_1]
                · have p1396_0 := h1396c.1
                  have p1396_1 := h1396c.2.1
                  have p1396_2 := h1396c.2.2.1
                  have p1396_3 := h1396c.2.2.2
                  linarith only [h1078, hlam, p1396_0]
                · have p1396_0 := h1396c.1
                  have p1396_1 := h1396c.2.1
                  have p1396_2 := h1396c.2.2.1
                  have p1396_3 := h1396c.2.2.2
                  linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1396_1]
                · have p1396_0 := h1396c.1
                  have p1396_1 := h1396c.2.1
                  have p1396_2 := h1396c.2.2.1
                  have p1396_3 := h1396c.2.2.2
                  linarith only [h1367, h1369, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1396_1, u3ehi2]
                · have p1396_0 := h1396c.1
                  have p1396_1 := h1396c.2.1
                  have p1396_2 := h1396c.2.2.1
                  have p1396_3 := h1396c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p1396_1]
                · have p1396_0 := h1396c.1
                  have p1396_1 := h1396c.2.1
                  have p1396_2 := h1396c.2.2.1
                  have p1396_3 := h1396c.2.2.2
                  linarith only [hlam, p1396_0]
                · have p1396_0 := h1396c.1
                  have p1396_1 := h1396c.2.1
                  have p1396_2 := h1396c.2.2.1
                  have p1396_3 := h1396c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1396_1, u3ehi0]
                · have p1396_0 := h1396c.1
                  have p1396_1 := h1396c.2.1
                  have p1396_2 := h1396c.2.2.1
                  have p1396_3 := h1396c.2.2.2
                  linarith only [h0, h1366, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1396_1, u3ehi3]
                · have p1396_0 := h1396c.1
                  have p1396_1 := h1396c.2.1
                  have p1396_2 := h1396c.2.2.1
                  have p1396_3 := h1396c.2.2.2
                  linarith only [h0, h1367, h1369, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1396_1, u3ehi2]
                · have p1396_0 := h1396c.1
                  have p1396_1 := h1396c.2.1
                  have p1396_2 := h1396c.2.2.1
                  have p1396_3 := h1396c.2.2.2
                  linarith only [h1362, h1367, h1369, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1396_1, u3ehi2]
                · have p1396_0 := h1396c.1
                  have p1396_1 := h1396c.2.1
                  have p1396_2 := h1396c.2.2.1
                  have p1396_3 := h1396c.2.2.2
                  linarith only [h1363, hlam, p1396_1]
                · have p1396_0 := h1396c.1
                  have p1396_1 := h1396c.2.1
                  have p1396_2 := h1396c.2.2.1
                  have p1396_3 := h1396c.2.2.2
                  linarith only [hlam, p1396_0]
                · have p1396_0 := h1396c.1
                  have p1396_1 := h1396c.2.1
                  have p1396_2 := h1396c.2.2.1
                  have p1396_3 := h1396c.2.2.2
                  linarith only [h0, h1363, h1366, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1396_1, u3ehi3]
                · have p1396_0 := h1396c.1
                  have p1396_1 := h1396c.2.1
                  have p1396_2 := h1396c.2.2.1
                  have p1396_3 := h1396c.2.2.2
                  linarith only [h0, h1363, h1367, h1369, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1396_1, u3ehi2]
                · have p1396_0 := h1396c.1
                  have p1396_1 := h1396c.2.1
                  have p1396_2 := h1396c.2.2.1
                  have p1396_3 := h1396c.2.2.2
                  linarith only [h1362, h1367, h1369, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1396_1, u3ehi2]
                · have p1396_0 := h1396c.1
                  have p1396_1 := h1396c.2.1
                  have p1396_2 := h1396c.2.2.1
                  have p1396_3 := h1396c.2.2.2
                  linarith only [h1364, hlam, p1396_0]
                · have p1396_0 := h1396c.1
                  have p1396_1 := h1396c.2.1
                  have p1396_2 := h1396c.2.2.1
                  have p1396_3 := h1396c.2.2.2
                  linarith only [h1366, hlam, p1396_0]
                · have p1396_0 := h1396c.1
                  have p1396_1 := h1396c.2.1
                  have p1396_2 := h1396c.2.2.1
                  have p1396_3 := h1396c.2.2.2
                  linarith only [hlam, p1396_0]
                · have p1396_0 := h1396c.1
                  have p1396_1 := h1396c.2.1
                  have p1396_2 := h1396c.2.2.1
                  have p1396_3 := h1396c.2.2.2
                  linarith only [h0, h1363, h1366, h1367, h1369, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1396_1, u3ehi2]
                · have p1396_0 := h1396c.1
                  have p1396_1 := h1396c.2.1
                  have p1396_2 := h1396c.2.2.1
                  have p1396_3 := h1396c.2.2.2
                  linarith only [h1362, hlam, p1396_0]
                · have p1396_0 := h1396c.1
                  have p1396_1 := h1396c.2.1
                  have p1396_2 := h1396c.2.2.1
                  have p1396_3 := h1396c.2.2.2
                  linarith only [h1365, hlam, p1396_1]
                · have p1396_0 := h1396c.1
                  have p1396_1 := h1396c.2.1
                  have p1396_2 := h1396c.2.2.1
                  have p1396_3 := h1396c.2.2.2
                  linarith only [h1367, hlam, p1396_0]
                · have p1396_0 := h1396c.1
                  have p1396_1 := h1396c.2.1
                  have p1396_2 := h1396c.2.2.1
                  have p1396_3 := h1396c.2.2.2
                  linarith only [h1368, hlam, p1396_1]
                · have p1396_0 := h1396c.1
                  have p1396_1 := h1396c.2.1
                  have p1396_2 := h1396c.2.2.1
                  have p1396_3 := h1396c.2.2.2
                  linarith only [hlam, p1396_0]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1422 | h1422
              · rcases h0bigk with h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c
                · have p1423_0 := h1423c.1
                  have p1423_1 := h1423c.2.1
                  have p1423_2 := h1423c.2.2.1
                  have p1423_3 := h1423c.2.2.2
                  linarith only [hlam, p1423_0]
                · have p1423_0 := h1423c.1
                  have p1423_1 := h1423c.2.1
                  have p1423_2 := h1423c.2.2.1
                  have p1423_3 := h1423c.2.2.2
                  linarith only [h0, hlam, p1423_1]
                · have p1423_0 := h1423c.1
                  have p1423_1 := h1423c.2.1
                  have p1423_2 := h1423c.2.2.1
                  have p1423_3 := h1423c.2.2.2
                  linarith only [h1078, hlam, p1423_0]
                · have p1423_0 := h1423c.1
                  have p1423_1 := h1423c.2.1
                  have p1423_2 := h1423c.2.2.1
                  have p1423_3 := h1423c.2.2.2
                  linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1423_1]
                · have p1423_0 := h1423c.1
                  have p1423_1 := h1423c.2.1
                  have p1423_2 := h1423c.2.2.1
                  have p1423_3 := h1423c.2.2.2
                  linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1423_1]
                · have p1423_0 := h1423c.1
                  have p1423_1 := h1423c.2.1
                  have p1423_2 := h1423c.2.2.1
                  have p1423_3 := h1423c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p1423_1]
                · have p1423_0 := h1423c.1
                  have p1423_1 := h1423c.2.1
                  have p1423_2 := h1423c.2.2.1
                  have p1423_3 := h1423c.2.2.2
                  linarith only [hlam, p1423_0]
                · have p1423_0 := h1423c.1
                  have p1423_1 := h1423c.2.1
                  have p1423_2 := h1423c.2.2.1
                  have p1423_3 := h1423c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1423_1, u3ehi0]
                · have p1423_0 := h1423c.1
                  have p1423_1 := h1423c.2.1
                  have p1423_2 := h1423c.2.2.1
                  have p1423_3 := h1423c.2.2.2
                  linarith only [h0, h1366, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1423_1, u3ehi3]
                · have p1423_0 := h1423c.1
                  have p1423_1 := h1423c.2.1
                  have p1423_2 := h1423c.2.2.1
                  have p1423_3 := h1423c.2.2.2
                  linarith only [h0, h1365, h1422, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1423_1, u3ehi4]
                · have p1423_0 := h1423c.1
                  have p1423_1 := h1423c.2.1
                  have p1423_2 := h1423c.2.2.1
                  have p1423_3 := h1423c.2.2.2
                  linarith only [h1078, hc01, hc13, hlam, hphi, p1423_1]
                · have p1423_0 := h1423c.1
                  have p1423_1 := h1423c.2.1
                  have p1423_2 := h1423c.2.2.1
                  have p1423_3 := h1423c.2.2.2
                  linarith only [h1363, hlam, p1423_1]
                · have p1423_0 := h1423c.1
                  have p1423_1 := h1423c.2.1
                  have p1423_2 := h1423c.2.2.1
                  have p1423_3 := h1423c.2.2.2
                  linarith only [hlam, p1423_0]
                · have p1423_0 := h1423c.1
                  have p1423_1 := h1423c.2.1
                  have p1423_2 := h1423c.2.2.1
                  have p1423_3 := h1423c.2.2.2
                  linarith only [h0, h1363, h1366, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1423_1, u3ehi3]
                · have p1423_0 := h1423c.1
                  have p1423_1 := h1423c.2.1
                  have p1423_2 := h1423c.2.2.1
                  have p1423_3 := h1423c.2.2.2
                  linarith only [h0, h1363, h1365, h1422, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1423_1, u3ehi4]
                · have p1423_0 := h1423c.1
                  have p1423_1 := h1423c.2.1
                  have p1423_2 := h1423c.2.2.1
                  have p1423_3 := h1423c.2.2.2
                  linarith only [h1362, h1365, h1422, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1423_1, u3ehi4]
                · have p1423_0 := h1423c.1
                  have p1423_1 := h1423c.2.1
                  have p1423_2 := h1423c.2.2.1
                  have p1423_3 := h1423c.2.2.2
                  linarith only [h1364, hlam, p1423_0]
                · have p1423_0 := h1423c.1
                  have p1423_1 := h1423c.2.1
                  have p1423_2 := h1423c.2.2.1
                  have p1423_3 := h1423c.2.2.2
                  linarith only [h1366, hlam, p1423_0]
                · have p1423_0 := h1423c.1
                  have p1423_1 := h1423c.2.1
                  have p1423_2 := h1423c.2.2.1
                  have p1423_3 := h1423c.2.2.2
                  linarith only [hlam, p1423_0]
                · have p1423_0 := h1423c.1
                  have p1423_1 := h1423c.2.1
                  have p1423_2 := h1423c.2.2.1
                  have p1423_3 := h1423c.2.2.2
                  linarith only [h1368, hlam, p1423_0]
                · have p1423_0 := h1423c.1
                  have p1423_1 := h1423c.2.1
                  have p1423_2 := h1423c.2.2.1
                  have p1423_3 := h1423c.2.2.2
                  linarith only [h1362, hlam, p1423_0]
                · have p1423_0 := h1423c.1
                  have p1423_1 := h1423c.2.1
                  have p1423_2 := h1423c.2.2.1
                  have p1423_3 := h1423c.2.2.2
                  linarith only [h1365, hlam, p1423_1]
                · have p1423_0 := h1423c.1
                  have p1423_1 := h1423c.2.1
                  have p1423_2 := h1423c.2.2.1
                  have p1423_3 := h1423c.2.2.2
                  linarith only [h1367, hlam, p1423_0]
                · have p1423_0 := h1423c.1
                  have p1423_1 := h1423c.2.1
                  have p1423_2 := h1423c.2.2.1
                  have p1423_3 := h1423c.2.2.2
                  linarith only [h0, h1362, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1423_1]
                · have p1423_0 := h1423c.1
                  have p1423_1 := h1423c.2.1
                  have p1423_2 := h1423c.2.2.1
                  have p1423_3 := h1423c.2.2.2
                  linarith only [hlam, p1423_0]
              · rcases h0bigk with h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c | h1449c
                · have p1449_0 := h1449c.1
                  have p1449_1 := h1449c.2.1
                  have p1449_2 := h1449c.2.2.1
                  have p1449_3 := h1449c.2.2.2
                  linarith only [hlam, p1449_0]
                · have p1449_0 := h1449c.1
                  have p1449_1 := h1449c.2.1
                  have p1449_2 := h1449c.2.2.1
                  have p1449_3 := h1449c.2.2.2
                  linarith only [h0, hlam, p1449_1]
                · have p1449_0 := h1449c.1
                  have p1449_1 := h1449c.2.1
                  have p1449_2 := h1449c.2.2.1
                  have p1449_3 := h1449c.2.2.2
                  linarith only [h1078, hlam, p1449_0]
                · have p1449_0 := h1449c.1
                  have p1449_1 := h1449c.2.1
                  have p1449_2 := h1449c.2.2.1
                  have p1449_3 := h1449c.2.2.2
                  linarith only [h0, h1366, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1449_1, u3ehi3]
                · have p1449_0 := h1449c.1
                  have p1449_1 := h1449c.2.1
                  have p1449_2 := h1449c.2.2.1
                  have p1449_3 := h1449c.2.2.2
                  linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1449_1]
                · have p1449_0 := h1449c.1
                  have p1449_1 := h1449c.2.1
                  have p1449_2 := h1449c.2.2.1
                  have p1449_3 := h1449c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p1449_1]
                · have p1449_0 := h1449c.1
                  have p1449_1 := h1449c.2.1
                  have p1449_2 := h1449c.2.2.1
                  have p1449_3 := h1449c.2.2.2
                  linarith only [hlam, p1449_0]
                · have p1449_0 := h1449c.1
                  have p1449_1 := h1449c.2.1
                  have p1449_2 := h1449c.2.2.1
                  have p1449_3 := h1449c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1449_1, u3ehi0]
                · have p1449_0 := h1449c.1
                  have p1449_1 := h1449c.2.1
                  have p1449_2 := h1449c.2.2.1
                  have p1449_3 := h1449c.2.2.2
                  linarith only [h0, h1366, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1449_1, u3ehi3]
                · have p1449_0 := h1449c.1
                  have p1449_1 := h1449c.2.1
                  have p1449_2 := h1449c.2.2.1
                  have p1449_3 := h1449c.2.2.2
                  linarith only [h0, h1367, h1422, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1449_1, u3ehi2]
                · have p1449_0 := h1449c.1
                  have p1449_1 := h1449c.2.1
                  have p1449_2 := h1449c.2.2.1
                  have p1449_3 := h1449c.2.2.2
                  linarith only [h1362, h1367, h1422, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1449_1, u3ehi2]
                · have p1449_0 := h1449c.1
                  have p1449_1 := h1449c.2.1
                  have p1449_2 := h1449c.2.2.1
                  have p1449_3 := h1449c.2.2.2
                  linarith only [h1363, hlam, p1449_1]
                · have p1449_0 := h1449c.1
                  have p1449_1 := h1449c.2.1
                  have p1449_2 := h1449c.2.2.1
                  have p1449_3 := h1449c.2.2.2
                  linarith only [hlam, p1449_0]
                · have p1449_0 := h1449c.1
                  have p1449_1 := h1449c.2.1
                  have p1449_2 := h1449c.2.2.1
                  have p1449_3 := h1449c.2.2.2
                  linarith only [h0, h1363, h1366, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1449_1, u3ehi3]
                · have p1449_0 := h1449c.1
                  have p1449_1 := h1449c.2.1
                  have p1449_2 := h1449c.2.2.1
                  have p1449_3 := h1449c.2.2.2
                  linarith only [h0, h1363, h1367, h1422, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1449_1, u3ehi2]
                · have p1449_0 := h1449c.1
                  have p1449_1 := h1449c.2.1
                  have p1449_2 := h1449c.2.2.1
                  have p1449_3 := h1449c.2.2.2
                  linarith only [h1362, h1367, h1422, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1449_1, u3ehi2]
                · have p1449_0 := h1449c.1
                  have p1449_1 := h1449c.2.1
                  have p1449_2 := h1449c.2.2.1
                  have p1449_3 := h1449c.2.2.2
                  linarith only [h1364, hlam, p1449_0]
                · have p1449_0 := h1449c.1
                  have p1449_1 := h1449c.2.1
                  have p1449_2 := h1449c.2.2.1
                  have p1449_3 := h1449c.2.2.2
                  linarith only [h1366, hlam, p1449_0]
                · have p1449_0 := h1449c.1
                  have p1449_1 := h1449c.2.1
                  have p1449_2 := h1449c.2.2.1
                  have p1449_3 := h1449c.2.2.2
                  linarith only [hlam, p1449_0]
                · have p1449_0 := h1449c.1
                  have p1449_1 := h1449c.2.1
                  have p1449_2 := h1449c.2.2.1
                  have p1449_3 := h1449c.2.2.2
                  linarith only [h1368, hlam, p1449_0]
                · have p1449_0 := h1449c.1
                  have p1449_1 := h1449c.2.1
                  have p1449_2 := h1449c.2.2.1
                  have p1449_3 := h1449c.2.2.2
                  linarith only [h1362, hlam, p1449_0]
                · have p1449_0 := h1449c.1
                  have p1449_1 := h1449c.2.1
                  have p1449_2 := h1449c.2.2.1
                  have p1449_3 := h1449c.2.2.2
                  linarith only [h1365, hlam, p1449_1]
                · have p1449_0 := h1449c.1
                  have p1449_1 := h1449c.2.1
                  have p1449_2 := h1449c.2.2.1
                  have p1449_3 := h1449c.2.2.2
                  linarith only [h1367, hlam, p1449_0]
                · have p1449_0 := h1449c.1
                  have p1449_1 := h1449c.2.1
                  have p1449_2 := h1449c.2.2.1
                  have p1449_3 := h1449c.2.2.2
                  linarith only [h0, h1362, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1449_1]
                · have p1449_0 := h1449c.1
                  have p1449_1 := h1449c.2.1
                  have p1449_2 := h1449c.2.2.1
                  have p1449_3 := h1449c.2.2.2
                  linarith only [hlam, p1449_0]
          · linarith only [h1366, h1367, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1476 | h1476
          · linarith only [h1366, h1476, hc34, hlam, hphi, u3ehi4]
          · linarith only [h1078, h1362, h1476, hlam]
      · linarith only [h0, h1362, h1365, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1480 | h1480
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1481 | h1481
        · linarith only [h1363, h1364, h1481, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1483 | h1483
          · linarith only [h1481, h1483, hc34, hlam, hphi, u3ehi4]
          · linarith only [h1078, h1362, h1483, hlam]
      · linarith only [h1078, h1362, h1363, h1480, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1487 | h1487
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1488 | h1488
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1489 | h1489
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1490 | h1490
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1491 | h1491
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1492 | h1492
              · rcases h0bigk with h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c | h1493c
                · have p1493_0 := h1493c.1
                  have p1493_1 := h1493c.2.1
                  have p1493_2 := h1493c.2.2.1
                  have p1493_3 := h1493c.2.2.2
                  linarith only [hlam, p1493_0]
                · have p1493_0 := h1493c.1
                  have p1493_1 := h1493c.2.1
                  have p1493_2 := h1493c.2.2.1
                  have p1493_3 := h1493c.2.2.2
                  linarith only [h0, hlam, p1493_1]
                · have p1493_0 := h1493c.1
                  have p1493_1 := h1493c.2.1
                  have p1493_2 := h1493c.2.2.1
                  have p1493_3 := h1493c.2.2.2
                  linarith only [h1078, hlam, p1493_0]
                · have p1493_0 := h1493c.1
                  have p1493_1 := h1493c.2.1
                  have p1493_2 := h1493c.2.2.1
                  have p1493_3 := h1493c.2.2.2
                  linarith only [h1491, hc01, hc45, hlam, hphi, ht0b, ht5b, p1493_1]
                · have p1493_0 := h1493c.1
                  have p1493_1 := h1493c.2.1
                  have p1493_2 := h1493c.2.2.1
                  have p1493_3 := h1493c.2.2.2
                  linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1493_1]
                · have p1493_0 := h1493c.1
                  have p1493_1 := h1493c.2.1
                  have p1493_2 := h1493c.2.2.1
                  have p1493_3 := h1493c.2.2.2
                  linarith only [h1363, hc01, hc23, hlam, hphi, ht12, p1493_1]
                · have p1493_0 := h1493c.1
                  have p1493_1 := h1493c.2.1
                  have p1493_2 := h1493c.2.2.1
                  have p1493_3 := h1493c.2.2.2
                  linarith only [hlam, p1493_0]
                · have p1493_0 := h1493c.1
                  have p1493_1 := h1493c.2.1
                  have p1493_2 := h1493c.2.2.1
                  have p1493_3 := h1493c.2.2.2
                  linarith only [h1363, hlam, p1493_0]
                · have p1493_0 := h1493c.1
                  have p1493_1 := h1493c.2.1
                  have p1493_2 := h1493c.2.2.1
                  have p1493_3 := h1493c.2.2.2
                  linarith only [h1363, h1491, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1493_1]
                · have p1493_0 := h1493c.1
                  have p1493_1 := h1493c.2.1
                  have p1493_2 := h1493c.2.2.1
                  have p1493_3 := h1493c.2.2.2
                  linarith only [h1362, h1363, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1493_1]
                · have p1493_0 := h1493c.1
                  have p1493_1 := h1493c.2.1
                  have p1493_2 := h1493c.2.2.1
                  have p1493_3 := h1493c.2.2.2
                  linarith only [h1362, hc03, hc15, hlam, hphi, ht0b, ht5b, p1493_1]
                · have p1493_0 := h1493c.1
                  have p1493_1 := h1493c.2.1
                  have p1493_2 := h1493c.2.2.1
                  have p1493_3 := h1493c.2.2.2
                  linarith only [h1363, hc02, hc23, hlam, hphi, p1493_1]
                · have p1493_0 := h1493c.1
                  have p1493_1 := h1493c.2.1
                  have p1493_2 := h1493c.2.2.1
                  have p1493_3 := h1493c.2.2.2
                  linarith only [hlam, p1493_0]
                · have p1493_0 := h1493c.1
                  have p1493_1 := h1493c.2.1
                  have p1493_2 := h1493c.2.2.1
                  have p1493_3 := h1493c.2.2.2
                  linarith only [h1363, h1491, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1493_1]
                · have p1493_0 := h1493c.1
                  have p1493_1 := h1493c.2.1
                  have p1493_2 := h1493c.2.2.1
                  have p1493_3 := h1493c.2.2.2
                  linarith only [h1363, h1488, h1492, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1493_1, u3ehi4]
                · have p1493_0 := h1493c.1
                  have p1493_1 := h1493c.2.1
                  have p1493_2 := h1493c.2.2.1
                  have p1493_3 := h1493c.2.2.2
                  linarith only [h1362, h1488, h1492, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1493_1, u3ehi4]
                · have p1493_0 := h1493c.1
                  have p1493_1 := h1493c.2.1
                  have p1493_2 := h1493c.2.2.1
                  have p1493_3 := h1493c.2.2.2
                  linarith only [h1487, hlam, p1493_0]
                · have p1493_0 := h1493c.1
                  have p1493_1 := h1493c.2.1
                  have p1493_2 := h1493c.2.2.1
                  have p1493_3 := h1493c.2.2.2
                  linarith only [h1489, hlam, p1493_0]
                · have p1493_0 := h1493c.1
                  have p1493_1 := h1493c.2.1
                  have p1493_2 := h1493c.2.2.1
                  have p1493_3 := h1493c.2.2.2
                  linarith only [hlam, p1493_0]
                · have p1493_0 := h1493c.1
                  have p1493_1 := h1493c.2.1
                  have p1493_2 := h1493c.2.2.1
                  have p1493_3 := h1493c.2.2.2
                  linarith only [h1487, h1488, h1492, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1493_1, u3ehi4]
                · have p1493_0 := h1493c.1
                  have p1493_1 := h1493c.2.1
                  have p1493_2 := h1493c.2.2.1
                  have p1493_3 := h1493c.2.2.2
                  linarith only [h1362, hlam, p1493_0]
                · have p1493_0 := h1493c.1
                  have p1493_1 := h1493c.2.1
                  have p1493_2 := h1493c.2.2.1
                  have p1493_3 := h1493c.2.2.2
                  linarith only [h1488, hlam, p1493_1]
                · have p1493_0 := h1493c.1
                  have p1493_1 := h1493c.2.1
                  have p1493_2 := h1493c.2.2.1
                  have p1493_3 := h1493c.2.2.2
                  linarith only [h1490, hlam, p1493_0]
                · have p1493_0 := h1493c.1
                  have p1493_1 := h1493c.2.1
                  have p1493_2 := h1493c.2.2.1
                  have p1493_3 := h1493c.2.2.2
                  linarith only [h1491, hlam, p1493_1]
                · have p1493_0 := h1493c.1
                  have p1493_1 := h1493c.2.1
                  have p1493_2 := h1493c.2.2.1
                  have p1493_3 := h1493c.2.2.2
                  linarith only [hlam, p1493_0]
              · linarith only [h1363, h1489, h1492, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1520 | h1520
              · rcases h0bigk with h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c | h1521c
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [hlam, p1521_0]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h0, hlam, p1521_1]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h1078, hlam, p1521_0]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h1489, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1521_1, u3ehi3]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h1489, h1491, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1521_1, u3ehi3]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h1363, hc01, hc23, hlam, hphi, ht12, p1521_1]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [hlam, p1521_0]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h1363, hlam, p1521_0]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h1363, h1489, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1521_1, u3ehi3]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h1363, h1489, h1491, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1521_1, u3ehi3]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h1362, h1363, h1489, h1491, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1521_1, u3ehi3]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h1363, hc02, hc23, hlam, hphi, p1521_1]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [hlam, p1521_0]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h1363, h1489, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1521_1, u3ehi3]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h1363, h1489, h1491, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1521_1, u3ehi3]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h1362, h1491, hlam, p1521_1]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h1487, hlam, p1521_0]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h1489, hlam, p1521_0]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [hlam, p1521_0]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h1491, hlam, p1521_0]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h1362, hlam, p1521_0]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h1488, hlam, p1521_1]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h1490, hlam, p1521_0]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [h1362, h1489, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1521_1, u3ehi3]
                · have p1521_0 := h1521c.1
                  have p1521_1 := h1521c.2.1
                  have p1521_2 := h1521c.2.2.1
                  have p1521_3 := h1521c.2.2.2
                  linarith only [hlam, p1521_0]
              · linarith only [h1363, h1487, h1489, h1520, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1489, h1490, hc35, hlam, hphi, u3ehi3]
        · linarith only [h1363, h1487, h1489, hlam]
      · linarith only [h0, h1362, h1488, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1551 | h1551
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1552 | h1552
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1553 | h1553
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1554 | h1554
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1555 | h1555
              · rcases h0bigk with h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c | h1556c
                · have p1556_0 := h1556c.1
                  have p1556_1 := h1556c.2.1
                  have p1556_2 := h1556c.2.2.1
                  have p1556_3 := h1556c.2.2.2
                  linarith only [hlam, p1556_0]
                · have p1556_0 := h1556c.1
                  have p1556_1 := h1556c.2.1
                  have p1556_2 := h1556c.2.2.1
                  have p1556_3 := h1556c.2.2.2
                  linarith only [h0, hlam, p1556_1]
                · have p1556_0 := h1556c.1
                  have p1556_1 := h1556c.2.1
                  have p1556_2 := h1556c.2.2.1
                  have p1556_3 := h1556c.2.2.2
                  linarith only [h1078, hlam, p1556_0]
                · have p1556_0 := h1556c.1
                  have p1556_1 := h1556c.2.1
                  have p1556_2 := h1556c.2.2.1
                  have p1556_3 := h1556c.2.2.2
                  linarith only [h0, h1487, hlam, p1556_1]
                · have p1556_0 := h1556c.1
                  have p1556_1 := h1556c.2.1
                  have p1556_2 := h1556c.2.2.1
                  have p1556_3 := h1556c.2.2.2
                  linarith only [h0, h1363, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1556_1]
                · have p1556_0 := h1556c.1
                  have p1556_1 := h1556c.2.1
                  have p1556_2 := h1556c.2.2.1
                  have p1556_3 := h1556c.2.2.2
                  linarith only [h1363, hc01, hc23, hlam, hphi, ht12, p1556_1]
                · have p1556_0 := h1556c.1
                  have p1556_1 := h1556c.2.1
                  have p1556_2 := h1556c.2.2.1
                  have p1556_3 := h1556c.2.2.2
                  linarith only [hlam, p1556_0]
                · have p1556_0 := h1556c.1
                  have p1556_1 := h1556c.2.1
                  have p1556_2 := h1556c.2.2.1
                  have p1556_3 := h1556c.2.2.2
                  linarith only [h1363, hlam, p1556_0]
                · have p1556_0 := h1556c.1
                  have p1556_1 := h1556c.2.1
                  have p1556_2 := h1556c.2.2.1
                  have p1556_3 := h1556c.2.2.2
                  linarith only [h1487, hlam, p1556_1]
                · have p1556_0 := h1556c.1
                  have p1556_1 := h1556c.2.1
                  have p1556_2 := h1556c.2.2.1
                  have p1556_3 := h1556c.2.2.2
                  linarith only [h1362, h1363, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1556_1]
                · have p1556_0 := h1556c.1
                  have p1556_1 := h1556c.2.1
                  have p1556_2 := h1556c.2.2.1
                  have p1556_3 := h1556c.2.2.2
                  linarith only [h1362, hc03, hc15, hlam, hphi, ht0b, ht5b, p1556_1]
                · have p1556_0 := h1556c.1
                  have p1556_1 := h1556c.2.1
                  have p1556_2 := h1556c.2.2.1
                  have p1556_3 := h1556c.2.2.2
                  linarith only [h1363, h1551, h1555, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1556_1, u3ehi4]
                · have p1556_0 := h1556c.1
                  have p1556_1 := h1556c.2.1
                  have p1556_2 := h1556c.2.2.1
                  have p1556_3 := h1556c.2.2.2
                  linarith only [hlam, p1556_0]
                · have p1556_0 := h1556c.1
                  have p1556_1 := h1556c.2.1
                  have p1556_2 := h1556c.2.2.1
                  have p1556_3 := h1556c.2.2.2
                  linarith only [h1363, h1487, h1551, h1555, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1556_1, u3ehi4]
                · have p1556_0 := h1556c.1
                  have p1556_1 := h1556c.2.1
                  have p1556_2 := h1556c.2.2.1
                  have p1556_3 := h1556c.2.2.2
                  linarith only [h1363, h1551, h1555, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1556_1, u3ehi4]
                · have p1556_0 := h1556c.1
                  have p1556_1 := h1556c.2.1
                  have p1556_2 := h1556c.2.2.1
                  have p1556_3 := h1556c.2.2.2
                  linarith only [h1362, h1551, h1555, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1556_1, u3ehi4]
                · have p1556_0 := h1556c.1
                  have p1556_1 := h1556c.2.1
                  have p1556_2 := h1556c.2.2.1
                  have p1556_3 := h1556c.2.2.2
                  linarith only [h1551, h1555, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1556_1, u3ehi4]
                · have p1556_0 := h1556c.1
                  have p1556_1 := h1556c.2.1
                  have p1556_2 := h1556c.2.2.1
                  have p1556_3 := h1556c.2.2.2
                  linarith only [h1552, hlam, p1556_0]
                · have p1556_0 := h1556c.1
                  have p1556_1 := h1556c.2.1
                  have p1556_2 := h1556c.2.2.1
                  have p1556_3 := h1556c.2.2.2
                  linarith only [hlam, p1556_0]
                · have p1556_0 := h1556c.1
                  have p1556_1 := h1556c.2.1
                  have p1556_2 := h1556c.2.2.1
                  have p1556_3 := h1556c.2.2.2
                  linarith only [h1363, h1551, h1552, h1555, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1556_1, u3ehi4]
                · have p1556_0 := h1556c.1
                  have p1556_1 := h1556c.2.1
                  have p1556_2 := h1556c.2.2.1
                  have p1556_3 := h1556c.2.2.2
                  linarith only [h1362, hlam, p1556_0]
                · have p1556_0 := h1556c.1
                  have p1556_1 := h1556c.2.1
                  have p1556_2 := h1556c.2.2.1
                  have p1556_3 := h1556c.2.2.2
                  linarith only [h1551, hlam, p1556_1]
                · have p1556_0 := h1556c.1
                  have p1556_1 := h1556c.2.1
                  have p1556_2 := h1556c.2.2.1
                  have p1556_3 := h1556c.2.2.2
                  linarith only [h1553, hlam, p1556_0]
                · have p1556_0 := h1556c.1
                  have p1556_1 := h1556c.2.1
                  have p1556_2 := h1556c.2.2.1
                  have p1556_3 := h1556c.2.2.2
                  linarith only [h1554, hlam, p1556_1]
                · have p1556_0 := h1556c.1
                  have p1556_1 := h1556c.2.1
                  have p1556_2 := h1556c.2.2.1
                  have p1556_3 := h1556c.2.2.2
                  linarith only [hlam, p1556_0]
              · linarith only [h1363, h1552, h1555, hc35, hlam, hphi, u3ehi3]
            · linarith only [h0, h1362, h1487, h1554, hlam]
          · linarith only [h1552, h1553, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1585 | h1585
          · linarith only [h1552, h1585, hc34, hlam, hphi, u3ehi4]
          · linarith only [h1078, h1362, h1585, hlam]
      · linarith only [h0, h1362, h1551, hlam]

end R2N4
