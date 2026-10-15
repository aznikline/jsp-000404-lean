import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_6S19

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5504000 in
set_option maxHeartbeats 5504000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s15_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg10058 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11024 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg11558 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg11559 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg11560 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h11561 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h11562 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h11563 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h11558 := hg11558
  have h11559 := hg11559
  have h11560 := hg11560
  rcases m.htr 1 2 3 (by decide) (by decide) with h12081 | h12081
  · rcases m.htr 1 2 4 (by decide) (by decide) with h12082 | h12082
    · rcases m.htr 1 2 5 (by decide) (by decide) with h12083 | h12083
      · rcases m.htr 1 3 4 (by decide) (by decide) with h12084 | h12084
        · rcases m.htr 1 4 5 (by decide) (by decide) with h12085 | h12085
          · rcases m.htr 2 3 4 (by decide) (by decide) with h12086 | h12086
            · rcases m.htr 2 3 5 (by decide) (by decide) with h12087 | h12087
              · rcases m.htr 2 4 5 (by decide) (by decide) with h12088 | h12088
                · linarith only [h11558, h11563, h12086, h12088, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h12090 | h12090
                  · linarith only [h11561, h11563, h12090, hlam]
                  · rcases h0bigk with h12092c | h12092c | h12092c | h12092c | h12092c | h12092c | h12092c | h12092c | h12092c | h12092c | h12092c | h12092c | h12092c | h12092c | h12092c | h12092c | h12092c | h12092c | h12092c | h12092c | h12092c | h12092c | h12092c | h12092c | h12092c
                    · have p12092_0 := h12092c.1
                      have p12092_1 := h12092c.2.1
                      have p12092_2 := h12092c.2.2.1
                      have p12092_3 := h12092c.2.2.2
                      linarith only [hlam, p12092_0]
                    · have p12092_0 := h12092c.1
                      have p12092_1 := h12092c.2.1
                      have p12092_2 := h12092c.2.2.1
                      have p12092_3 := h12092c.2.2.2
                      linarith only [h0, hlam, p12092_1]
                    · have p12092_0 := h12092c.1
                      have p12092_1 := h12092c.2.1
                      have p12092_2 := h12092c.2.2.1
                      have p12092_3 := h12092c.2.2.2
                      linarith only [h6793, hlam, p12092_0]
                    · have p12092_0 := h12092c.1
                      have p12092_1 := h12092c.2.1
                      have p12092_2 := h12092c.2.2.1
                      have p12092_3 := h12092c.2.2.2
                      linarith only [h10058, hlam, p12092_1]
                    · have p12092_0 := h12092c.1
                      have p12092_1 := h12092c.2.1
                      have p12092_2 := h12092c.2.2.1
                      have p12092_3 := h12092c.2.2.2
                      linarith only [h11024, hlam, p12092_1]
                    · have p12092_0 := h12092c.1
                      have p12092_1 := h12092c.2.1
                      have p12092_2 := h12092c.2.2.1
                      have p12092_3 := h12092c.2.2.2
                      rcases p12092_3 (m.d 0 1) (by simp) with h12098 | h12098
                      · linarith only [h0, h12098, hlam]
                      · rcases p12092_3 (m.d 0 2) (by simp) with h12100 | h12100
                        · rcases p12092_3 (m.d 0 3) (by simp) with h12101 | h12101
                          · linarith only [h11558, h12101, hlam]
                          · linarith only [h12101, h6793, hlam]
                        · linarith only [h0, h12100, hlam]
                    · have p12092_0 := h12092c.1
                      have p12092_1 := h12092c.2.1
                      have p12092_2 := h12092c.2.2.1
                      have p12092_3 := h12092c.2.2.2
                      linarith only [hlam, p12092_0]
                    · have p12092_0 := h12092c.1
                      have p12092_1 := h12092c.2.1
                      have p12092_2 := h12092c.2.2.1
                      have p12092_3 := h12092c.2.2.2
                      linarith only [h11558, h12087, h12090, hc34, hlam, hphi, ht0b, ht45, ht5b, p12092_1, u0elo1]
                    · have p12092_0 := h12092c.1
                      have p12092_1 := h12092c.2.1
                      have p12092_2 := h12092c.2.2.1
                      have p12092_3 := h12092c.2.2.2
                      rcases p12092_3 (m.d 0 1) (by simp) with h12107 | h12107
                      · linarith only [h0, h12107, hlam]
                      · rcases p12092_3 (m.d 0 2) (by simp) with h12109 | h12109
                        · rcases p12092_3 (m.d 0 3) (by simp) with h12110 | h12110
                          · linarith only [h11558, h12110, hlam]
                          · linarith only [h11561, h12110, hlam]
                        · linarith only [h11559, h12109, hlam]
                    · have p12092_0 := h12092c.1
                      have p12092_1 := h12092c.2.1
                      have p12092_2 := h12092c.2.2.1
                      have p12092_3 := h12092c.2.2.2
                      rcases p12092_3 (m.d 0 1) (by simp) with h12114 | h12114
                      · linarith only [h0, h12114, hlam]
                      · rcases p12092_3 (m.d 0 2) (by simp) with h12116 | h12116
                        · rcases p12092_3 (m.d 0 3) (by simp) with h12117 | h12117
                          · linarith only [h11558, h12117, hlam]
                          · linarith only [h11562, h12117, hlam]
                        · linarith only [h11560, h12116, hlam]
                    · have p12092_0 := h12092c.1
                      have p12092_1 := h12092c.2.1
                      have p12092_2 := h12092c.2.2.1
                      have p12092_3 := h12092c.2.2.2
                      rcases p12092_3 (m.d 0 1) (by simp) with h12121 | h12121
                      · linarith only [h12121, h6793, hlam]
                      · rcases p12092_3 (m.d 0 2) (by simp) with h12123 | h12123
                        · rcases p12092_3 (m.d 0 3) (by simp) with h12124 | h12124
                          · rcases p12092_3 (m.d 0 4) (by simp) with h12125 | h12125
                            · linarith only [h11561, h12125, hlam]
                            · linarith only [h10058, h12125, hlam]
                          · linarith only [h12124, h6793, hlam]
                        · linarith only [h0, h12123, hlam]
                    · have p12092_0 := h12092c.1
                      have p12092_1 := h12092c.2.1
                      have p12092_2 := h12092c.2.2.1
                      have p12092_3 := h12092c.2.2.2
                      linarith only [h11558, hlam, p12092_1]
                    · have p12092_0 := h12092c.1
                      have p12092_1 := h12092c.2.1
                      have p12092_2 := h12092c.2.2.1
                      have p12092_3 := h12092c.2.2.2
                      linarith only [hlam, p12092_0]
                    · have p12092_0 := h12092c.1
                      have p12092_1 := h12092c.2.1
                      have p12092_2 := h12092c.2.2.1
                      have p12092_3 := h12092c.2.2.2
                      rcases p12092_3 (m.d 0 1) (by simp) with h12132 | h12132
                      · linarith only [h12132, h6793, hlam]
                      · rcases p12092_3 (m.d 0 2) (by simp) with h12134 | h12134
                        · rcases p12092_3 (m.d 0 3) (by simp) with h12135 | h12135
                          · rcases p12092_3 (m.d 0 4) (by simp) with h12136 | h12136
                            · linarith only [h11561, h12136, hlam]
                            · rcases p12092_3 (m.d 0 5) (by simp) with h12138 | h12138
                              · linarith only [h11562, h12138, hlam]
                              · linarith only [h11563, h12138, hlam]
                          · linarith only [h11561, h12135, hlam]
                        · linarith only [h11559, h12134, hlam]
                    · have p12092_0 := h12092c.1
                      have p12092_1 := h12092c.2.1
                      have p12092_2 := h12092c.2.2.1
                      have p12092_3 := h12092c.2.2.2
                      rcases p12092_3 (m.d 0 1) (by simp) with h12143 | h12143
                      · linarith only [h12143, h6793, hlam]
                      · rcases p12092_3 (m.d 0 2) (by simp) with h12145 | h12145
                        · rcases p12092_3 (m.d 0 3) (by simp) with h12146 | h12146
                          · rcases p12092_3 (m.d 0 4) (by simp) with h12147 | h12147
                            · linarith only [h11561, h12147, hlam]
                            · rcases p12092_3 (m.d 0 5) (by simp) with h12149 | h12149
                              · linarith only [h11562, h12149, hlam]
                              · rcases h0emin with h12151 | h12151 | h12151 | h12151 | h12151
                                · linarith only [h10058, h11558, h11563, h12151, hlam, p12092_1, u0elo1]
                                · rcases h2bigk with h12153c | h12153c | h12153c | h12153c | h12153c | h12153c | h12153c | h12153c | h12153c | h12153c | h12153c | h12153c | h12153c | h12153c | h12153c | h12153c | h12153c | h12153c | h12153c | h12153c | h12153c | h12153c | h12153c | h12153c | h12153c
                                  · have p12153_0 := h12153c.1
                                    have p12153_1 := h12153c.2.1
                                    have p12153_2 := h12153c.2.2.1
                                    have p12153_3 := h12153c.2.2.2
                                    linarith only [hlam, p12153_0]
                                  · have p12153_0 := h12153c.1
                                    have p12153_1 := h12153c.2.1
                                    have p12153_2 := h12153c.2.2.1
                                    have p12153_3 := h12153c.2.2.2
                                    linarith only [h0, hlam, p12153_1]
                                  · have p12153_0 := h12153c.1
                                    have p12153_1 := h12153c.2.1
                                    have p12153_2 := h12153c.2.2.1
                                    have p12153_3 := h12153c.2.2.2
                                    linarith only [h12087, h12090, hc34, hlam, hphi, ht0b, ht45, ht5b, p12153_1, u0elo1]
                                  · have p12153_0 := h12153c.1
                                    have p12153_1 := h12153c.2.1
                                    have p12153_2 := h12153c.2.2.1
                                    have p12153_3 := h12153c.2.2.2
                                    rcases p12153_3 (m.d 0 2) (by simp) with h12157 | h12157
                                    · rcases p12153_3 (m.d 1 2) (by simp) with h12158 | h12158
                                      · rcases p12153_3 (m.d 2 3) (by simp) with h12159 | h12159
                                        · linarith only [h11558, h12159, hlam]
                                        · linarith only [h12086, h12159, hlam]
                                      · linarith only [h12082, h12158, hlam]
                                    · linarith only [h12157, hlam, p12153_0]
                                  · have p12153_0 := h12153c.1
                                    have p12153_1 := h12153c.2.1
                                    have p12153_2 := h12153c.2.2.1
                                    have p12153_3 := h12153c.2.2.2
                                    rcases p12153_3 (m.d 0 2) (by simp) with h12164 | h12164
                                    · rcases p12153_3 (m.d 1 2) (by simp) with h12165 | h12165
                                      · rcases p12153_3 (m.d 2 3) (by simp) with h12166 | h12166
                                        · linarith only [h11558, h12166, hlam]
                                        · linarith only [h12087, h12166, hlam]
                                      · linarith only [h12083, h12165, hlam]
                                    · linarith only [h12164, hlam, p12153_0]
                                  · have p12153_0 := h12153c.1
                                    have p12153_1 := h12153c.2.1
                                    have p12153_2 := h12153c.2.2.1
                                    have p12153_3 := h12153c.2.2.2
                                    linarith only [h10058, h11558, h11563, hc01, hc12, hlam, hphi, p12092_1, p12153_1]
                                  · have p12153_0 := h12153c.1
                                    have p12153_1 := h12153c.2.1
                                    have p12153_2 := h12153c.2.2.1
                                    have p12153_3 := h12153c.2.2.2
                                    linarith only [hlam, p12153_0]
                                  · have p12153_0 := h12153c.1
                                    have p12153_1 := h12153c.2.1
                                    have p12153_2 := h12153c.2.2.1
                                    have p12153_3 := h12153c.2.2.2
                                    rcases p12153_3 (m.d 0 2) (by simp) with h12173 | h12173
                                    · linarith only [h0, h12173, hlam]
                                    · linarith only [h11558, h12173, hlam]
                                  · have p12153_0 := h12153c.1
                                    have p12153_1 := h12153c.2.1
                                    have p12153_2 := h12153c.2.2.1
                                    have p12153_3 := h12153c.2.2.2
                                    rcases p12153_3 (m.d 0 2) (by simp) with h12176 | h12176
                                    · linarith only [h0, h12176, hlam]
                                    · linarith only [h11559, h12176, hlam]
                                  · have p12153_0 := h12153c.1
                                    have p12153_1 := h12153c.2.1
                                    have p12153_2 := h12153c.2.2.1
                                    have p12153_3 := h12153c.2.2.2
                                    rcases p12153_3 (m.d 0 2) (by simp) with h12179 | h12179
                                    · linarith only [h0, h12179, hlam]
                                    · linarith only [h11560, h12179, hlam]
                                  · have p12153_0 := h12153c.1
                                    have p12153_1 := h12153c.2.1
                                    have p12153_2 := h12153c.2.2.1
                                    have p12153_3 := h12153c.2.2.2
                                    linarith only [h11558, hlam, p12153_0]
                                  · have p12153_0 := h12153c.1
                                    have p12153_1 := h12153c.2.1
                                    have p12153_2 := h12153c.2.2.1
                                    have p12153_3 := h12153c.2.2.2
                                    linarith only [h12081, hlam, p12153_0]
                                  · have p12153_0 := h12153c.1
                                    have p12153_1 := h12153c.2.1
                                    have p12153_2 := h12153c.2.2.1
                                    have p12153_3 := h12153c.2.2.2
                                    linarith only [hlam, p12153_0]
                                  · have p12153_0 := h12153c.1
                                    have p12153_1 := h12153c.2.1
                                    have p12153_2 := h12153c.2.2.1
                                    have p12153_3 := h12153c.2.2.2
                                    linarith only [h11558, hc24, hlam, hphi, ht0b, ht45, ht5b, p12153_1, u0elo1]
                                  · have p12153_0 := h12153c.1
                                    have p12153_1 := h12153c.2.1
                                    have p12153_2 := h12153c.2.2.1
                                    have p12153_3 := h12153c.2.2.2
                                    linarith only [h11558, hc25, hlam, hphi, ht0b, ht5b, p12153_1, u0elo1]
                                  · have p12153_0 := h12153c.1
                                    have p12153_1 := h12153c.2.1
                                    have p12153_2 := h12153c.2.2.1
                                    have p12153_3 := h12153c.2.2.2
                                    linarith only [h11559, hlam, p12153_0]
                                  · have p12153_0 := h12153c.1
                                    have p12153_1 := h12153c.2.1
                                    have p12153_2 := h12153c.2.2.1
                                    have p12153_3 := h12153c.2.2.2
                                    linarith only [h12082, hlam, p12153_0]
                                  · have p12153_0 := h12153c.1
                                    have p12153_1 := h12153c.2.1
                                    have p12153_2 := h12153c.2.2.1
                                    have p12153_3 := h12153c.2.2.2
                                    linarith only [h12086, hlam, p12153_1]
                                  · have p12153_0 := h12153c.1
                                    have p12153_1 := h12153c.2.1
                                    have p12153_2 := h12153c.2.2.1
                                    have p12153_3 := h12153c.2.2.2
                                    linarith only [hlam, p12153_0]
                                  · have p12153_0 := h12153c.1
                                    have p12153_1 := h12153c.2.1
                                    have p12153_2 := h12153c.2.2.1
                                    have p12153_3 := h12153c.2.2.2
                                    linarith only [h12088, hlam, p12153_1]
                                  · have p12153_0 := h12153c.1
                                    have p12153_1 := h12153c.2.1
                                    have p12153_2 := h12153c.2.2.1
                                    have p12153_3 := h12153c.2.2.2
                                    linarith only [h11560, hlam, p12153_0]
                                  · have p12153_0 := h12153c.1
                                    have p12153_1 := h12153c.2.1
                                    have p12153_2 := h12153c.2.2.1
                                    have p12153_3 := h12153c.2.2.2
                                    linarith only [h12083, hlam, p12153_0]
                                  · have p12153_0 := h12153c.1
                                    have p12153_1 := h12153c.2.1
                                    have p12153_2 := h12153c.2.2.1
                                    have p12153_3 := h12153c.2.2.2
                                    linarith only [h12087, hlam, p12153_1]
                                  · have p12153_0 := h12153c.1
                                    have p12153_1 := h12153c.2.1
                                    have p12153_2 := h12153c.2.2.1
                                    have p12153_3 := h12153c.2.2.2
                                    linarith only [h11560, h12086, hc34, hlam, hphi, ht0b, ht45, ht5b, p12153_1, u0elo1]
                                  · have p12153_0 := h12153c.1
                                    have p12153_1 := h12153c.2.1
                                    have p12153_2 := h12153c.2.2.1
                                    have p12153_3 := h12153c.2.2.2
                                    linarith only [hlam, p12153_0]
                                · rcases h2bigk with h12197c | h12197c | h12197c | h12197c | h12197c | h12197c | h12197c | h12197c | h12197c | h12197c | h12197c | h12197c | h12197c | h12197c | h12197c | h12197c | h12197c | h12197c | h12197c | h12197c | h12197c | h12197c | h12197c | h12197c | h12197c
                                  · have p12197_0 := h12197c.1
                                    have p12197_1 := h12197c.2.1
                                    have p12197_2 := h12197c.2.2.1
                                    have p12197_3 := h12197c.2.2.2
                                    linarith only [hlam, p12197_0]
                                  · have p12197_0 := h12197c.1
                                    have p12197_1 := h12197c.2.1
                                    have p12197_2 := h12197c.2.2.1
                                    have p12197_3 := h12197c.2.2.2
                                    linarith only [h0, hlam, p12197_1]
                                  · have p12197_0 := h12197c.1
                                    have p12197_1 := h12197c.2.1
                                    have p12197_2 := h12197c.2.2.1
                                    have p12197_3 := h12197c.2.2.2
                                    linarith only [h12086, hc34, hlam, hphi, ht0b, ht45, ht5b, p12197_1, u0elo1]
                                  · have p12197_0 := h12197c.1
                                    have p12197_1 := h12197c.2.1
                                    have p12197_2 := h12197c.2.2.1
                                    have p12197_3 := h12197c.2.2.2
                                    rcases p12197_3 (m.d 0 2) (by simp) with h12201 | h12201
                                    · rcases p12197_3 (m.d 1 2) (by simp) with h12202 | h12202
                                      · rcases p12197_3 (m.d 2 3) (by simp) with h12203 | h12203
                                        · linarith only [h11558, h12203, hlam]
                                        · linarith only [h12086, h12203, hlam]
                                      · linarith only [h12082, h12202, hlam]
                                    · linarith only [h12201, hlam, p12197_0]
                                  · have p12197_0 := h12197c.1
                                    have p12197_1 := h12197c.2.1
                                    have p12197_2 := h12197c.2.2.1
                                    have p12197_3 := h12197c.2.2.2
                                    rcases p12197_3 (m.d 0 2) (by simp) with h12208 | h12208
                                    · rcases p12197_3 (m.d 1 2) (by simp) with h12209 | h12209
                                      · rcases p12197_3 (m.d 2 3) (by simp) with h12210 | h12210
                                        · linarith only [h11558, h12210, hlam]
                                        · linarith only [h12087, h12210, hlam]
                                      · linarith only [h12083, h12209, hlam]
                                    · linarith only [h12208, hlam, p12197_0]
                                  · have p12197_0 := h12197c.1
                                    have p12197_1 := h12197c.2.1
                                    have p12197_2 := h12197c.2.2.1
                                    have p12197_3 := h12197c.2.2.2
                                    linarith only [h10058, h11558, h11563, hc01, hc12, hlam, hphi, p12092_1, p12197_1]
                                  · have p12197_0 := h12197c.1
                                    have p12197_1 := h12197c.2.1
                                    have p12197_2 := h12197c.2.2.1
                                    have p12197_3 := h12197c.2.2.2
                                    linarith only [hlam, p12197_0]
                                  · have p12197_0 := h12197c.1
                                    have p12197_1 := h12197c.2.1
                                    have p12197_2 := h12197c.2.2.1
                                    have p12197_3 := h12197c.2.2.2
                                    rcases p12197_3 (m.d 0 2) (by simp) with h12217 | h12217
                                    · linarith only [h0, h12217, hlam]
                                    · linarith only [h11558, h12217, hlam]
                                  · have p12197_0 := h12197c.1
                                    have p12197_1 := h12197c.2.1
                                    have p12197_2 := h12197c.2.2.1
                                    have p12197_3 := h12197c.2.2.2
                                    rcases p12197_3 (m.d 0 2) (by simp) with h12220 | h12220
                                    · linarith only [h0, h12220, hlam]
                                    · linarith only [h11559, h12220, hlam]
                                  · have p12197_0 := h12197c.1
                                    have p12197_1 := h12197c.2.1
                                    have p12197_2 := h12197c.2.2.1
                                    have p12197_3 := h12197c.2.2.2
                                    rcases p12197_3 (m.d 0 2) (by simp) with h12223 | h12223
                                    · linarith only [h0, h12223, hlam]
                                    · linarith only [h11560, h12223, hlam]
                                  · have p12197_0 := h12197c.1
                                    have p12197_1 := h12197c.2.1
                                    have p12197_2 := h12197c.2.2.1
                                    have p12197_3 := h12197c.2.2.2
                                    linarith only [h11558, hlam, p12197_0]
                                  · have p12197_0 := h12197c.1
                                    have p12197_1 := h12197c.2.1
                                    have p12197_2 := h12197c.2.2.1
                                    have p12197_3 := h12197c.2.2.2
                                    linarith only [h12081, hlam, p12197_0]
                                  · have p12197_0 := h12197c.1
                                    have p12197_1 := h12197c.2.1
                                    have p12197_2 := h12197c.2.2.1
                                    have p12197_3 := h12197c.2.2.2
                                    linarith only [hlam, p12197_0]
                                  · have p12197_0 := h12197c.1
                                    have p12197_1 := h12197c.2.1
                                    have p12197_2 := h12197c.2.2.1
                                    have p12197_3 := h12197c.2.2.2
                                    linarith only [h11558, hc24, hlam, hphi, ht0b, ht45, ht5b, p12197_1, u0elo1]
                                  · have p12197_0 := h12197c.1
                                    have p12197_1 := h12197c.2.1
                                    have p12197_2 := h12197c.2.2.1
                                    have p12197_3 := h12197c.2.2.2
                                    linarith only [h11558, hc25, hlam, hphi, ht0b, ht5b, p12197_1, u0elo1]
                                  · have p12197_0 := h12197c.1
                                    have p12197_1 := h12197c.2.1
                                    have p12197_2 := h12197c.2.2.1
                                    have p12197_3 := h12197c.2.2.2
                                    linarith only [h11559, hlam, p12197_0]
                                  · have p12197_0 := h12197c.1
                                    have p12197_1 := h12197c.2.1
                                    have p12197_2 := h12197c.2.2.1
                                    have p12197_3 := h12197c.2.2.2
                                    linarith only [h12082, hlam, p12197_0]
                                  · have p12197_0 := h12197c.1
                                    have p12197_1 := h12197c.2.1
                                    have p12197_2 := h12197c.2.2.1
                                    have p12197_3 := h12197c.2.2.2
                                    linarith only [h12086, hlam, p12197_1]
                                  · have p12197_0 := h12197c.1
                                    have p12197_1 := h12197c.2.1
                                    have p12197_2 := h12197c.2.2.1
                                    have p12197_3 := h12197c.2.2.2
                                    linarith only [hlam, p12197_0]
                                  · have p12197_0 := h12197c.1
                                    have p12197_1 := h12197c.2.1
                                    have p12197_2 := h12197c.2.2.1
                                    have p12197_3 := h12197c.2.2.2
                                    linarith only [h12088, hlam, p12197_1]
                                  · have p12197_0 := h12197c.1
                                    have p12197_1 := h12197c.2.1
                                    have p12197_2 := h12197c.2.2.1
                                    have p12197_3 := h12197c.2.2.2
                                    linarith only [h11560, hlam, p12197_0]
                                  · have p12197_0 := h12197c.1
                                    have p12197_1 := h12197c.2.1
                                    have p12197_2 := h12197c.2.2.1
                                    have p12197_3 := h12197c.2.2.2
                                    linarith only [h12083, hlam, p12197_0]
                                  · have p12197_0 := h12197c.1
                                    have p12197_1 := h12197c.2.1
                                    have p12197_2 := h12197c.2.2.1
                                    have p12197_3 := h12197c.2.2.2
                                    linarith only [h12087, hlam, p12197_1]
                                  · have p12197_0 := h12197c.1
                                    have p12197_1 := h12197c.2.1
                                    have p12197_2 := h12197c.2.2.1
                                    have p12197_3 := h12197c.2.2.2
                                    linarith only [h11560, h12086, hc34, hlam, hphi, ht0b, ht45, ht5b, p12197_1, u0elo1]
                                  · have p12197_0 := h12197c.1
                                    have p12197_1 := h12197c.2.1
                                    have p12197_2 := h12197c.2.2.1
                                    have p12197_3 := h12197c.2.2.2
                                    linarith only [hlam, p12197_0]
                                · linarith only [h11558, h11563, h12151, hlam, p12092_1, u0elo1]
                                · linarith only [h11558, h12151, hlam, p12092_1, u0elo1]
                          · linarith only [h11562, h12146, hlam]
                        · linarith only [h11560, h12145, hlam]
                    · have p12092_0 := h12092c.1
                      have p12092_1 := h12092c.2.1
                      have p12092_2 := h12092c.2.2.1
                      have p12092_3 := h12092c.2.2.2
                      linarith only [h11563, h12081, h12084, h12085, hc01, hc12, hlam, hphi, p12092_1]
                    · have p12092_0 := h12092c.1
                      have p12092_1 := h12092c.2.1
                      have p12092_2 := h12092c.2.2.1
                      have p12092_3 := h12092c.2.2.2
                      linarith only [h11559, hlam, p12092_0]
                    · have p12092_0 := h12092c.1
                      have p12092_1 := h12092c.2.1
                      have p12092_2 := h12092c.2.2.1
                      have p12092_3 := h12092c.2.2.2
                      linarith only [h11561, hlam, p12092_0]
                    · have p12092_0 := h12092c.1
                      have p12092_1 := h12092c.2.1
                      have p12092_2 := h12092c.2.2.1
                      have p12092_3 := h12092c.2.2.2
                      linarith only [hlam, p12092_0]
                    · have p12092_0 := h12092c.1
                      have p12092_1 := h12092c.2.1
                      have p12092_2 := h12092c.2.2.1
                      have p12092_3 := h12092c.2.2.2
                      linarith only [h11563, hlam, p12092_0]
                    · have p12092_0 := h12092c.1
                      have p12092_1 := h12092c.2.1
                      have p12092_2 := h12092c.2.2.1
                      have p12092_3 := h12092c.2.2.2
                      linarith only [h11563, h12081, h12084, h12085, hc01, hc12, hlam, hphi, p12092_1]
                    · have p12092_0 := h12092c.1
                      have p12092_1 := h12092c.2.1
                      have p12092_2 := h12092c.2.2.1
                      have p12092_3 := h12092c.2.2.2
                      linarith only [h11560, hlam, p12092_1]
                    · have p12092_0 := h12092c.1
                      have p12092_1 := h12092c.2.1
                      have p12092_2 := h12092c.2.2.1
                      have p12092_3 := h12092c.2.2.2
                      linarith only [h11562, hlam, p12092_0]
                    · have p12092_0 := h12092c.1
                      have p12092_1 := h12092c.2.1
                      have p12092_2 := h12092c.2.2.1
                      have p12092_3 := h12092c.2.2.2
                      linarith only [h10058, h11563, h12081, h12084, h12085, hc01, hc12, hlam, hphi, p12092_1]
                    · have p12092_0 := h12092c.1
                      have p12092_1 := h12092c.2.1
                      have p12092_2 := h12092c.2.2.1
                      have p12092_3 := h12092c.2.2.2
                      linarith only [hlam, p12092_0]
              · linarith only [h11558, h11562, h12086, h12087, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h12256 | h12256
              · linarith only [h11561, h11563, h12081, h12084, h12085, h12086, h12256, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h12258 | h12258
                · linarith only [h11559, h11561, h11563, h12086, h12258, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h12260 | h12260
                  · linarith only [h11561, h11563, h12260, hlam]
                  · rcases h0bigk with h12262c | h12262c | h12262c | h12262c | h12262c | h12262c | h12262c | h12262c | h12262c | h12262c | h12262c | h12262c | h12262c | h12262c | h12262c | h12262c | h12262c | h12262c | h12262c | h12262c | h12262c | h12262c | h12262c | h12262c | h12262c
                    · have p12262_0 := h12262c.1
                      have p12262_1 := h12262c.2.1
                      have p12262_2 := h12262c.2.2.1
                      have p12262_3 := h12262c.2.2.2
                      linarith only [hlam, p12262_0]
                    · have p12262_0 := h12262c.1
                      have p12262_1 := h12262c.2.1
                      have p12262_2 := h12262c.2.2.1
                      have p12262_3 := h12262c.2.2.2
                      linarith only [h0, hlam, p12262_1]
                    · have p12262_0 := h12262c.1
                      have p12262_1 := h12262c.2.1
                      have p12262_2 := h12262c.2.2.1
                      have p12262_3 := h12262c.2.2.2
                      linarith only [h6793, hlam, p12262_0]
                    · have p12262_0 := h12262c.1
                      have p12262_1 := h12262c.2.1
                      have p12262_2 := h12262c.2.2.1
                      have p12262_3 := h12262c.2.2.2
                      linarith only [h10058, hlam, p12262_1]
                    · have p12262_0 := h12262c.1
                      have p12262_1 := h12262c.2.1
                      have p12262_2 := h12262c.2.2.1
                      have p12262_3 := h12262c.2.2.2
                      linarith only [h11024, hlam, p12262_1]
                    · have p12262_0 := h12262c.1
                      have p12262_1 := h12262c.2.1
                      have p12262_2 := h12262c.2.2.1
                      have p12262_3 := h12262c.2.2.2
                      rcases p12262_3 (m.d 0 1) (by simp) with h12268 | h12268
                      · linarith only [h0, h12268, hlam]
                      · rcases p12262_3 (m.d 0 2) (by simp) with h12270 | h12270
                        · rcases p12262_3 (m.d 0 3) (by simp) with h12271 | h12271
                          · linarith only [h11558, h12271, hlam]
                          · linarith only [h12271, h6793, hlam]
                        · linarith only [h0, h12270, hlam]
                    · have p12262_0 := h12262c.1
                      have p12262_1 := h12262c.2.1
                      have p12262_2 := h12262c.2.2.1
                      have p12262_3 := h12262c.2.2.2
                      linarith only [hlam, p12262_0]
                    · have p12262_0 := h12262c.1
                      have p12262_1 := h12262c.2.1
                      have p12262_2 := h12262c.2.2.1
                      have p12262_3 := h12262c.2.2.2
                      linarith only [h11562, h12256, hc25, hlam, hphi, ht0b, ht5b, p12262_1, u0elo1]
                    · have p12262_0 := h12262c.1
                      have p12262_1 := h12262c.2.1
                      have p12262_2 := h12262c.2.2.1
                      have p12262_3 := h12262c.2.2.2
                      linarith only [h11561, h12086, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12262_1, u0elo1]
                    · have p12262_0 := h12262c.1
                      have p12262_1 := h12262c.2.1
                      have p12262_2 := h12262c.2.2.1
                      have p12262_3 := h12262c.2.2.2
                      linarith only [h11561, h11563, h12086, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12262_1, u0elo1]
                    · have p12262_0 := h12262c.1
                      have p12262_1 := h12262c.2.1
                      have p12262_2 := h12262c.2.2.1
                      have p12262_3 := h12262c.2.2.2
                      rcases p12262_3 (m.d 0 1) (by simp) with h12279 | h12279
                      · linarith only [h12279, h6793, hlam]
                      · rcases p12262_3 (m.d 0 2) (by simp) with h12281 | h12281
                        · rcases p12262_3 (m.d 0 3) (by simp) with h12282 | h12282
                          · rcases p12262_3 (m.d 0 4) (by simp) with h12283 | h12283
                            · linarith only [h11561, h12283, hlam]
                            · linarith only [h10058, h12283, hlam]
                          · linarith only [h12282, h6793, hlam]
                        · linarith only [h0, h12281, hlam]
                    · have p12262_0 := h12262c.1
                      have p12262_1 := h12262c.2.1
                      have p12262_2 := h12262c.2.2.1
                      have p12262_3 := h12262c.2.2.2
                      linarith only [h11558, hlam, p12262_1]
                    · have p12262_0 := h12262c.1
                      have p12262_1 := h12262c.2.1
                      have p12262_2 := h12262c.2.2.1
                      have p12262_3 := h12262c.2.2.2
                      linarith only [hlam, p12262_0]
                    · have p12262_0 := h12262c.1
                      have p12262_1 := h12262c.2.1
                      have p12262_2 := h12262c.2.2.1
                      have p12262_3 := h12262c.2.2.2
                      linarith only [h11561, h12086, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12262_1, u0elo2]
                    · have p12262_0 := h12262c.1
                      have p12262_1 := h12262c.2.1
                      have p12262_2 := h12262c.2.2.1
                      have p12262_3 := h12262c.2.2.2
                      linarith only [h11558, h11561, h11563, h12086, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12262_1, u0elo1]
                    · have p12262_0 := h12262c.1
                      have p12262_1 := h12262c.2.1
                      have p12262_2 := h12262c.2.2.1
                      have p12262_3 := h12262c.2.2.2
                      linarith only [h11563, h12081, h12084, h12085, hc01, hc12, hlam, hphi, p12262_1]
                    · have p12262_0 := h12262c.1
                      have p12262_1 := h12262c.2.1
                      have p12262_2 := h12262c.2.2.1
                      have p12262_3 := h12262c.2.2.2
                      linarith only [h11559, hlam, p12262_0]
                    · have p12262_0 := h12262c.1
                      have p12262_1 := h12262c.2.1
                      have p12262_2 := h12262c.2.2.1
                      have p12262_3 := h12262c.2.2.2
                      linarith only [h11561, hlam, p12262_0]
                    · have p12262_0 := h12262c.1
                      have p12262_1 := h12262c.2.1
                      have p12262_2 := h12262c.2.2.1
                      have p12262_3 := h12262c.2.2.2
                      linarith only [hlam, p12262_0]
                    · have p12262_0 := h12262c.1
                      have p12262_1 := h12262c.2.1
                      have p12262_2 := h12262c.2.2.1
                      have p12262_3 := h12262c.2.2.2
                      linarith only [h11563, hlam, p12262_0]
                    · have p12262_0 := h12262c.1
                      have p12262_1 := h12262c.2.1
                      have p12262_2 := h12262c.2.2.1
                      have p12262_3 := h12262c.2.2.2
                      linarith only [h11563, h12081, h12084, h12085, hc01, hc12, hlam, hphi, p12262_1]
                    · have p12262_0 := h12262c.1
                      have p12262_1 := h12262c.2.1
                      have p12262_2 := h12262c.2.2.1
                      have p12262_3 := h12262c.2.2.2
                      linarith only [h11560, hlam, p12262_1]
                    · have p12262_0 := h12262c.1
                      have p12262_1 := h12262c.2.1
                      have p12262_2 := h12262c.2.2.1
                      have p12262_3 := h12262c.2.2.2
                      linarith only [h11562, hlam, p12262_0]
                    · have p12262_0 := h12262c.1
                      have p12262_1 := h12262c.2.1
                      have p12262_2 := h12262c.2.2.1
                      have p12262_3 := h12262c.2.2.2
                      linarith only [h11561, h11563, h12081, h12084, h12085, h12086, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12262_1]
                    · have p12262_0 := h12262c.1
                      have p12262_1 := h12262c.2.1
                      have p12262_2 := h12262c.2.2.1
                      have p12262_3 := h12262c.2.2.2
                      linarith only [hlam, p12262_0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h12302 | h12302
            · rcases m.htr 2 3 5 (by decide) (by decide) with h12303 | h12303
              · rcases m.htr 2 4 5 (by decide) (by decide) with h12304 | h12304
                · linarith only [h10058, h12085, h12304, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h12306 | h12306
                  · linarith only [h11024, h11559, h12085, h12302, h12306, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · rcases h0bigk with h12308c | h12308c | h12308c | h12308c | h12308c | h12308c | h12308c | h12308c | h12308c | h12308c | h12308c | h12308c | h12308c | h12308c | h12308c | h12308c | h12308c | h12308c | h12308c | h12308c | h12308c | h12308c | h12308c | h12308c | h12308c
                    · have p12308_0 := h12308c.1
                      have p12308_1 := h12308c.2.1
                      have p12308_2 := h12308c.2.2.1
                      have p12308_3 := h12308c.2.2.2
                      linarith only [hlam, p12308_0]
                    · have p12308_0 := h12308c.1
                      have p12308_1 := h12308c.2.1
                      have p12308_2 := h12308c.2.2.1
                      have p12308_3 := h12308c.2.2.2
                      linarith only [h0, hlam, p12308_1]
                    · have p12308_0 := h12308c.1
                      have p12308_1 := h12308c.2.1
                      have p12308_2 := h12308c.2.2.1
                      have p12308_3 := h12308c.2.2.2
                      linarith only [h6793, hlam, p12308_0]
                    · have p12308_0 := h12308c.1
                      have p12308_1 := h12308c.2.1
                      have p12308_2 := h12308c.2.2.1
                      have p12308_3 := h12308c.2.2.2
                      linarith only [h10058, hlam, p12308_1]
                    · have p12308_0 := h12308c.1
                      have p12308_1 := h12308c.2.1
                      have p12308_2 := h12308c.2.2.1
                      have p12308_3 := h12308c.2.2.2
                      linarith only [h11024, hlam, p12308_1]
                    · have p12308_0 := h12308c.1
                      have p12308_1 := h12308c.2.1
                      have p12308_2 := h12308c.2.2.1
                      have p12308_3 := h12308c.2.2.2
                      rcases p12308_3 (m.d 0 1) (by simp) with h12314 | h12314
                      · linarith only [h0, h12314, hlam]
                      · rcases p12308_3 (m.d 0 2) (by simp) with h12316 | h12316
                        · rcases p12308_3 (m.d 0 3) (by simp) with h12317 | h12317
                          · linarith only [h11558, h12317, hlam]
                          · linarith only [h12317, h6793, hlam]
                        · linarith only [h0, h12316, hlam]
                    · have p12308_0 := h12308c.1
                      have p12308_1 := h12308c.2.1
                      have p12308_2 := h12308c.2.2.1
                      have p12308_3 := h12308c.2.2.2
                      linarith only [hlam, p12308_0]
                    · have p12308_0 := h12308c.1
                      have p12308_1 := h12308c.2.1
                      have p12308_2 := h12308c.2.2.1
                      have p12308_3 := h12308c.2.2.2
                      linarith only [h11558, h12303, h12306, hc34, hlam, hphi, ht0b, ht45, ht5b, p12308_1, u0elo1]
                    · have p12308_0 := h12308c.1
                      have p12308_1 := h12308c.2.1
                      have p12308_2 := h12308c.2.2.1
                      have p12308_3 := h12308c.2.2.2
                      rcases p12308_3 (m.d 0 1) (by simp) with h12323 | h12323
                      · linarith only [h0, h12323, hlam]
                      · rcases p12308_3 (m.d 0 2) (by simp) with h12325 | h12325
                        · rcases p12308_3 (m.d 0 3) (by simp) with h12326 | h12326
                          · linarith only [h11558, h12326, hlam]
                          · linarith only [h11561, h12326, hlam]
                        · linarith only [h11559, h12325, hlam]
                    · have p12308_0 := h12308c.1
                      have p12308_1 := h12308c.2.1
                      have p12308_2 := h12308c.2.2.1
                      have p12308_3 := h12308c.2.2.2
                      rcases p12308_3 (m.d 0 1) (by simp) with h12330 | h12330
                      · linarith only [h0, h12330, hlam]
                      · rcases p12308_3 (m.d 0 2) (by simp) with h12332 | h12332
                        · rcases p12308_3 (m.d 0 3) (by simp) with h12333 | h12333
                          · linarith only [h11558, h12333, hlam]
                          · linarith only [h11562, h12333, hlam]
                        · linarith only [h11560, h12332, hlam]
                    · have p12308_0 := h12308c.1
                      have p12308_1 := h12308c.2.1
                      have p12308_2 := h12308c.2.2.1
                      have p12308_3 := h12308c.2.2.2
                      rcases p12308_3 (m.d 0 1) (by simp) with h12337 | h12337
                      · linarith only [h12337, h6793, hlam]
                      · rcases p12308_3 (m.d 0 2) (by simp) with h12339 | h12339
                        · rcases p12308_3 (m.d 0 3) (by simp) with h12340 | h12340
                          · rcases p12308_3 (m.d 0 4) (by simp) with h12341 | h12341
                            · linarith only [h11561, h12341, hlam]
                            · linarith only [h10058, h12341, hlam]
                          · linarith only [h12340, h6793, hlam]
                        · linarith only [h0, h12339, hlam]
                    · have p12308_0 := h12308c.1
                      have p12308_1 := h12308c.2.1
                      have p12308_2 := h12308c.2.2.1
                      have p12308_3 := h12308c.2.2.2
                      linarith only [h11558, hlam, p12308_1]
                    · have p12308_0 := h12308c.1
                      have p12308_1 := h12308c.2.1
                      have p12308_2 := h12308c.2.2.1
                      have p12308_3 := h12308c.2.2.2
                      linarith only [hlam, p12308_0]
                    · have p12308_0 := h12308c.1
                      have p12308_1 := h12308c.2.1
                      have p12308_2 := h12308c.2.2.1
                      have p12308_3 := h12308c.2.2.2
                      rcases p12308_3 (m.d 0 1) (by simp) with h12348 | h12348
                      · linarith only [h12348, h6793, hlam]
                      · rcases p12308_3 (m.d 0 2) (by simp) with h12350 | h12350
                        · rcases p12308_3 (m.d 0 3) (by simp) with h12351 | h12351
                          · rcases p12308_3 (m.d 0 4) (by simp) with h12352 | h12352
                            · linarith only [h11561, h12352, hlam]
                            · rcases p12308_3 (m.d 0 5) (by simp) with h12354 | h12354
                              · linarith only [h11562, h12354, hlam]
                              · linarith only [h11563, h12354, hlam]
                          · linarith only [h11561, h12351, hlam]
                        · linarith only [h11559, h12350, hlam]
                    · have p12308_0 := h12308c.1
                      have p12308_1 := h12308c.2.1
                      have p12308_2 := h12308c.2.2.1
                      have p12308_3 := h12308c.2.2.2
                      rcases p12308_3 (m.d 0 1) (by simp) with h12359 | h12359
                      · linarith only [h12359, h6793, hlam]
                      · rcases p12308_3 (m.d 0 2) (by simp) with h12361 | h12361
                        · rcases p12308_3 (m.d 0 3) (by simp) with h12362 | h12362
                          · rcases p12308_3 (m.d 0 4) (by simp) with h12363 | h12363
                            · linarith only [h11561, h12363, hlam]
                            · rcases p12308_3 (m.d 0 5) (by simp) with h12365 | h12365
                              · linarith only [h11562, h12365, hlam]
                              · rcases h0emin with h12367 | h12367 | h12367 | h12367 | h12367
                                · linarith only [h10058, h12085, h12367, hc45, hlam, ht01, ht12, ht23, ht34]
                                · rcases h2bigk with h12369c | h12369c | h12369c | h12369c | h12369c | h12369c | h12369c | h12369c | h12369c | h12369c | h12369c | h12369c | h12369c | h12369c | h12369c | h12369c | h12369c | h12369c | h12369c | h12369c | h12369c | h12369c | h12369c | h12369c | h12369c
                                  · have p12369_0 := h12369c.1
                                    have p12369_1 := h12369c.2.1
                                    have p12369_2 := h12369c.2.2.1
                                    have p12369_3 := h12369c.2.2.2
                                    linarith only [hlam, p12369_0]
                                  · have p12369_0 := h12369c.1
                                    have p12369_1 := h12369c.2.1
                                    have p12369_2 := h12369c.2.2.1
                                    have p12369_3 := h12369c.2.2.2
                                    linarith only [h0, hlam, p12369_1]
                                  · have p12369_0 := h12369c.1
                                    have p12369_1 := h12369c.2.1
                                    have p12369_2 := h12369c.2.2.1
                                    have p12369_3 := h12369c.2.2.2
                                    linarith only [h12303, h12306, hc34, hlam, hphi, ht0b, ht45, ht5b, p12369_1, u0elo1]
                                  · have p12369_0 := h12369c.1
                                    have p12369_1 := h12369c.2.1
                                    have p12369_2 := h12369c.2.2.1
                                    have p12369_3 := h12369c.2.2.2
                                    rcases p12369_3 (m.d 0 2) (by simp) with h12373 | h12373
                                    · rcases p12369_3 (m.d 1 2) (by simp) with h12374 | h12374
                                      · rcases p12369_3 (m.d 2 3) (by simp) with h12375 | h12375
                                        · linarith only [h11558, h12375, hlam]
                                        · linarith only [h12302, h12375, hlam]
                                      · linarith only [h12082, h12374, hlam]
                                    · linarith only [h12373, hlam, p12369_0]
                                  · have p12369_0 := h12369c.1
                                    have p12369_1 := h12369c.2.1
                                    have p12369_2 := h12369c.2.2.1
                                    have p12369_3 := h12369c.2.2.2
                                    rcases p12369_3 (m.d 0 2) (by simp) with h12380 | h12380
                                    · rcases p12369_3 (m.d 1 2) (by simp) with h12381 | h12381
                                      · rcases p12369_3 (m.d 2 3) (by simp) with h12382 | h12382
                                        · linarith only [h11558, h12382, hlam]
                                        · linarith only [h12303, h12382, hlam]
                                      · linarith only [h12083, h12381, hlam]
                                    · linarith only [h12380, hlam, p12369_0]
                                  · have p12369_0 := h12369c.1
                                    have p12369_1 := h12369c.2.1
                                    have p12369_2 := h12369c.2.2.1
                                    have p12369_3 := h12369c.2.2.2
                                    linarith only [h12367, hc12, hlam, ht01, p12369_1]
                                  · have p12369_0 := h12369c.1
                                    have p12369_1 := h12369c.2.1
                                    have p12369_2 := h12369c.2.2.1
                                    have p12369_3 := h12369c.2.2.2
                                    linarith only [hlam, p12369_0]
                                  · have p12369_0 := h12369c.1
                                    have p12369_1 := h12369c.2.1
                                    have p12369_2 := h12369c.2.2.1
                                    have p12369_3 := h12369c.2.2.2
                                    rcases p12369_3 (m.d 0 2) (by simp) with h12389 | h12389
                                    · linarith only [h0, h12389, hlam]
                                    · linarith only [h11558, h12389, hlam]
                                  · have p12369_0 := h12369c.1
                                    have p12369_1 := h12369c.2.1
                                    have p12369_2 := h12369c.2.2.1
                                    have p12369_3 := h12369c.2.2.2
                                    rcases p12369_3 (m.d 0 2) (by simp) with h12392 | h12392
                                    · linarith only [h0, h12392, hlam]
                                    · linarith only [h11559, h12392, hlam]
                                  · have p12369_0 := h12369c.1
                                    have p12369_1 := h12369c.2.1
                                    have p12369_2 := h12369c.2.2.1
                                    have p12369_3 := h12369c.2.2.2
                                    rcases p12369_3 (m.d 0 2) (by simp) with h12395 | h12395
                                    · linarith only [h0, h12395, hlam]
                                    · linarith only [h11560, h12395, hlam]
                                  · have p12369_0 := h12369c.1
                                    have p12369_1 := h12369c.2.1
                                    have p12369_2 := h12369c.2.2.1
                                    have p12369_3 := h12369c.2.2.2
                                    linarith only [h11558, hlam, p12369_0]
                                  · have p12369_0 := h12369c.1
                                    have p12369_1 := h12369c.2.1
                                    have p12369_2 := h12369c.2.2.1
                                    have p12369_3 := h12369c.2.2.2
                                    linarith only [h12081, hlam, p12369_0]
                                  · have p12369_0 := h12369c.1
                                    have p12369_1 := h12369c.2.1
                                    have p12369_2 := h12369c.2.2.1
                                    have p12369_3 := h12369c.2.2.2
                                    linarith only [hlam, p12369_0]
                                  · have p12369_0 := h12369c.1
                                    have p12369_1 := h12369c.2.1
                                    have p12369_2 := h12369c.2.2.1
                                    have p12369_3 := h12369c.2.2.2
                                    linarith only [h11558, hc24, hlam, hphi, ht0b, ht45, ht5b, p12369_1, u0elo1]
                                  · have p12369_0 := h12369c.1
                                    have p12369_1 := h12369c.2.1
                                    have p12369_2 := h12369c.2.2.1
                                    have p12369_3 := h12369c.2.2.2
                                    linarith only [h11558, hc25, hlam, hphi, ht0b, ht5b, p12369_1, u0elo1]
                                  · have p12369_0 := h12369c.1
                                    have p12369_1 := h12369c.2.1
                                    have p12369_2 := h12369c.2.2.1
                                    have p12369_3 := h12369c.2.2.2
                                    linarith only [h11559, hlam, p12369_0]
                                  · have p12369_0 := h12369c.1
                                    have p12369_1 := h12369c.2.1
                                    have p12369_2 := h12369c.2.2.1
                                    have p12369_3 := h12369c.2.2.2
                                    linarith only [h12082, hlam, p12369_0]
                                  · have p12369_0 := h12369c.1
                                    have p12369_1 := h12369c.2.1
                                    have p12369_2 := h12369c.2.2.1
                                    have p12369_3 := h12369c.2.2.2
                                    linarith only [h12302, hlam, p12369_1]
                                  · have p12369_0 := h12369c.1
                                    have p12369_1 := h12369c.2.1
                                    have p12369_2 := h12369c.2.2.1
                                    have p12369_3 := h12369c.2.2.2
                                    linarith only [hlam, p12369_0]
                                  · have p12369_0 := h12369c.1
                                    have p12369_1 := h12369c.2.1
                                    have p12369_2 := h12369c.2.2.1
                                    have p12369_3 := h12369c.2.2.2
                                    linarith only [h12304, hlam, p12369_1]
                                  · have p12369_0 := h12369c.1
                                    have p12369_1 := h12369c.2.1
                                    have p12369_2 := h12369c.2.2.1
                                    have p12369_3 := h12369c.2.2.2
                                    linarith only [h11560, hlam, p12369_0]
                                  · have p12369_0 := h12369c.1
                                    have p12369_1 := h12369c.2.1
                                    have p12369_2 := h12369c.2.2.1
                                    have p12369_3 := h12369c.2.2.2
                                    linarith only [h12083, hlam, p12369_0]
                                  · have p12369_0 := h12369c.1
                                    have p12369_1 := h12369c.2.1
                                    have p12369_2 := h12369c.2.2.1
                                    have p12369_3 := h12369c.2.2.2
                                    linarith only [h12303, hlam, p12369_1]
                                  · have p12369_0 := h12369c.1
                                    have p12369_1 := h12369c.2.1
                                    have p12369_2 := h12369c.2.2.1
                                    have p12369_3 := h12369c.2.2.2
                                    linarith only [h11560, h12302, hc34, hlam, hphi, ht0b, ht45, ht5b, p12369_1, u0elo1]
                                  · have p12369_0 := h12369c.1
                                    have p12369_1 := h12369c.2.1
                                    have p12369_2 := h12369c.2.2.1
                                    have p12369_3 := h12369c.2.2.2
                                    linarith only [hlam, p12369_0]
                                · rcases h2bigk with h12413c | h12413c | h12413c | h12413c | h12413c | h12413c | h12413c | h12413c | h12413c | h12413c | h12413c | h12413c | h12413c | h12413c | h12413c | h12413c | h12413c | h12413c | h12413c | h12413c | h12413c | h12413c | h12413c | h12413c | h12413c
                                  · have p12413_0 := h12413c.1
                                    have p12413_1 := h12413c.2.1
                                    have p12413_2 := h12413c.2.2.1
                                    have p12413_3 := h12413c.2.2.2
                                    linarith only [hlam, p12413_0]
                                  · have p12413_0 := h12413c.1
                                    have p12413_1 := h12413c.2.1
                                    have p12413_2 := h12413c.2.2.1
                                    have p12413_3 := h12413c.2.2.2
                                    linarith only [h0, hlam, p12413_1]
                                  · have p12413_0 := h12413c.1
                                    have p12413_1 := h12413c.2.1
                                    have p12413_2 := h12413c.2.2.1
                                    have p12413_3 := h12413c.2.2.2
                                    linarith only [h12302, hc34, hlam, hphi, ht0b, ht45, ht5b, p12413_1, u0elo1]
                                  · have p12413_0 := h12413c.1
                                    have p12413_1 := h12413c.2.1
                                    have p12413_2 := h12413c.2.2.1
                                    have p12413_3 := h12413c.2.2.2
                                    rcases p12413_3 (m.d 0 2) (by simp) with h12417 | h12417
                                    · rcases p12413_3 (m.d 1 2) (by simp) with h12418 | h12418
                                      · rcases p12413_3 (m.d 2 3) (by simp) with h12419 | h12419
                                        · linarith only [h11558, h12419, hlam]
                                        · linarith only [h12302, h12419, hlam]
                                      · linarith only [h12082, h12418, hlam]
                                    · linarith only [h12417, hlam, p12413_0]
                                  · have p12413_0 := h12413c.1
                                    have p12413_1 := h12413c.2.1
                                    have p12413_2 := h12413c.2.2.1
                                    have p12413_3 := h12413c.2.2.2
                                    rcases p12413_3 (m.d 0 2) (by simp) with h12424 | h12424
                                    · rcases p12413_3 (m.d 1 2) (by simp) with h12425 | h12425
                                      · rcases p12413_3 (m.d 2 3) (by simp) with h12426 | h12426
                                        · linarith only [h11558, h12426, hlam]
                                        · linarith only [h12303, h12426, hlam]
                                      · linarith only [h12083, h12425, hlam]
                                    · linarith only [h12424, hlam, p12413_0]
                                  · have p12413_0 := h12413c.1
                                    have p12413_1 := h12413c.2.1
                                    have p12413_2 := h12413c.2.2.1
                                    have p12413_3 := h12413c.2.2.2
                                    linarith only [h11558, h12303, h12306, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12413_1]
                                  · have p12413_0 := h12413c.1
                                    have p12413_1 := h12413c.2.1
                                    have p12413_2 := h12413c.2.2.1
                                    have p12413_3 := h12413c.2.2.2
                                    linarith only [hlam, p12413_0]
                                  · have p12413_0 := h12413c.1
                                    have p12413_1 := h12413c.2.1
                                    have p12413_2 := h12413c.2.2.1
                                    have p12413_3 := h12413c.2.2.2
                                    rcases p12413_3 (m.d 0 2) (by simp) with h12433 | h12433
                                    · linarith only [h0, h12433, hlam]
                                    · linarith only [h11558, h12433, hlam]
                                  · have p12413_0 := h12413c.1
                                    have p12413_1 := h12413c.2.1
                                    have p12413_2 := h12413c.2.2.1
                                    have p12413_3 := h12413c.2.2.2
                                    rcases p12413_3 (m.d 0 2) (by simp) with h12436 | h12436
                                    · linarith only [h0, h12436, hlam]
                                    · linarith only [h11559, h12436, hlam]
                                  · have p12413_0 := h12413c.1
                                    have p12413_1 := h12413c.2.1
                                    have p12413_2 := h12413c.2.2.1
                                    have p12413_3 := h12413c.2.2.2
                                    rcases p12413_3 (m.d 0 2) (by simp) with h12439 | h12439
                                    · linarith only [h0, h12439, hlam]
                                    · linarith only [h11560, h12439, hlam]
                                  · have p12413_0 := h12413c.1
                                    have p12413_1 := h12413c.2.1
                                    have p12413_2 := h12413c.2.2.1
                                    have p12413_3 := h12413c.2.2.2
                                    linarith only [h11558, hlam, p12413_0]
                                  · have p12413_0 := h12413c.1
                                    have p12413_1 := h12413c.2.1
                                    have p12413_2 := h12413c.2.2.1
                                    have p12413_3 := h12413c.2.2.2
                                    linarith only [h12081, hlam, p12413_0]
                                  · have p12413_0 := h12413c.1
                                    have p12413_1 := h12413c.2.1
                                    have p12413_2 := h12413c.2.2.1
                                    have p12413_3 := h12413c.2.2.2
                                    linarith only [hlam, p12413_0]
                                  · have p12413_0 := h12413c.1
                                    have p12413_1 := h12413c.2.1
                                    have p12413_2 := h12413c.2.2.1
                                    have p12413_3 := h12413c.2.2.2
                                    linarith only [h11558, hc24, hlam, hphi, ht0b, ht45, ht5b, p12413_1, u0elo1]
                                  · have p12413_0 := h12413c.1
                                    have p12413_1 := h12413c.2.1
                                    have p12413_2 := h12413c.2.2.1
                                    have p12413_3 := h12413c.2.2.2
                                    linarith only [h11558, hc25, hlam, hphi, ht0b, ht5b, p12413_1, u0elo1]
                                  · have p12413_0 := h12413c.1
                                    have p12413_1 := h12413c.2.1
                                    have p12413_2 := h12413c.2.2.1
                                    have p12413_3 := h12413c.2.2.2
                                    linarith only [h11559, hlam, p12413_0]
                                  · have p12413_0 := h12413c.1
                                    have p12413_1 := h12413c.2.1
                                    have p12413_2 := h12413c.2.2.1
                                    have p12413_3 := h12413c.2.2.2
                                    linarith only [h12082, hlam, p12413_0]
                                  · have p12413_0 := h12413c.1
                                    have p12413_1 := h12413c.2.1
                                    have p12413_2 := h12413c.2.2.1
                                    have p12413_3 := h12413c.2.2.2
                                    linarith only [h12302, hlam, p12413_1]
                                  · have p12413_0 := h12413c.1
                                    have p12413_1 := h12413c.2.1
                                    have p12413_2 := h12413c.2.2.1
                                    have p12413_3 := h12413c.2.2.2
                                    linarith only [hlam, p12413_0]
                                  · have p12413_0 := h12413c.1
                                    have p12413_1 := h12413c.2.1
                                    have p12413_2 := h12413c.2.2.1
                                    have p12413_3 := h12413c.2.2.2
                                    linarith only [h12304, hlam, p12413_1]
                                  · have p12413_0 := h12413c.1
                                    have p12413_1 := h12413c.2.1
                                    have p12413_2 := h12413c.2.2.1
                                    have p12413_3 := h12413c.2.2.2
                                    linarith only [h11560, hlam, p12413_0]
                                  · have p12413_0 := h12413c.1
                                    have p12413_1 := h12413c.2.1
                                    have p12413_2 := h12413c.2.2.1
                                    have p12413_3 := h12413c.2.2.2
                                    linarith only [h12083, hlam, p12413_0]
                                  · have p12413_0 := h12413c.1
                                    have p12413_1 := h12413c.2.1
                                    have p12413_2 := h12413c.2.2.1
                                    have p12413_3 := h12413c.2.2.2
                                    linarith only [h12303, hlam, p12413_1]
                                  · have p12413_0 := h12413c.1
                                    have p12413_1 := h12413c.2.1
                                    have p12413_2 := h12413c.2.2.1
                                    have p12413_3 := h12413c.2.2.2
                                    linarith only [h11560, h12302, hc34, hlam, hphi, ht0b, ht45, ht5b, p12413_1, u0elo1]
                                  · have p12413_0 := h12413c.1
                                    have p12413_1 := h12413c.2.1
                                    have p12413_2 := h12413c.2.2.1
                                    have p12413_3 := h12413c.2.2.2
                                    linarith only [hlam, p12413_0]
                                · linarith only [h11558, h11563, h12367, hlam, p12308_1, u0elo1]
                                · linarith only [h11558, h12367, hlam, p12308_1, u0elo1]
                          · linarith only [h11562, h12362, hlam]
                        · linarith only [h11560, h12361, hlam]
                    · have p12308_0 := h12308c.1
                      have p12308_1 := h12308c.2.1
                      have p12308_2 := h12308c.2.2.1
                      have p12308_3 := h12308c.2.2.2
                      linarith only [h10058, h12085, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p12308_1]
                    · have p12308_0 := h12308c.1
                      have p12308_1 := h12308c.2.1
                      have p12308_2 := h12308c.2.2.1
                      have p12308_3 := h12308c.2.2.2
                      linarith only [h11559, hlam, p12308_0]
                    · have p12308_0 := h12308c.1
                      have p12308_1 := h12308c.2.1
                      have p12308_2 := h12308c.2.2.1
                      have p12308_3 := h12308c.2.2.2
                      linarith only [h11561, hlam, p12308_0]
                    · have p12308_0 := h12308c.1
                      have p12308_1 := h12308c.2.1
                      have p12308_2 := h12308c.2.2.1
                      have p12308_3 := h12308c.2.2.2
                      linarith only [hlam, p12308_0]
                    · have p12308_0 := h12308c.1
                      have p12308_1 := h12308c.2.1
                      have p12308_2 := h12308c.2.2.1
                      have p12308_3 := h12308c.2.2.2
                      linarith only [h11563, hlam, p12308_0]
                    · have p12308_0 := h12308c.1
                      have p12308_1 := h12308c.2.1
                      have p12308_2 := h12308c.2.2.1
                      have p12308_3 := h12308c.2.2.2
                      rcases p12308_3 (m.d 0 1) (by simp) with h12466 | h12466
                      · linarith only [h11024, h12466, hlam]
                      · rcases p12308_3 (m.d 0 2) (by simp) with h12468 | h12468
                        · rcases p12308_3 (m.d 0 3) (by simp) with h12469 | h12469
                          · rcases p12308_3 (m.d 0 4) (by simp) with h12470 | h12470
                            · linarith only [h11563, h12470, hlam]
                            · linarith only [h10058, h12470, hlam]
                          · linarith only [h12469, h6793, hlam]
                        · linarith only [h0, h12468, hlam]
                    · have p12308_0 := h12308c.1
                      have p12308_1 := h12308c.2.1
                      have p12308_2 := h12308c.2.2.1
                      have p12308_3 := h12308c.2.2.2
                      linarith only [h11560, hlam, p12308_1]
                    · have p12308_0 := h12308c.1
                      have p12308_1 := h12308c.2.1
                      have p12308_2 := h12308c.2.2.1
                      have p12308_3 := h12308c.2.2.2
                      linarith only [h11562, hlam, p12308_0]
                    · have p12308_0 := h12308c.1
                      have p12308_1 := h12308c.2.1
                      have p12308_2 := h12308c.2.2.1
                      have p12308_3 := h12308c.2.2.2
                      rcases p12308_3 (m.d 0 1) (by simp) with h12477 | h12477
                      · linarith only [h11024, h12477, hlam]
                      · rcases p12308_3 (m.d 0 2) (by simp) with h12479 | h12479
                        · rcases p12308_3 (m.d 0 3) (by simp) with h12480 | h12480
                          · rcases p12308_3 (m.d 0 4) (by simp) with h12481 | h12481
                            · linarith only [h11563, h12481, hlam]
                            · rcases p12308_3 (m.d 0 5) (by simp) with h12483 | h12483
                              · rcases h0emin with h12484 | h12484 | h12484 | h12484 | h12484
                                · linarith only [h10058, h12484, hlam, p12308_1, u0elo4]
                                · rcases h2bigk with h12486c | h12486c | h12486c | h12486c | h12486c | h12486c | h12486c | h12486c | h12486c | h12486c | h12486c | h12486c | h12486c | h12486c | h12486c | h12486c | h12486c | h12486c | h12486c | h12486c | h12486c | h12486c | h12486c | h12486c | h12486c
                                  · have p12486_0 := h12486c.1
                                    have p12486_1 := h12486c.2.1
                                    have p12486_2 := h12486c.2.2.1
                                    have p12486_3 := h12486c.2.2.2
                                    linarith only [hlam, p12486_0]
                                  · have p12486_0 := h12486c.1
                                    have p12486_1 := h12486c.2.1
                                    have p12486_2 := h12486c.2.2.1
                                    have p12486_3 := h12486c.2.2.2
                                    linarith only [h0, hlam, p12486_1]
                                  · have p12486_0 := h12486c.1
                                    have p12486_1 := h12486c.2.1
                                    have p12486_2 := h12486c.2.2.1
                                    have p12486_3 := h12486c.2.2.2
                                    linarith only [h12302, hc34, hlam, hphi, ht0b, ht45, ht5b, p12486_1, u0elo1]
                                  · have p12486_0 := h12486c.1
                                    have p12486_1 := h12486c.2.1
                                    have p12486_2 := h12486c.2.2.1
                                    have p12486_3 := h12486c.2.2.2
                                    rcases p12486_3 (m.d 0 2) (by simp) with h12490 | h12490
                                    · rcases p12486_3 (m.d 1 2) (by simp) with h12491 | h12491
                                      · rcases p12486_3 (m.d 2 3) (by simp) with h12492 | h12492
                                        · linarith only [h11558, h12492, hlam]
                                        · linarith only [h12302, h12492, hlam]
                                      · linarith only [h12082, h12491, hlam]
                                    · linarith only [h12490, hlam, p12486_0]
                                  · have p12486_0 := h12486c.1
                                    have p12486_1 := h12486c.2.1
                                    have p12486_2 := h12486c.2.2.1
                                    have p12486_3 := h12486c.2.2.2
                                    rcases p12486_3 (m.d 0 2) (by simp) with h12497 | h12497
                                    · rcases p12486_3 (m.d 1 2) (by simp) with h12498 | h12498
                                      · rcases p12486_3 (m.d 2 3) (by simp) with h12499 | h12499
                                        · linarith only [h11558, h12499, hlam]
                                        · linarith only [h12303, h12499, hlam]
                                      · linarith only [h12083, h12498, hlam]
                                    · linarith only [h12497, hlam, p12486_0]
                                  · have p12486_0 := h12486c.1
                                    have p12486_1 := h12486c.2.1
                                    have p12486_2 := h12486c.2.2.1
                                    have p12486_3 := h12486c.2.2.2
                                    linarith only [h10058, h11558, h11562, hc01, hc12, hlam, hphi, p12308_1, p12486_1]
                                  · have p12486_0 := h12486c.1
                                    have p12486_1 := h12486c.2.1
                                    have p12486_2 := h12486c.2.2.1
                                    have p12486_3 := h12486c.2.2.2
                                    linarith only [hlam, p12486_0]
                                  · have p12486_0 := h12486c.1
                                    have p12486_1 := h12486c.2.1
                                    have p12486_2 := h12486c.2.2.1
                                    have p12486_3 := h12486c.2.2.2
                                    rcases p12486_3 (m.d 0 2) (by simp) with h12506 | h12506
                                    · linarith only [h0, h12506, hlam]
                                    · linarith only [h11558, h12506, hlam]
                                  · have p12486_0 := h12486c.1
                                    have p12486_1 := h12486c.2.1
                                    have p12486_2 := h12486c.2.2.1
                                    have p12486_3 := h12486c.2.2.2
                                    rcases p12486_3 (m.d 0 2) (by simp) with h12509 | h12509
                                    · linarith only [h0, h12509, hlam]
                                    · linarith only [h11559, h12509, hlam]
                                  · have p12486_0 := h12486c.1
                                    have p12486_1 := h12486c.2.1
                                    have p12486_2 := h12486c.2.2.1
                                    have p12486_3 := h12486c.2.2.2
                                    rcases p12486_3 (m.d 0 2) (by simp) with h12512 | h12512
                                    · linarith only [h0, h12512, hlam]
                                    · linarith only [h11560, h12512, hlam]
                                  · have p12486_0 := h12486c.1
                                    have p12486_1 := h12486c.2.1
                                    have p12486_2 := h12486c.2.2.1
                                    have p12486_3 := h12486c.2.2.2
                                    linarith only [h11558, hlam, p12486_0]
                                  · have p12486_0 := h12486c.1
                                    have p12486_1 := h12486c.2.1
                                    have p12486_2 := h12486c.2.2.1
                                    have p12486_3 := h12486c.2.2.2
                                    linarith only [h12081, hlam, p12486_0]
                                  · have p12486_0 := h12486c.1
                                    have p12486_1 := h12486c.2.1
                                    have p12486_2 := h12486c.2.2.1
                                    have p12486_3 := h12486c.2.2.2
                                    linarith only [hlam, p12486_0]
                                  · have p12486_0 := h12486c.1
                                    have p12486_1 := h12486c.2.1
                                    have p12486_2 := h12486c.2.2.1
                                    have p12486_3 := h12486c.2.2.2
                                    linarith only [h11558, hc24, hlam, hphi, ht0b, ht45, ht5b, p12486_1, u0elo1]
                                  · have p12486_0 := h12486c.1
                                    have p12486_1 := h12486c.2.1
                                    have p12486_2 := h12486c.2.2.1
                                    have p12486_3 := h12486c.2.2.2
                                    linarith only [h11558, hc25, hlam, hphi, ht0b, ht5b, p12486_1, u0elo1]
                                  · have p12486_0 := h12486c.1
                                    have p12486_1 := h12486c.2.1
                                    have p12486_2 := h12486c.2.2.1
                                    have p12486_3 := h12486c.2.2.2
                                    linarith only [h11559, hlam, p12486_0]
                                  · have p12486_0 := h12486c.1
                                    have p12486_1 := h12486c.2.1
                                    have p12486_2 := h12486c.2.2.1
                                    have p12486_3 := h12486c.2.2.2
                                    linarith only [h12082, hlam, p12486_0]
                                  · have p12486_0 := h12486c.1
                                    have p12486_1 := h12486c.2.1
                                    have p12486_2 := h12486c.2.2.1
                                    have p12486_3 := h12486c.2.2.2
                                    linarith only [h12302, hlam, p12486_1]
                                  · have p12486_0 := h12486c.1
                                    have p12486_1 := h12486c.2.1
                                    have p12486_2 := h12486c.2.2.1
                                    have p12486_3 := h12486c.2.2.2
                                    linarith only [hlam, p12486_0]
                                  · have p12486_0 := h12486c.1
                                    have p12486_1 := h12486c.2.1
                                    have p12486_2 := h12486c.2.2.1
                                    have p12486_3 := h12486c.2.2.2
                                    linarith only [h12304, hlam, p12486_1]
                                  · have p12486_0 := h12486c.1
                                    have p12486_1 := h12486c.2.1
                                    have p12486_2 := h12486c.2.2.1
                                    have p12486_3 := h12486c.2.2.2
                                    linarith only [h11560, hlam, p12486_0]
                                  · have p12486_0 := h12486c.1
                                    have p12486_1 := h12486c.2.1
                                    have p12486_2 := h12486c.2.2.1
                                    have p12486_3 := h12486c.2.2.2
                                    linarith only [h12083, hlam, p12486_0]
                                  · have p12486_0 := h12486c.1
                                    have p12486_1 := h12486c.2.1
                                    have p12486_2 := h12486c.2.2.1
                                    have p12486_3 := h12486c.2.2.2
                                    linarith only [h12303, hlam, p12486_1]
                                  · have p12486_0 := h12486c.1
                                    have p12486_1 := h12486c.2.1
                                    have p12486_2 := h12486c.2.2.1
                                    have p12486_3 := h12486c.2.2.2
                                    linarith only [h11560, h12302, hc34, hlam, hphi, ht0b, ht45, ht5b, p12486_1, u0elo1]
                                  · have p12486_0 := h12486c.1
                                    have p12486_1 := h12486c.2.1
                                    have p12486_2 := h12486c.2.2.1
                                    have p12486_3 := h12486c.2.2.2
                                    linarith only [hlam, p12486_0]
                                · rcases h2bigk with h12530c | h12530c | h12530c | h12530c | h12530c | h12530c | h12530c | h12530c | h12530c | h12530c | h12530c | h12530c | h12530c | h12530c | h12530c | h12530c | h12530c | h12530c | h12530c | h12530c | h12530c | h12530c | h12530c | h12530c | h12530c
                                  · have p12530_0 := h12530c.1
                                    have p12530_1 := h12530c.2.1
                                    have p12530_2 := h12530c.2.2.1
                                    have p12530_3 := h12530c.2.2.2
                                    linarith only [hlam, p12530_0]
                                  · have p12530_0 := h12530c.1
                                    have p12530_1 := h12530c.2.1
                                    have p12530_2 := h12530c.2.2.1
                                    have p12530_3 := h12530c.2.2.2
                                    linarith only [h0, hlam, p12530_1]
                                  · have p12530_0 := h12530c.1
                                    have p12530_1 := h12530c.2.1
                                    have p12530_2 := h12530c.2.2.1
                                    have p12530_3 := h12530c.2.2.2
                                    linarith only [h12302, hc34, hlam, hphi, ht0b, ht45, ht5b, p12530_1, u0elo1]
                                  · have p12530_0 := h12530c.1
                                    have p12530_1 := h12530c.2.1
                                    have p12530_2 := h12530c.2.2.1
                                    have p12530_3 := h12530c.2.2.2
                                    rcases p12530_3 (m.d 0 2) (by simp) with h12534 | h12534
                                    · rcases p12530_3 (m.d 1 2) (by simp) with h12535 | h12535
                                      · rcases p12530_3 (m.d 2 3) (by simp) with h12536 | h12536
                                        · linarith only [h11558, h12536, hlam]
                                        · linarith only [h12302, h12536, hlam]
                                      · linarith only [h12082, h12535, hlam]
                                    · linarith only [h12534, hlam, p12530_0]
                                  · have p12530_0 := h12530c.1
                                    have p12530_1 := h12530c.2.1
                                    have p12530_2 := h12530c.2.2.1
                                    have p12530_3 := h12530c.2.2.2
                                    rcases p12530_3 (m.d 0 2) (by simp) with h12541 | h12541
                                    · rcases p12530_3 (m.d 1 2) (by simp) with h12542 | h12542
                                      · rcases p12530_3 (m.d 2 3) (by simp) with h12543 | h12543
                                        · linarith only [h11558, h12543, hlam]
                                        · linarith only [h12303, h12543, hlam]
                                      · linarith only [h12083, h12542, hlam]
                                    · linarith only [h12541, hlam, p12530_0]
                                  · have p12530_0 := h12530c.1
                                    have p12530_1 := h12530c.2.1
                                    have p12530_2 := h12530c.2.2.1
                                    have p12530_3 := h12530c.2.2.2
                                    linarith only [h10058, h11558, h11562, hc01, hc12, hlam, hphi, p12308_1, p12530_1]
                                  · have p12530_0 := h12530c.1
                                    have p12530_1 := h12530c.2.1
                                    have p12530_2 := h12530c.2.2.1
                                    have p12530_3 := h12530c.2.2.2
                                    linarith only [hlam, p12530_0]
                                  · have p12530_0 := h12530c.1
                                    have p12530_1 := h12530c.2.1
                                    have p12530_2 := h12530c.2.2.1
                                    have p12530_3 := h12530c.2.2.2
                                    rcases p12530_3 (m.d 0 2) (by simp) with h12550 | h12550
                                    · linarith only [h0, h12550, hlam]
                                    · linarith only [h11558, h12550, hlam]
                                  · have p12530_0 := h12530c.1
                                    have p12530_1 := h12530c.2.1
                                    have p12530_2 := h12530c.2.2.1
                                    have p12530_3 := h12530c.2.2.2
                                    rcases p12530_3 (m.d 0 2) (by simp) with h12553 | h12553
                                    · linarith only [h0, h12553, hlam]
                                    · linarith only [h11559, h12553, hlam]
                                  · have p12530_0 := h12530c.1
                                    have p12530_1 := h12530c.2.1
                                    have p12530_2 := h12530c.2.2.1
                                    have p12530_3 := h12530c.2.2.2
                                    rcases p12530_3 (m.d 0 2) (by simp) with h12556 | h12556
                                    · linarith only [h0, h12556, hlam]
                                    · linarith only [h11560, h12556, hlam]
                                  · have p12530_0 := h12530c.1
                                    have p12530_1 := h12530c.2.1
                                    have p12530_2 := h12530c.2.2.1
                                    have p12530_3 := h12530c.2.2.2
                                    linarith only [h11558, hlam, p12530_0]
                                  · have p12530_0 := h12530c.1
                                    have p12530_1 := h12530c.2.1
                                    have p12530_2 := h12530c.2.2.1
                                    have p12530_3 := h12530c.2.2.2
                                    linarith only [h12081, hlam, p12530_0]
                                  · have p12530_0 := h12530c.1
                                    have p12530_1 := h12530c.2.1
                                    have p12530_2 := h12530c.2.2.1
                                    have p12530_3 := h12530c.2.2.2
                                    linarith only [hlam, p12530_0]
                                  · have p12530_0 := h12530c.1
                                    have p12530_1 := h12530c.2.1
                                    have p12530_2 := h12530c.2.2.1
                                    have p12530_3 := h12530c.2.2.2
                                    linarith only [h11558, hc24, hlam, hphi, ht0b, ht45, ht5b, p12530_1, u0elo1]
                                  · have p12530_0 := h12530c.1
                                    have p12530_1 := h12530c.2.1
                                    have p12530_2 := h12530c.2.2.1
                                    have p12530_3 := h12530c.2.2.2
                                    linarith only [h11558, hc25, hlam, hphi, ht0b, ht5b, p12530_1, u0elo1]
                                  · have p12530_0 := h12530c.1
                                    have p12530_1 := h12530c.2.1
                                    have p12530_2 := h12530c.2.2.1
                                    have p12530_3 := h12530c.2.2.2
                                    linarith only [h11559, hlam, p12530_0]
                                  · have p12530_0 := h12530c.1
                                    have p12530_1 := h12530c.2.1
                                    have p12530_2 := h12530c.2.2.1
                                    have p12530_3 := h12530c.2.2.2
                                    linarith only [h12082, hlam, p12530_0]
                                  · have p12530_0 := h12530c.1
                                    have p12530_1 := h12530c.2.1
                                    have p12530_2 := h12530c.2.2.1
                                    have p12530_3 := h12530c.2.2.2
                                    linarith only [h12302, hlam, p12530_1]
                                  · have p12530_0 := h12530c.1
                                    have p12530_1 := h12530c.2.1
                                    have p12530_2 := h12530c.2.2.1
                                    have p12530_3 := h12530c.2.2.2
                                    linarith only [hlam, p12530_0]
                                  · have p12530_0 := h12530c.1
                                    have p12530_1 := h12530c.2.1
                                    have p12530_2 := h12530c.2.2.1
                                    have p12530_3 := h12530c.2.2.2
                                    linarith only [h12304, hlam, p12530_1]
                                  · have p12530_0 := h12530c.1
                                    have p12530_1 := h12530c.2.1
                                    have p12530_2 := h12530c.2.2.1
                                    have p12530_3 := h12530c.2.2.2
                                    linarith only [h11560, hlam, p12530_0]
                                  · have p12530_0 := h12530c.1
                                    have p12530_1 := h12530c.2.1
                                    have p12530_2 := h12530c.2.2.1
                                    have p12530_3 := h12530c.2.2.2
                                    linarith only [h12083, hlam, p12530_0]
                                  · have p12530_0 := h12530c.1
                                    have p12530_1 := h12530c.2.1
                                    have p12530_2 := h12530c.2.2.1
                                    have p12530_3 := h12530c.2.2.2
                                    linarith only [h12303, hlam, p12530_1]
                                  · have p12530_0 := h12530c.1
                                    have p12530_1 := h12530c.2.1
                                    have p12530_2 := h12530c.2.2.1
                                    have p12530_3 := h12530c.2.2.2
                                    linarith only [h11560, h12302, hc34, hlam, hphi, ht0b, ht45, ht5b, p12530_1, u0elo1]
                                  · have p12530_0 := h12530c.1
                                    have p12530_1 := h12530c.2.1
                                    have p12530_2 := h12530c.2.2.1
                                    have p12530_3 := h12530c.2.2.2
                                    linarith only [hlam, p12530_0]
                                · linarith only [h11558, h11562, h12484, hlam, p12308_1, u0elo1]
                                · rcases h2bigk with h12575c | h12575c | h12575c | h12575c | h12575c | h12575c | h12575c | h12575c | h12575c | h12575c | h12575c | h12575c | h12575c | h12575c | h12575c | h12575c | h12575c | h12575c | h12575c | h12575c | h12575c | h12575c | h12575c | h12575c | h12575c
                                  · have p12575_0 := h12575c.1
                                    have p12575_1 := h12575c.2.1
                                    have p12575_2 := h12575c.2.2.1
                                    have p12575_3 := h12575c.2.2.2
                                    linarith only [hlam, p12575_0]
                                  · have p12575_0 := h12575c.1
                                    have p12575_1 := h12575c.2.1
                                    have p12575_2 := h12575c.2.2.1
                                    have p12575_3 := h12575c.2.2.2
                                    linarith only [h0, hlam, p12575_1]
                                  · have p12575_0 := h12575c.1
                                    have p12575_1 := h12575c.2.1
                                    have p12575_2 := h12575c.2.2.1
                                    have p12575_3 := h12575c.2.2.2
                                    linarith only [h12302, hc34, hlam, hphi, ht0b, ht45, ht5b, p12575_1, u0elo1]
                                  · have p12575_0 := h12575c.1
                                    have p12575_1 := h12575c.2.1
                                    have p12575_2 := h12575c.2.2.1
                                    have p12575_3 := h12575c.2.2.2
                                    rcases p12575_3 (m.d 0 2) (by simp) with h12579 | h12579
                                    · rcases p12575_3 (m.d 1 2) (by simp) with h12580 | h12580
                                      · rcases p12575_3 (m.d 2 3) (by simp) with h12581 | h12581
                                        · linarith only [h11558, h12581, hlam]
                                        · linarith only [h12302, h12581, hlam]
                                      · linarith only [h12082, h12580, hlam]
                                    · linarith only [h12579, hlam, p12575_0]
                                  · have p12575_0 := h12575c.1
                                    have p12575_1 := h12575c.2.1
                                    have p12575_2 := h12575c.2.2.1
                                    have p12575_3 := h12575c.2.2.2
                                    rcases p12575_3 (m.d 0 2) (by simp) with h12586 | h12586
                                    · rcases p12575_3 (m.d 1 2) (by simp) with h12587 | h12587
                                      · rcases p12575_3 (m.d 2 3) (by simp) with h12588 | h12588
                                        · linarith only [h11558, h12588, hlam]
                                        · linarith only [h12303, h12588, hlam]
                                      · linarith only [h12083, h12587, hlam]
                                    · linarith only [h12586, hlam, p12575_0]
                                  · have p12575_0 := h12575c.1
                                    have p12575_1 := h12575c.2.1
                                    have p12575_2 := h12575c.2.2.1
                                    have p12575_3 := h12575c.2.2.2
                                    linarith only [h10058, h11558, h11562, hc01, hc12, hlam, hphi, p12308_1, p12575_1]
                                  · have p12575_0 := h12575c.1
                                    have p12575_1 := h12575c.2.1
                                    have p12575_2 := h12575c.2.2.1
                                    have p12575_3 := h12575c.2.2.2
                                    linarith only [hlam, p12575_0]
                                  · have p12575_0 := h12575c.1
                                    have p12575_1 := h12575c.2.1
                                    have p12575_2 := h12575c.2.2.1
                                    have p12575_3 := h12575c.2.2.2
                                    rcases p12575_3 (m.d 0 2) (by simp) with h12595 | h12595
                                    · linarith only [h0, h12595, hlam]
                                    · linarith only [h11558, h12595, hlam]
                                  · have p12575_0 := h12575c.1
                                    have p12575_1 := h12575c.2.1
                                    have p12575_2 := h12575c.2.2.1
                                    have p12575_3 := h12575c.2.2.2
                                    rcases p12575_3 (m.d 0 2) (by simp) with h12598 | h12598
                                    · linarith only [h0, h12598, hlam]
                                    · linarith only [h11559, h12598, hlam]
                                  · have p12575_0 := h12575c.1
                                    have p12575_1 := h12575c.2.1
                                    have p12575_2 := h12575c.2.2.1
                                    have p12575_3 := h12575c.2.2.2
                                    rcases p12575_3 (m.d 0 2) (by simp) with h12601 | h12601
                                    · linarith only [h0, h12601, hlam]
                                    · linarith only [h11560, h12601, hlam]
                                  · have p12575_0 := h12575c.1
                                    have p12575_1 := h12575c.2.1
                                    have p12575_2 := h12575c.2.2.1
                                    have p12575_3 := h12575c.2.2.2
                                    linarith only [h11558, hlam, p12575_0]
                                  · have p12575_0 := h12575c.1
                                    have p12575_1 := h12575c.2.1
                                    have p12575_2 := h12575c.2.2.1
                                    have p12575_3 := h12575c.2.2.2
                                    linarith only [h12081, hlam, p12575_0]
                                  · have p12575_0 := h12575c.1
                                    have p12575_1 := h12575c.2.1
                                    have p12575_2 := h12575c.2.2.1
                                    have p12575_3 := h12575c.2.2.2
                                    linarith only [hlam, p12575_0]
                                  · have p12575_0 := h12575c.1
                                    have p12575_1 := h12575c.2.1
                                    have p12575_2 := h12575c.2.2.1
                                    have p12575_3 := h12575c.2.2.2
                                    linarith only [h11558, hc24, hlam, hphi, ht0b, ht45, ht5b, p12575_1, u0elo1]
                                  · have p12575_0 := h12575c.1
                                    have p12575_1 := h12575c.2.1
                                    have p12575_2 := h12575c.2.2.1
                                    have p12575_3 := h12575c.2.2.2
                                    linarith only [h11558, hc25, hlam, hphi, ht0b, ht5b, p12575_1, u0elo1]
                                  · have p12575_0 := h12575c.1
                                    have p12575_1 := h12575c.2.1
                                    have p12575_2 := h12575c.2.2.1
                                    have p12575_3 := h12575c.2.2.2
                                    linarith only [h11559, hlam, p12575_0]
                                  · have p12575_0 := h12575c.1
                                    have p12575_1 := h12575c.2.1
                                    have p12575_2 := h12575c.2.2.1
                                    have p12575_3 := h12575c.2.2.2
                                    linarith only [h12082, hlam, p12575_0]
                                  · have p12575_0 := h12575c.1
                                    have p12575_1 := h12575c.2.1
                                    have p12575_2 := h12575c.2.2.1
                                    have p12575_3 := h12575c.2.2.2
                                    linarith only [h12302, hlam, p12575_1]
                                  · have p12575_0 := h12575c.1
                                    have p12575_1 := h12575c.2.1
                                    have p12575_2 := h12575c.2.2.1
                                    have p12575_3 := h12575c.2.2.2
                                    linarith only [hlam, p12575_0]
                                  · have p12575_0 := h12575c.1
                                    have p12575_1 := h12575c.2.1
                                    have p12575_2 := h12575c.2.2.1
                                    have p12575_3 := h12575c.2.2.2
                                    linarith only [h12304, hlam, p12575_1]
                                  · have p12575_0 := h12575c.1
                                    have p12575_1 := h12575c.2.1
                                    have p12575_2 := h12575c.2.2.1
                                    have p12575_3 := h12575c.2.2.2
                                    linarith only [h11560, hlam, p12575_0]
                                  · have p12575_0 := h12575c.1
                                    have p12575_1 := h12575c.2.1
                                    have p12575_2 := h12575c.2.2.1
                                    have p12575_3 := h12575c.2.2.2
                                    linarith only [h12083, hlam, p12575_0]
                                  · have p12575_0 := h12575c.1
                                    have p12575_1 := h12575c.2.1
                                    have p12575_2 := h12575c.2.2.1
                                    have p12575_3 := h12575c.2.2.2
                                    linarith only [h12303, hlam, p12575_1]
                                  · have p12575_0 := h12575c.1
                                    have p12575_1 := h12575c.2.1
                                    have p12575_2 := h12575c.2.2.1
                                    have p12575_3 := h12575c.2.2.2
                                    linarith only [h11560, h12302, hc34, hlam, hphi, ht0b, ht45, ht5b, p12575_1, u0elo1]
                                  · have p12575_0 := h12575c.1
                                    have p12575_1 := h12575c.2.1
                                    have p12575_2 := h12575c.2.2.1
                                    have p12575_3 := h12575c.2.2.2
                                    linarith only [hlam, p12575_0]
                              · linarith only [h11563, h12483, hlam]
                          · linarith only [h11561, h12480, hlam]
                        · linarith only [h11559, h12479, hlam]
                    · have p12308_0 := h12308c.1
                      have p12308_1 := h12308c.2.1
                      have p12308_2 := h12308c.2.2.1
                      have p12308_3 := h12308c.2.2.2
                      linarith only [hlam, p12308_0]
              · linarith only [h11558, h11562, h12302, h12303, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h12624 | h12624
              · linarith only [h11558, h11561, h12302, h12624, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h12626 | h12626
                · linarith only [h10058, h12085, h12626, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h12628 | h12628
                  · linarith only [h10058, h11561, h12085, h12628, hlam]
                  · rcases h0bigk with h12630c | h12630c | h12630c | h12630c | h12630c | h12630c | h12630c | h12630c | h12630c | h12630c | h12630c | h12630c | h12630c | h12630c | h12630c | h12630c | h12630c | h12630c | h12630c | h12630c | h12630c | h12630c | h12630c | h12630c | h12630c
                    · have p12630_0 := h12630c.1
                      have p12630_1 := h12630c.2.1
                      have p12630_2 := h12630c.2.2.1
                      have p12630_3 := h12630c.2.2.2
                      linarith only [hlam, p12630_0]
                    · have p12630_0 := h12630c.1
                      have p12630_1 := h12630c.2.1
                      have p12630_2 := h12630c.2.2.1
                      have p12630_3 := h12630c.2.2.2
                      linarith only [h0, hlam, p12630_1]
                    · have p12630_0 := h12630c.1
                      have p12630_1 := h12630c.2.1
                      have p12630_2 := h12630c.2.2.1
                      have p12630_3 := h12630c.2.2.2
                      linarith only [h6793, hlam, p12630_0]
                    · have p12630_0 := h12630c.1
                      have p12630_1 := h12630c.2.1
                      have p12630_2 := h12630c.2.2.1
                      have p12630_3 := h12630c.2.2.2
                      linarith only [h10058, hlam, p12630_1]
                    · have p12630_0 := h12630c.1
                      have p12630_1 := h12630c.2.1
                      have p12630_2 := h12630c.2.2.1
                      have p12630_3 := h12630c.2.2.2
                      linarith only [h11024, hlam, p12630_1]
                    · have p12630_0 := h12630c.1
                      have p12630_1 := h12630c.2.1
                      have p12630_2 := h12630c.2.2.1
                      have p12630_3 := h12630c.2.2.2
                      rcases p12630_3 (m.d 0 1) (by simp) with h12636 | h12636
                      · linarith only [h0, h12636, hlam]
                      · rcases p12630_3 (m.d 0 2) (by simp) with h12638 | h12638
                        · rcases p12630_3 (m.d 0 3) (by simp) with h12639 | h12639
                          · linarith only [h11558, h12639, hlam]
                          · linarith only [h12639, h6793, hlam]
                        · linarith only [h0, h12638, hlam]
                    · have p12630_0 := h12630c.1
                      have p12630_1 := h12630c.2.1
                      have p12630_2 := h12630c.2.2.1
                      have p12630_3 := h12630c.2.2.2
                      linarith only [hlam, p12630_0]
                    · have p12630_0 := h12630c.1
                      have p12630_1 := h12630c.2.1
                      have p12630_2 := h12630c.2.2.1
                      have p12630_3 := h12630c.2.2.2
                      linarith only [h11562, h12624, hc25, hlam, hphi, ht0b, ht5b, p12630_1, u0elo1]
                    · have p12630_0 := h12630c.1
                      have p12630_1 := h12630c.2.1
                      have p12630_2 := h12630c.2.2.1
                      have p12630_3 := h12630c.2.2.2
                      linarith only [h11561, h12302, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12630_1, u0elo1]
                    · have p12630_0 := h12630c.1
                      have p12630_1 := h12630c.2.1
                      have p12630_2 := h12630c.2.2.1
                      have p12630_3 := h12630c.2.2.2
                      linarith only [h11561, h11563, h12302, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12630_1, u0elo1]
                    · have p12630_0 := h12630c.1
                      have p12630_1 := h12630c.2.1
                      have p12630_2 := h12630c.2.2.1
                      have p12630_3 := h12630c.2.2.2
                      rcases p12630_3 (m.d 0 1) (by simp) with h12647 | h12647
                      · linarith only [h12647, h6793, hlam]
                      · rcases p12630_3 (m.d 0 2) (by simp) with h12649 | h12649
                        · rcases p12630_3 (m.d 0 3) (by simp) with h12650 | h12650
                          · rcases p12630_3 (m.d 0 4) (by simp) with h12651 | h12651
                            · linarith only [h11561, h12651, hlam]
                            · linarith only [h10058, h12651, hlam]
                          · linarith only [h12650, h6793, hlam]
                        · linarith only [h0, h12649, hlam]
                    · have p12630_0 := h12630c.1
                      have p12630_1 := h12630c.2.1
                      have p12630_2 := h12630c.2.2.1
                      have p12630_3 := h12630c.2.2.2
                      linarith only [h11558, hlam, p12630_1]
                    · have p12630_0 := h12630c.1
                      have p12630_1 := h12630c.2.1
                      have p12630_2 := h12630c.2.2.1
                      have p12630_3 := h12630c.2.2.2
                      linarith only [hlam, p12630_0]
                    · have p12630_0 := h12630c.1
                      have p12630_1 := h12630c.2.1
                      have p12630_2 := h12630c.2.2.1
                      have p12630_3 := h12630c.2.2.2
                      linarith only [h11558, h11561, h12302, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12630_1, u0elo1]
                    · have p12630_0 := h12630c.1
                      have p12630_1 := h12630c.2.1
                      have p12630_2 := h12630c.2.2.1
                      have p12630_3 := h12630c.2.2.2
                      linarith only [h11558, h11561, h11563, h12302, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12630_1, u0elo1]
                    · have p12630_0 := h12630c.1
                      have p12630_1 := h12630c.2.1
                      have p12630_2 := h12630c.2.2.1
                      have p12630_3 := h12630c.2.2.2
                      linarith only [h10058, h12085, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p12630_1]
                    · have p12630_0 := h12630c.1
                      have p12630_1 := h12630c.2.1
                      have p12630_2 := h12630c.2.2.1
                      have p12630_3 := h12630c.2.2.2
                      linarith only [h11559, hlam, p12630_0]
                    · have p12630_0 := h12630c.1
                      have p12630_1 := h12630c.2.1
                      have p12630_2 := h12630c.2.2.1
                      have p12630_3 := h12630c.2.2.2
                      linarith only [h11561, hlam, p12630_0]
                    · have p12630_0 := h12630c.1
                      have p12630_1 := h12630c.2.1
                      have p12630_2 := h12630c.2.2.1
                      have p12630_3 := h12630c.2.2.2
                      linarith only [hlam, p12630_0]
                    · have p12630_0 := h12630c.1
                      have p12630_1 := h12630c.2.1
                      have p12630_2 := h12630c.2.2.1
                      have p12630_3 := h12630c.2.2.2
                      linarith only [h11563, hlam, p12630_0]
                    · have p12630_0 := h12630c.1
                      have p12630_1 := h12630c.2.1
                      have p12630_2 := h12630c.2.2.1
                      have p12630_3 := h12630c.2.2.2
                      rcases p12630_3 (m.d 0 1) (by simp) with h12665 | h12665
                      · linarith only [h11024, h12665, hlam]
                      · rcases p12630_3 (m.d 0 2) (by simp) with h12667 | h12667
                        · rcases p12630_3 (m.d 0 3) (by simp) with h12668 | h12668
                          · rcases p12630_3 (m.d 0 4) (by simp) with h12669 | h12669
                            · linarith only [h11563, h12669, hlam]
                            · linarith only [h10058, h12669, hlam]
                          · linarith only [h12668, h6793, hlam]
                        · linarith only [h0, h12667, hlam]
                    · have p12630_0 := h12630c.1
                      have p12630_1 := h12630c.2.1
                      have p12630_2 := h12630c.2.2.1
                      have p12630_3 := h12630c.2.2.2
                      linarith only [h11560, hlam, p12630_1]
                    · have p12630_0 := h12630c.1
                      have p12630_1 := h12630c.2.1
                      have p12630_2 := h12630c.2.2.1
                      have p12630_3 := h12630c.2.2.2
                      linarith only [h11562, hlam, p12630_0]
                    · have p12630_0 := h12630c.1
                      have p12630_1 := h12630c.2.1
                      have p12630_2 := h12630c.2.2.1
                      have p12630_3 := h12630c.2.2.2
                      linarith only [h11558, h11561, h11562, h12302, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p12630_1, u0elo1]
                    · have p12630_0 := h12630c.1
                      have p12630_1 := h12630c.2.1
                      have p12630_2 := h12630c.2.2.1
                      have p12630_3 := h12630c.2.2.2
                      linarith only [hlam, p12630_0]
        · linarith only [h11561, h12084, h6793, hlam]
      · linarith only [h0, h11560, h12083, hlam]
    · linarith only [h0, h11559, h12082, hlam]
  · linarith only [h0, h11558, h12081, hlam]

set_option maxHeartbeats 5504000 in
set_option maxHeartbeats 5504000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s15_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg10058 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11024 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg11558 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg11559 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg11560 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h11561 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h11562 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h11558 := hg11558
  have h11559 := hg11559
  have h11560 := hg11560
  rcases m.htr 0 4 5 (by decide) (by decide) with h11563 | h11563
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s15_x0_x0_x0 m hb0 hb2 hb4 hg0 hg6793 hg10058 hg11024 hg11558 hg11559 hg11560 h11561 h11562 h11563
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s15_x0_x0_x1 m hb0 hb2 hb4 hg0 hg6793 hg10058 hg11024 hg11558 hg11559 hg11560 h11561 h11562 h11563

set_option maxHeartbeats 5504000 in
set_option maxHeartbeats 5504000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s15_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg10058 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11024 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg11558 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg11559 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg11560 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h11561 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h11562 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h11558 := hg11558
  have h11559 := hg11559
  have h11560 := hg11560
  rcases m.htr 0 4 5 (by decide) (by decide) with h12682 | h12682
  · linarith only [h11561, h11562, h12682, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h12684 | h12684
    · rcases m.htr 1 2 4 (by decide) (by decide) with h12685 | h12685
      · rcases m.htr 1 2 5 (by decide) (by decide) with h12686 | h12686
        · rcases m.htr 1 3 4 (by decide) (by decide) with h12687 | h12687
          · rcases m.htr 1 4 5 (by decide) (by decide) with h12688 | h12688
            · rcases m.htr 2 3 4 (by decide) (by decide) with h12689 | h12689
              · rcases m.htr 2 3 5 (by decide) (by decide) with h12690 | h12690
                · linarith only [h11558, h11562, h12690, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h12692 | h12692
                  · linarith only [h11559, h12682, h12692, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h12694 | h12694
                    · linarith only [h10058, h11558, h12682, h12689, h12694, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · rcases h0bigk with h12696c | h12696c | h12696c | h12696c | h12696c | h12696c | h12696c | h12696c | h12696c | h12696c | h12696c | h12696c | h12696c | h12696c | h12696c | h12696c | h12696c | h12696c | h12696c | h12696c | h12696c | h12696c | h12696c | h12696c | h12696c
                      · have p12696_0 := h12696c.1
                        have p12696_1 := h12696c.2.1
                        have p12696_2 := h12696c.2.2.1
                        have p12696_3 := h12696c.2.2.2
                        linarith only [hlam, p12696_0]
                      · have p12696_0 := h12696c.1
                        have p12696_1 := h12696c.2.1
                        have p12696_2 := h12696c.2.2.1
                        have p12696_3 := h12696c.2.2.2
                        linarith only [h0, hlam, p12696_1]
                      · have p12696_0 := h12696c.1
                        have p12696_1 := h12696c.2.1
                        have p12696_2 := h12696c.2.2.1
                        have p12696_3 := h12696c.2.2.2
                        linarith only [h6793, hlam, p12696_0]
                      · have p12696_0 := h12696c.1
                        have p12696_1 := h12696c.2.1
                        have p12696_2 := h12696c.2.2.1
                        have p12696_3 := h12696c.2.2.2
                        linarith only [h10058, hlam, p12696_1]
                      · have p12696_0 := h12696c.1
                        have p12696_1 := h12696c.2.1
                        have p12696_2 := h12696c.2.2.1
                        have p12696_3 := h12696c.2.2.2
                        linarith only [h11024, hlam, p12696_1]
                      · have p12696_0 := h12696c.1
                        have p12696_1 := h12696c.2.1
                        have p12696_2 := h12696c.2.2.1
                        have p12696_3 := h12696c.2.2.2
                        rcases p12696_3 (m.d 0 1) (by simp) with h12702 | h12702
                        · linarith only [h0, h12702, hlam]
                        · rcases p12696_3 (m.d 0 2) (by simp) with h12704 | h12704
                          · rcases p12696_3 (m.d 0 3) (by simp) with h12705 | h12705
                            · linarith only [h11558, h12705, hlam]
                            · linarith only [h12705, h6793, hlam]
                          · linarith only [h0, h12704, hlam]
                      · have p12696_0 := h12696c.1
                        have p12696_1 := h12696c.2.1
                        have p12696_2 := h12696c.2.2.1
                        have p12696_3 := h12696c.2.2.2
                        linarith only [hlam, p12696_0]
                      · have p12696_0 := h12696c.1
                        have p12696_1 := h12696c.2.1
                        have p12696_2 := h12696c.2.2.1
                        have p12696_3 := h12696c.2.2.2
                        linarith only [h11558, h12689, hc34, hlam, hphi, ht0b, ht45, ht5b, p12696_1, u0elo1]
                      · have p12696_0 := h12696c.1
                        have p12696_1 := h12696c.2.1
                        have p12696_2 := h12696c.2.2.1
                        have p12696_3 := h12696c.2.2.2
                        rcases p12696_3 (m.d 0 1) (by simp) with h12711 | h12711
                        · linarith only [h0, h12711, hlam]
                        · rcases p12696_3 (m.d 0 2) (by simp) with h12713 | h12713
                          · rcases p12696_3 (m.d 0 3) (by simp) with h12714 | h12714
                            · linarith only [h11558, h12714, hlam]
                            · linarith only [h11561, h12714, hlam]
                          · linarith only [h11559, h12713, hlam]
                      · have p12696_0 := h12696c.1
                        have p12696_1 := h12696c.2.1
                        have p12696_2 := h12696c.2.2.1
                        have p12696_3 := h12696c.2.2.2
                        linarith only [h11558, h11562, h12689, hc34, hlam, hphi, ht0b, ht45, ht5b, p12696_1, u0elo1]
                      · have p12696_0 := h12696c.1
                        have p12696_1 := h12696c.2.1
                        have p12696_2 := h12696c.2.2.1
                        have p12696_3 := h12696c.2.2.2
                        linarith only [h11562, h12684, h12687, h12688, h12694, hc01, hc12, hlam, hphi, p12696_1]
                      · have p12696_0 := h12696c.1
                        have p12696_1 := h12696c.2.1
                        have p12696_2 := h12696c.2.2.1
                        have p12696_3 := h12696c.2.2.2
                        linarith only [h11558, hlam, p12696_1]
                      · have p12696_0 := h12696c.1
                        have p12696_1 := h12696c.2.1
                        have p12696_2 := h12696c.2.2.1
                        have p12696_3 := h12696c.2.2.2
                        linarith only [hlam, p12696_0]
                      · have p12696_0 := h12696c.1
                        have p12696_1 := h12696c.2.1
                        have p12696_2 := h12696c.2.2.1
                        have p12696_3 := h12696c.2.2.2
                        linarith only [h11562, h12684, h12687, h12688, h12694, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p12696_1]
                      · have p12696_0 := h12696c.1
                        have p12696_1 := h12696c.2.1
                        have p12696_2 := h12696c.2.2.1
                        have p12696_3 := h12696c.2.2.2
                        linarith only [h11562, hlam, p12696_1]
                      · have p12696_0 := h12696c.1
                        have p12696_1 := h12696c.2.1
                        have p12696_2 := h12696c.2.2.1
                        have p12696_3 := h12696c.2.2.2
                        linarith only [h11561, h11562, h12684, h12687, h12688, h12694, hc01, hc12, hlam, hphi, p12696_1]
                      · have p12696_0 := h12696c.1
                        have p12696_1 := h12696c.2.1
                        have p12696_2 := h12696c.2.2.1
                        have p12696_3 := h12696c.2.2.2
                        linarith only [h11559, hlam, p12696_0]
                      · have p12696_0 := h12696c.1
                        have p12696_1 := h12696c.2.1
                        have p12696_2 := h12696c.2.2.1
                        have p12696_3 := h12696c.2.2.2
                        linarith only [h11561, hlam, p12696_0]
                      · have p12696_0 := h12696c.1
                        have p12696_1 := h12696c.2.1
                        have p12696_2 := h12696c.2.2.1
                        have p12696_3 := h12696c.2.2.2
                        linarith only [hlam, p12696_0]
                      · have p12696_0 := h12696c.1
                        have p12696_1 := h12696c.2.1
                        have p12696_2 := h12696c.2.2.1
                        have p12696_3 := h12696c.2.2.2
                        linarith only [h12682, hlam, p12696_0]
                      · have p12696_0 := h12696c.1
                        have p12696_1 := h12696c.2.1
                        have p12696_2 := h12696c.2.2.1
                        have p12696_3 := h12696c.2.2.2
                        linarith only [h11562, h12684, h12687, h12688, h12694, hc01, hc12, hlam, hphi, p12696_1]
                      · have p12696_0 := h12696c.1
                        have p12696_1 := h12696c.2.1
                        have p12696_2 := h12696c.2.2.1
                        have p12696_3 := h12696c.2.2.2
                        linarith only [h11560, hlam, p12696_1]
                      · have p12696_0 := h12696c.1
                        have p12696_1 := h12696c.2.1
                        have p12696_2 := h12696c.2.2.1
                        have p12696_3 := h12696c.2.2.2
                        linarith only [h11562, h12684, h12687, h12688, h12694, h6793, hc01, hc12, hlam, hphi, p12696_1]
                      · have p12696_0 := h12696c.1
                        have p12696_1 := h12696c.2.1
                        have p12696_2 := h12696c.2.2.1
                        have p12696_3 := h12696c.2.2.2
                        linarith only [h10058, h11562, h12684, h12687, h12688, h12694, hc01, hc12, hlam, hphi, p12696_1]
                      · have p12696_0 := h12696c.1
                        have p12696_1 := h12696c.2.1
                        have p12696_2 := h12696c.2.2.1
                        have p12696_3 := h12696c.2.2.2
                        linarith only [hlam, p12696_0]
              · linarith only [h11561, h11562, h12689, hc23, hc35, hlam, hphi]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h12735 | h12735
              · rcases m.htr 2 3 5 (by decide) (by decide) with h12736 | h12736
                · linarith only [h11558, h11562, h12736, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h12738 | h12738
                  · linarith only [h11024, h11559, h12688, h12738, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h12740 | h12740
                    · linarith only [h10058, h11560, h12688, h12735, h12736, h12740, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · rcases h0bigk with h12742c | h12742c | h12742c | h12742c | h12742c | h12742c | h12742c | h12742c | h12742c | h12742c | h12742c | h12742c | h12742c | h12742c | h12742c | h12742c | h12742c | h12742c | h12742c | h12742c | h12742c | h12742c | h12742c | h12742c | h12742c
                      · have p12742_0 := h12742c.1
                        have p12742_1 := h12742c.2.1
                        have p12742_2 := h12742c.2.2.1
                        have p12742_3 := h12742c.2.2.2
                        linarith only [hlam, p12742_0]
                      · have p12742_0 := h12742c.1
                        have p12742_1 := h12742c.2.1
                        have p12742_2 := h12742c.2.2.1
                        have p12742_3 := h12742c.2.2.2
                        linarith only [h0, hlam, p12742_1]
                      · have p12742_0 := h12742c.1
                        have p12742_1 := h12742c.2.1
                        have p12742_2 := h12742c.2.2.1
                        have p12742_3 := h12742c.2.2.2
                        linarith only [h6793, hlam, p12742_0]
                      · have p12742_0 := h12742c.1
                        have p12742_1 := h12742c.2.1
                        have p12742_2 := h12742c.2.2.1
                        have p12742_3 := h12742c.2.2.2
                        linarith only [h10058, hlam, p12742_1]
                      · have p12742_0 := h12742c.1
                        have p12742_1 := h12742c.2.1
                        have p12742_2 := h12742c.2.2.1
                        have p12742_3 := h12742c.2.2.2
                        linarith only [h11024, hlam, p12742_1]
                      · have p12742_0 := h12742c.1
                        have p12742_1 := h12742c.2.1
                        have p12742_2 := h12742c.2.2.1
                        have p12742_3 := h12742c.2.2.2
                        rcases p12742_3 (m.d 0 1) (by simp) with h12748 | h12748
                        · linarith only [h0, h12748, hlam]
                        · rcases p12742_3 (m.d 0 2) (by simp) with h12750 | h12750
                          · rcases p12742_3 (m.d 0 3) (by simp) with h12751 | h12751
                            · linarith only [h11558, h12751, hlam]
                            · linarith only [h12751, h6793, hlam]
                          · linarith only [h0, h12750, hlam]
                      · have p12742_0 := h12742c.1
                        have p12742_1 := h12742c.2.1
                        have p12742_2 := h12742c.2.2.1
                        have p12742_3 := h12742c.2.2.2
                        linarith only [hlam, p12742_0]
                      · have p12742_0 := h12742c.1
                        have p12742_1 := h12742c.2.1
                        have p12742_2 := h12742c.2.2.1
                        have p12742_3 := h12742c.2.2.2
                        linarith only [h11558, h12735, hc34, hlam, hphi, ht0b, ht45, ht5b, p12742_1, u0elo1]
                      · have p12742_0 := h12742c.1
                        have p12742_1 := h12742c.2.1
                        have p12742_2 := h12742c.2.2.1
                        have p12742_3 := h12742c.2.2.2
                        rcases p12742_3 (m.d 0 1) (by simp) with h12757 | h12757
                        · linarith only [h0, h12757, hlam]
                        · rcases p12742_3 (m.d 0 2) (by simp) with h12759 | h12759
                          · rcases p12742_3 (m.d 0 3) (by simp) with h12760 | h12760
                            · linarith only [h11558, h12760, hlam]
                            · linarith only [h11561, h12760, hlam]
                          · linarith only [h11559, h12759, hlam]
                      · have p12742_0 := h12742c.1
                        have p12742_1 := h12742c.2.1
                        have p12742_2 := h12742c.2.2.1
                        have p12742_3 := h12742c.2.2.2
                        linarith only [h11558, h11562, h12735, hc34, hlam, hphi, ht0b, ht45, ht5b, p12742_1, u0elo1]
                      · have p12742_0 := h12742c.1
                        have p12742_1 := h12742c.2.1
                        have p12742_2 := h12742c.2.2.1
                        have p12742_3 := h12742c.2.2.2
                        linarith only [h11562, hc01, hc35, hlam, hphi, ht12, ht23, p12742_1]
                      · have p12742_0 := h12742c.1
                        have p12742_1 := h12742c.2.1
                        have p12742_2 := h12742c.2.2.1
                        have p12742_3 := h12742c.2.2.2
                        linarith only [h11558, hlam, p12742_1]
                      · have p12742_0 := h12742c.1
                        have p12742_1 := h12742c.2.1
                        have p12742_2 := h12742c.2.2.1
                        have p12742_3 := h12742c.2.2.2
                        linarith only [hlam, p12742_0]
                      · have p12742_0 := h12742c.1
                        have p12742_1 := h12742c.2.1
                        have p12742_2 := h12742c.2.2.1
                        have p12742_3 := h12742c.2.2.2
                        linarith only [h10058, h11562, hc01, hc35, hlam, hphi, ht12, ht23, p12742_1]
                      · have p12742_0 := h12742c.1
                        have p12742_1 := h12742c.2.1
                        have p12742_2 := h12742c.2.2.1
                        have p12742_3 := h12742c.2.2.2
                        linarith only [h11562, hlam, p12742_1]
                      · have p12742_0 := h12742c.1
                        have p12742_1 := h12742c.2.1
                        have p12742_2 := h12742c.2.2.1
                        have p12742_3 := h12742c.2.2.2
                        linarith only [h10058, h12688, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p12742_1]
                      · have p12742_0 := h12742c.1
                        have p12742_1 := h12742c.2.1
                        have p12742_2 := h12742c.2.2.1
                        have p12742_3 := h12742c.2.2.2
                        linarith only [h11559, hlam, p12742_0]
                      · have p12742_0 := h12742c.1
                        have p12742_1 := h12742c.2.1
                        have p12742_2 := h12742c.2.2.1
                        have p12742_3 := h12742c.2.2.2
                        linarith only [h11561, hlam, p12742_0]
                      · have p12742_0 := h12742c.1
                        have p12742_1 := h12742c.2.1
                        have p12742_2 := h12742c.2.2.1
                        have p12742_3 := h12742c.2.2.2
                        linarith only [hlam, p12742_0]
                      · have p12742_0 := h12742c.1
                        have p12742_1 := h12742c.2.1
                        have p12742_2 := h12742c.2.2.1
                        have p12742_3 := h12742c.2.2.2
                        linarith only [h12682, hlam, p12742_0]
                      · have p12742_0 := h12742c.1
                        have p12742_1 := h12742c.2.1
                        have p12742_2 := h12742c.2.2.1
                        have p12742_3 := h12742c.2.2.2
                        rcases p12742_3 (m.d 0 1) (by simp) with h12775 | h12775
                        · linarith only [h11024, h12775, hlam]
                        · rcases p12742_3 (m.d 0 2) (by simp) with h12777 | h12777
                          · rcases p12742_3 (m.d 0 3) (by simp) with h12778 | h12778
                            · linarith only [h11562, h12778, hlam]
                            · linarith only [h12778, h6793, hlam]
                          · linarith only [h0, h12777, hlam]
                      · have p12742_0 := h12742c.1
                        have p12742_1 := h12742c.2.1
                        have p12742_2 := h12742c.2.2.1
                        have p12742_3 := h12742c.2.2.2
                        linarith only [h11560, hlam, p12742_1]
                      · have p12742_0 := h12742c.1
                        have p12742_1 := h12742c.2.1
                        have p12742_2 := h12742c.2.2.1
                        have p12742_3 := h12742c.2.2.2
                        linarith only [h11558, h12735, hc34, hlam, hphi, ht0b, ht45, ht5b, p12742_1, u0elo4]
                      · have p12742_0 := h12742c.1
                        have p12742_1 := h12742c.2.1
                        have p12742_2 := h12742c.2.2.1
                        have p12742_3 := h12742c.2.2.2
                        rcases p12742_3 (m.d 0 1) (by simp) with h12784 | h12784
                        · linarith only [h11024, h12784, hlam]
                        · rcases p12742_3 (m.d 0 2) (by simp) with h12786 | h12786
                          · rcases p12742_3 (m.d 0 3) (by simp) with h12787 | h12787
                            · linarith only [h11562, h12787, hlam]
                            · linarith only [h11561, h12787, hlam]
                          · linarith only [h11559, h12786, hlam]
                      · have p12742_0 := h12742c.1
                        have p12742_1 := h12742c.2.1
                        have p12742_2 := h12742c.2.2.1
                        have p12742_3 := h12742c.2.2.2
                        linarith only [hlam, p12742_0]
              · linarith only [h11561, h11562, h12735, hc23, hc35, hlam, hphi]
          · linarith only [h11561, h11562, h12687, hc13, hc35, hlam, hphi]
        · linarith only [h0, h11560, h12686, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
      · linarith only [h0, h11559, h12685, hlam]
    · linarith only [h0, h11558, h12684, hlam]

set_option maxHeartbeats 5504000 in
set_option maxHeartbeats 5504000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s15_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6793 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg10058 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11024 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg11558 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg11559 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg11560 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h11561 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h11558 := hg11558
  have h11559 := hg11559
  have h11560 := hg11560
  rcases m.htr 0 3 5 (by decide) (by decide) with h11562 | h11562
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s15_x0_x0 m hb0 hb2 hb4 hg0 hg6793 hg10058 hg11024 hg11558 hg11559 hg11560 h11561 h11562
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s15_x0_x1 m hb0 hb2 hb4 hg0 hg6793 hg10058 hg11024 hg11558 hg11559 hg11560 h11561 h11562

end R2N4
