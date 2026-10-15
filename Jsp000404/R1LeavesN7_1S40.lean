import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S36
import Jsp000404.R1LeavesN7_1S37
import Jsp000404.R1LeavesN7_1S39

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25423 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25424 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h25425 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h25426 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h25427 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h26147 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  rcases m.htr 2 3 5 (by decide) (by decide) with h26148 | h26148
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147 h26148
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147 h26148

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25423 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25424 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h25425 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h25426 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h25427 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h26147 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  rcases m.htr 2 3 5 (by decide) (by decide) with h27126 | h27126
  · rcases m.htr 2 4 5 (by decide) (by decide) with h27127 | h27127
    · linarith only [h18443, h22353, h25427, h26147, h27126, h27127, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
    · linarith only [h26147, h27126, h27127, hlam]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h27130 | h27130
    · linarith only [h18443, h25427, h27130, hc01, hc24, hlam, hphi, ht12]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h27132 | h27132
      · linarith only [h18443, h22353, h25427, h27132, hlam]
      · rcases h0bigk with h27134c | h27134c | h27134c | h27134c | h27134c | h27134c | h27134c | h27134c | h27134c | h27134c | h27134c | h27134c | h27134c | h27134c | h27134c | h27134c | h27134c | h27134c | h27134c | h27134c | h27134c | h27134c | h27134c | h27134c | h27134c
        · have p27134_0 := h27134c.1
          have p27134_1 := h27134c.2.1
          have p27134_2 := h27134c.2.2.1
          have p27134_3 := h27134c.2.2.2
          linarith only [hlam, p27134_0]
        · have p27134_0 := h27134c.1
          have p27134_1 := h27134c.2.1
          have p27134_2 := h27134c.2.2.1
          have p27134_3 := h27134c.2.2.2
          linarith only [h0, hlam, p27134_1]
        · have p27134_0 := h27134c.1
          have p27134_1 := h27134c.2.1
          have p27134_2 := h27134c.2.2.1
          have p27134_3 := h27134c.2.2.2
          linarith only [h15532, hlam, p27134_0]
        · have p27134_0 := h27134c.1
          have p27134_1 := h27134c.2.1
          have p27134_2 := h27134c.2.2.1
          have p27134_3 := h27134c.2.2.2
          linarith only [h18443, hlam, p27134_1]
        · have p27134_0 := h27134c.1
          have p27134_1 := h27134c.2.1
          have p27134_2 := h27134c.2.2.1
          have p27134_3 := h27134c.2.2.2
          linarith only [h20697, hlam, p27134_1]
        · have p27134_0 := h27134c.1
          have p27134_1 := h27134c.2.1
          have p27134_2 := h27134c.2.2.1
          have p27134_3 := h27134c.2.2.2
          rcases p27134_3 (m.d 0 1) (by simp) with h27140 | h27140
          · linarith only [h0, h27140, hlam]
          · rcases p27134_3 (m.d 0 2) (by simp) with h27142 | h27142
            · rcases p27134_3 (m.d 0 3) (by simp) with h27143 | h27143
              · linarith only [h22350, h27143, hlam]
              · linarith only [h15532, h27143, hlam]
            · linarith only [h0, h27142, hlam]
        · have p27134_0 := h27134c.1
          have p27134_1 := h27134c.2.1
          have p27134_2 := h27134c.2.2.1
          have p27134_3 := h27134c.2.2.2
          linarith only [hlam, p27134_0]
        · have p27134_0 := h27134c.1
          have p27134_1 := h27134c.2.1
          have p27134_2 := h27134c.2.2.1
          have p27134_3 := h27134c.2.2.2
          linarith only [h0, h22353, h26147, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p27134_1]
        · have p27134_0 := h27134c.1
          have p27134_1 := h27134c.2.1
          have p27134_2 := h27134c.2.2.1
          have p27134_3 := h27134c.2.2.2
          rcases p27134_3 (m.d 0 1) (by simp) with h27149 | h27149
          · linarith only [h0, h27149, hlam]
          · rcases p27134_3 (m.d 0 2) (by simp) with h27151 | h27151
            · rcases p27134_3 (m.d 0 3) (by simp) with h27152 | h27152
              · linarith only [h22350, h27152, hlam]
              · linarith only [h22353, h27152, hlam]
            · linarith only [h22351, h27151, hlam]
        · have p27134_0 := h27134c.1
          have p27134_1 := h27134c.2.1
          have p27134_2 := h27134c.2.2.1
          have p27134_3 := h27134c.2.2.2
          rcases p27134_3 (m.d 0 1) (by simp) with h27156 | h27156
          · linarith only [h0, h27156, hlam]
          · rcases p27134_3 (m.d 0 2) (by simp) with h27158 | h27158
            · rcases p27134_3 (m.d 0 3) (by simp) with h27159 | h27159
              · linarith only [h22350, h27159, hlam]
              · linarith only [h22354, h27159, hlam]
            · linarith only [h22352, h27158, hlam]
        · have p27134_0 := h27134c.1
          have p27134_1 := h27134c.2.1
          have p27134_2 := h27134c.2.2.1
          have p27134_3 := h27134c.2.2.2
          rcases p27134_3 (m.d 0 1) (by simp) with h27163 | h27163
          · linarith only [h15532, h27163, hlam]
          · rcases p27134_3 (m.d 0 2) (by simp) with h27165 | h27165
            · rcases p27134_3 (m.d 0 3) (by simp) with h27166 | h27166
              · rcases p27134_3 (m.d 0 4) (by simp) with h27167 | h27167
                · linarith only [h22353, h27167, hlam]
                · linarith only [h18443, h27167, hlam]
              · linarith only [h15532, h27166, hlam]
            · linarith only [h0, h27165, hlam]
        · have p27134_0 := h27134c.1
          have p27134_1 := h27134c.2.1
          have p27134_2 := h27134c.2.2.1
          have p27134_3 := h27134c.2.2.2
          linarith only [h22350, hlam, p27134_1]
        · have p27134_0 := h27134c.1
          have p27134_1 := h27134c.2.1
          have p27134_2 := h27134c.2.2.1
          have p27134_3 := h27134c.2.2.2
          linarith only [hlam, p27134_0]
        · have p27134_0 := h27134c.1
          have p27134_1 := h27134c.2.1
          have p27134_2 := h27134c.2.2.1
          have p27134_3 := h27134c.2.2.2
          rcases p27134_3 (m.d 0 1) (by simp) with h27174 | h27174
          · linarith only [h15532, h27174, hlam]
          · rcases p27134_3 (m.d 0 2) (by simp) with h27176 | h27176
            · rcases p27134_3 (m.d 0 3) (by simp) with h27177 | h27177
              · rcases p27134_3 (m.d 0 4) (by simp) with h27178 | h27178
                · linarith only [h22353, h27178, hlam]
                · rcases p27134_3 (m.d 0 5) (by simp) with h27180 | h27180
                  · linarith only [h22354, h27180, hlam]
                  · linarith only [h22355, h27180, hlam]
              · linarith only [h22353, h27177, hlam]
            · linarith only [h22351, h27176, hlam]
        · have p27134_0 := h27134c.1
          have p27134_1 := h27134c.2.1
          have p27134_2 := h27134c.2.2.1
          have p27134_3 := h27134c.2.2.2
          rcases p27134_3 (m.d 0 1) (by simp) with h27185 | h27185
          · linarith only [h15532, h27185, hlam]
          · rcases p27134_3 (m.d 0 2) (by simp) with h27187 | h27187
            · rcases p27134_3 (m.d 0 3) (by simp) with h27188 | h27188
              · rcases p27134_3 (m.d 0 4) (by simp) with h27189 | h27189
                · linarith only [h22353, h27189, hlam]
                · rcases p27134_3 (m.d 0 5) (by simp) with h27191 | h27191
                  · linarith only [h22354, h27191, hlam]
                  · rcases h2bigk with h27193c | h27193c | h27193c | h27193c | h27193c | h27193c | h27193c | h27193c | h27193c | h27193c | h27193c | h27193c | h27193c | h27193c | h27193c | h27193c | h27193c | h27193c | h27193c | h27193c | h27193c | h27193c | h27193c | h27193c | h27193c
                    · have p27193_0 := h27193c.1
                      have p27193_1 := h27193c.2.1
                      have p27193_2 := h27193c.2.2.1
                      have p27193_3 := h27193c.2.2.2
                      linarith only [hlam, p27193_0]
                    · have p27193_0 := h27193c.1
                      have p27193_1 := h27193c.2.1
                      have p27193_2 := h27193c.2.2.1
                      have p27193_3 := h27193c.2.2.2
                      linarith only [h0, hlam, p27193_1]
                    · have p27193_0 := h27193c.1
                      have p27193_1 := h27193c.2.1
                      have p27193_2 := h27193c.2.2.1
                      have p27193_3 := h27193c.2.2.2
                      linarith only [h22350, h22353, h22355, h26147, hlam, p27134_1, p27193_2]
                    · have p27193_0 := h27193c.1
                      have p27193_1 := h27193c.2.1
                      have p27193_2 := h27193c.2.2.1
                      have p27193_3 := h27193c.2.2.2
                      rcases p27193_3 (m.d 0 2) (by simp) with h27197 | h27197
                      · rcases p27193_3 (m.d 1 2) (by simp) with h27198 | h27198
                        · rcases p27193_3 (m.d 2 3) (by simp) with h27199 | h27199
                          · linarith only [h22350, h27199, hlam]
                          · rcases p27193_3 (m.d 2 4) (by simp) with h27201 | h27201
                            · linarith only [h27201, hlam, p27193_0]
                            · rcases p27193_3 (m.d 2 5) (by simp) with h27203 | h27203
                              · linarith only [h22352, h27203, hlam]
                              · linarith only [h27130, h27203, hlam]
                        · linarith only [h25423, h27198, hlam]
                      · linarith only [h27197, hlam, p27193_0]
                    · have p27193_0 := h27193c.1
                      have p27193_1 := h27193c.2.1
                      have p27193_2 := h27193c.2.2.1
                      have p27193_3 := h27193c.2.2.2
                      rcases p27193_3 (m.d 0 2) (by simp) with h27208 | h27208
                      · rcases p27193_3 (m.d 1 2) (by simp) with h27209 | h27209
                        · rcases p27193_3 (m.d 2 3) (by simp) with h27210 | h27210
                          · linarith only [h22350, h27210, hlam]
                          · rcases p27193_3 (m.d 2 4) (by simp) with h27212 | h27212
                            · linarith only [h22351, h27212, hlam]
                            · rcases p27193_3 (m.d 2 5) (by simp) with h27214 | h27214
                              · linarith only [h27214, hlam, p27193_0]
                              · rcases h3bigk with h27216c | h27216c | h27216c | h27216c | h27216c | h27216c | h27216c | h27216c | h27216c | h27216c | h27216c | h27216c | h27216c | h27216c | h27216c | h27216c | h27216c | h27216c | h27216c | h27216c | h27216c | h27216c | h27216c | h27216c | h27216c
                                · have p27216_0 := h27216c.1
                                  have p27216_1 := h27216c.2.1
                                  have p27216_2 := h27216c.2.2.1
                                  have p27216_3 := h27216c.2.2.2
                                  linarith only [hlam, p27216_0]
                                · have p27216_0 := h27216c.1
                                  have p27216_1 := h27216c.2.1
                                  have p27216_2 := h27216c.2.2.1
                                  have p27216_3 := h27216c.2.2.2
                                  linarith only [h15532, hlam, p27216_1]
                                · have p27216_0 := h27216c.1
                                  have p27216_1 := h27216c.2.1
                                  have p27216_2 := h27216c.2.2.1
                                  have p27216_3 := h27216c.2.2.2
                                  linarith only [h22353, h22355, h26147, hlam, p27134_1, p27216_2]
                                · have p27216_0 := h27216c.1
                                  have p27216_1 := h27216c.2.1
                                  have p27216_2 := h27216c.2.2.1
                                  have p27216_3 := h27216c.2.2.2
                                  rcases p27216_3 (m.d 0 3) (by simp) with h27220 | h27220
                                  · rcases p27216_3 (m.d 1 3) (by simp) with h27221 | h27221
                                    · rcases p27216_3 (m.d 2 3) (by simp) with h27222 | h27222
                                      · linarith only [h22350, h27222, hlam]
                                      · rcases p27216_3 (m.d 3 4) (by simp) with h27224 | h27224
                                        · linarith only [h27224, hlam, p27216_0]
                                        · rcases p27216_3 (m.d 3 5) (by simp) with h27226 | h27226
                                          · linarith only [h22354, h27226, hlam]
                                          · linarith only [h27132, h27226, hlam]
                                    · linarith only [h25425, h27221, hlam]
                                  · linarith only [h27220, hlam, p27216_0]
                                · have p27216_0 := h27216c.1
                                  have p27216_1 := h27216c.2.1
                                  have p27216_2 := h27216c.2.2.1
                                  have p27216_3 := h27216c.2.2.2
                                  rcases p27216_3 (m.d 0 3) (by simp) with h27231 | h27231
                                  · rcases p27216_3 (m.d 1 3) (by simp) with h27232 | h27232
                                    · rcases p27216_3 (m.d 2 3) (by simp) with h27233 | h27233
                                      · linarith only [h22350, h27233, hlam]
                                      · rcases p27216_3 (m.d 3 4) (by simp) with h27235 | h27235
                                        · linarith only [h22353, h27235, hlam]
                                        · rcases p27216_3 (m.d 3 5) (by simp) with h27237 | h27237
                                          · linarith only [h27237, hlam, p27216_0]
                                          · rcases h5bigk with h27239c | h27239c | h27239c | h27239c | h27239c | h27239c | h27239c | h27239c | h27239c | h27239c | h27239c | h27239c | h27239c | h27239c | h27239c | h27239c | h27239c | h27239c | h27239c | h27239c | h27239c | h27239c | h27239c | h27239c | h27239c
                                            · have p27239_0 := h27239c.1
                                              have p27239_1 := h27239c.2.1
                                              have p27239_2 := h27239c.2.2.1
                                              have p27239_3 := h27239c.2.2.2
                                              linarith only [hlam, p27239_0]
                                            · have p27239_0 := h27239c.1
                                              have p27239_1 := h27239c.2.1
                                              have p27239_2 := h27239c.2.2.1
                                              have p27239_3 := h27239c.2.2.2
                                              linarith only [h20697, hlam, p27239_1]
                                            · have p27239_0 := h27239c.1
                                              have p27239_1 := h27239c.2.1
                                              have p27239_2 := h27239c.2.2.1
                                              have p27239_3 := h27239c.2.2.2
                                              linarith only [h22350, hc02, hc25, hlam, hphi, ht0b, ht5b, p27134_1, p27239_1]
                                            · have p27239_0 := h27239c.1
                                              have p27239_1 := h27239c.2.1
                                              have p27239_2 := h27239c.2.2.1
                                              have p27239_3 := h27239c.2.2.2
                                              linarith only [h22350, hc02, hc35, hlam, hphi, ht0b, ht5b, p27134_1, p27239_1]
                                            · have p27239_0 := h27239c.1
                                              have p27239_1 := h27239c.2.1
                                              have p27239_2 := h27239c.2.2.1
                                              have p27239_3 := h27239c.2.2.2
                                              linarith only [h22355, hlam, p27239_1]
                                            · have p27239_0 := h27239c.1
                                              have p27239_1 := h27239c.2.1
                                              have p27239_2 := h27239c.2.2.1
                                              have p27239_3 := h27239c.2.2.2
                                              linarith only [h20697, hc01, hc15, hlam, hphi, p27239_1]
                                            · have p27239_0 := h27239c.1
                                              have p27239_1 := h27239c.2.1
                                              have p27239_2 := h27239c.2.2.1
                                              have p27239_3 := h27239c.2.2.2
                                              linarith only [hlam, p27239_0]
                                            · have p27239_0 := h27239c.1
                                              have p27239_1 := h27239c.2.1
                                              have p27239_2 := h27239c.2.2.1
                                              have p27239_3 := h27239c.2.2.2
                                              linarith only [h22350, h22353, h22355, h25427, h26147, hc23, hc45, hlam, hphi, ht34, p27134_1, p27193_2, p27239_1]
                                            · have p27239_0 := h27239c.1
                                              have p27239_1 := h27239c.2.1
                                              have p27239_2 := h27239c.2.2.1
                                              have p27239_3 := h27239c.2.2.2
                                              linarith only [h22353, h22355, h25427, h26147, hc23, hc45, hlam, hphi, ht34, p27134_1, p27216_2, p27239_1]
                                            · have p27239_0 := h27239c.1
                                              have p27239_1 := h27239c.2.1
                                              have p27239_2 := h27239c.2.2.1
                                              have p27239_3 := h27239c.2.2.2
                                              linarith only [h25427, hlam, p27239_1]
                                            · have p27239_0 := h27239c.1
                                              have p27239_1 := h27239c.2.1
                                              have p27239_2 := h27239c.2.2.1
                                              have p27239_3 := h27239c.2.2.2
                                              linarith only [h22352, hlam, p27239_1]
                                            · have p27239_0 := h27239c.1
                                              have p27239_1 := h27239c.2.1
                                              have p27239_2 := h27239c.2.2.1
                                              have p27239_3 := h27239c.2.2.2
                                              linarith only [h25424, hlam, p27239_1]
                                            · have p27239_0 := h27239c.1
                                              have p27239_1 := h27239c.2.1
                                              have p27239_2 := h27239c.2.2.1
                                              have p27239_3 := h27239c.2.2.2
                                              linarith only [hlam, p27239_0]
                                            · have p27239_0 := h27239c.1
                                              have p27239_1 := h27239c.2.1
                                              have p27239_2 := h27239c.2.2.1
                                              have p27239_3 := h27239c.2.2.2
                                              linarith only [h27126, hlam, p27239_1]
                                            · have p27239_0 := h27239c.1
                                              have p27239_1 := h27239c.2.1
                                              have p27239_2 := h27239c.2.2.1
                                              have p27239_3 := h27239c.2.2.2
                                              linarith only [h27130, hlam, p27239_1]
                                            · have p27239_0 := h27239c.1
                                              have p27239_1 := h27239c.2.1
                                              have p27239_2 := h27239c.2.2.1
                                              have p27239_3 := h27239c.2.2.2
                                              linarith only [h22354, hlam, p27239_0]
                                            · have p27239_0 := h27239c.1
                                              have p27239_1 := h27239c.2.1
                                              have p27239_2 := h27239c.2.2.1
                                              have p27239_3 := h27239c.2.2.2
                                              linarith only [h25426, hlam, p27239_0]
                                            · have p27239_0 := h27239c.1
                                              have p27239_1 := h27239c.2.1
                                              have p27239_2 := h27239c.2.2.1
                                              have p27239_3 := h27239c.2.2.2
                                              linarith only [h22350, h22353, h22355, h26147, hc23, hc35, hlam, hphi, p27134_1, p27193_2, p27239_1]
                                            · have p27239_0 := h27239c.1
                                              have p27239_1 := h27239c.2.1
                                              have p27239_2 := h27239c.2.2.1
                                              have p27239_3 := h27239c.2.2.2
                                              linarith only [hlam, p27239_0]
                                            · have p27239_0 := h27239c.1
                                              have p27239_1 := h27239c.2.1
                                              have p27239_2 := h27239c.2.2.1
                                              have p27239_3 := h27239c.2.2.2
                                              linarith only [h27132, hlam, p27239_1]
                                            · have p27239_0 := h27239c.1
                                              have p27239_1 := h27239c.2.1
                                              have p27239_2 := h27239c.2.2.1
                                              have p27239_3 := h27239c.2.2.2
                                              linarith only [h22353, h22355, h26147, hc23, hc45, hlam, hphi, ht34, p27239_1]
                                            · have p27239_0 := h27239c.1
                                              have p27239_1 := h27239c.2.1
                                              have p27239_2 := h27239c.2.2.1
                                              have p27239_3 := h27239c.2.2.2
                                              linarith only [h20697, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p27239_1]
                                            · have p27239_0 := h27239c.1
                                              have p27239_1 := h27239c.2.1
                                              have p27239_2 := h27239c.2.2.1
                                              have p27239_3 := h27239c.2.2.2
                                              linarith only [h22350, h22353, h22355, h26147, hc23, hc45, hlam, hphi, ht34, p27134_1, p27193_2, p27239_1]
                                            · have p27239_0 := h27239c.1
                                              have p27239_1 := h27239c.2.1
                                              have p27239_2 := h27239c.2.2.1
                                              have p27239_3 := h27239c.2.2.2
                                              linarith only [h22353, h22355, h26147, hc23, hc45, hlam, hphi, ht34, p27134_1, p27216_2, p27239_1]
                                            · have p27239_0 := h27239c.1
                                              have p27239_1 := h27239c.2.1
                                              have p27239_2 := h27239c.2.2.1
                                              have p27239_3 := h27239c.2.2.2
                                              linarith only [hlam, p27239_0]
                                    · linarith only [h25426, h27232, hlam]
                                  · linarith only [h27231, hlam, p27216_0]
                                · have p27216_0 := h27216c.1
                                  have p27216_1 := h27216c.2.1
                                  have p27216_2 := h27216c.2.2.1
                                  have p27216_3 := h27216c.2.2.2
                                  linarith only [h22353, h22355, h25422, h26147, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p27134_1, p27216_1]
                                · have p27216_0 := h27216c.1
                                  have p27216_1 := h27216c.2.1
                                  have p27216_2 := h27216c.2.2.1
                                  have p27216_3 := h27216c.2.2.2
                                  linarith only [hlam, p27216_0]
                                · have p27216_0 := h27216c.1
                                  have p27216_1 := h27216c.2.1
                                  have p27216_2 := h27216c.2.2.1
                                  have p27216_3 := h27216c.2.2.2
                                  linarith only [h15532, h22353, h22355, h26147, hlam, p27134_1, p27216_2]
                                · have p27216_0 := h27216c.1
                                  have p27216_1 := h27216c.2.1
                                  have p27216_2 := h27216c.2.2.1
                                  have p27216_3 := h27216c.2.2.2
                                  rcases p27216_3 (m.d 0 3) (by simp) with h27270 | h27270
                                  · linarith only [h15532, h27270, hlam]
                                  · linarith only [h22353, h27270, hlam]
                                · have p27216_0 := h27216c.1
                                  have p27216_1 := h27216c.2.1
                                  have p27216_2 := h27216c.2.2.1
                                  have p27216_3 := h27216c.2.2.2
                                  rcases p27216_3 (m.d 0 3) (by simp) with h27273 | h27273
                                  · linarith only [h15532, h27273, hlam]
                                  · linarith only [h22354, h27273, hlam]
                                · have p27216_0 := h27216c.1
                                  have p27216_1 := h27216c.2.1
                                  have p27216_2 := h27216c.2.2.1
                                  have p27216_3 := h27216c.2.2.2
                                  linarith only [h22350, hlam, p27216_0]
                                · have p27216_0 := h27216c.1
                                  have p27216_1 := h27216c.2.1
                                  have p27216_2 := h27216c.2.2.1
                                  have p27216_3 := h27216c.2.2.2
                                  linarith only [h25422, hlam, p27216_0]
                                · have p27216_0 := h27216c.1
                                  have p27216_1 := h27216c.2.1
                                  have p27216_2 := h27216c.2.2.1
                                  have p27216_3 := h27216c.2.2.2
                                  linarith only [hlam, p27216_0]
                                · have p27216_0 := h27216c.1
                                  have p27216_1 := h27216c.2.1
                                  have p27216_2 := h27216c.2.2.1
                                  have p27216_3 := h27216c.2.2.2
                                  linarith only [h26147, hlam, p27216_0]
                                · have p27216_0 := h27216c.1
                                  have p27216_1 := h27216c.2.1
                                  have p27216_2 := h27216c.2.2.1
                                  have p27216_3 := h27216c.2.2.2
                                  linarith only [h27126, hlam, p27216_0]
                                · have p27216_0 := h27216c.1
                                  have p27216_1 := h27216c.2.1
                                  have p27216_2 := h27216c.2.2.1
                                  have p27216_3 := h27216c.2.2.2
                                  linarith only [h22353, hlam, p27216_0]
                                · have p27216_0 := h27216c.1
                                  have p27216_1 := h27216c.2.1
                                  have p27216_2 := h27216c.2.2.1
                                  have p27216_3 := h27216c.2.2.2
                                  linarith only [h25425, hlam, p27216_0]
                                · have p27216_0 := h27216c.1
                                  have p27216_1 := h27216c.2.1
                                  have p27216_2 := h27216c.2.2.1
                                  have p27216_3 := h27216c.2.2.2
                                  linarith only [h22350, h22353, h22355, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p27134_1, p27216_1]
                                · have p27216_0 := h27216c.1
                                  have p27216_1 := h27216c.2.1
                                  have p27216_2 := h27216c.2.2.1
                                  have p27216_3 := h27216c.2.2.2
                                  linarith only [hlam, p27216_0]
                                · have p27216_0 := h27216c.1
                                  have p27216_1 := h27216c.2.1
                                  have p27216_2 := h27216c.2.2.1
                                  have p27216_3 := h27216c.2.2.2
                                  linarith only [h27132, hlam, p27216_1]
                                · have p27216_0 := h27216c.1
                                  have p27216_1 := h27216c.2.1
                                  have p27216_2 := h27216c.2.2.1
                                  have p27216_3 := h27216c.2.2.2
                                  linarith only [h22354, hlam, p27216_0]
                                · have p27216_0 := h27216c.1
                                  have p27216_1 := h27216c.2.1
                                  have p27216_2 := h27216c.2.2.1
                                  have p27216_3 := h27216c.2.2.2
                                  linarith only [h25426, hlam, p27216_0]
                                · have p27216_0 := h27216c.1
                                  have p27216_1 := h27216c.2.1
                                  have p27216_2 := h27216c.2.2.1
                                  have p27216_3 := h27216c.2.2.2
                                  linarith only [h0, h22350, h22354, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p27134_1, p27216_1]
                                · have p27216_0 := h27216c.1
                                  have p27216_1 := h27216c.2.1
                                  have p27216_2 := h27216c.2.2.1
                                  have p27216_3 := h27216c.2.2.2
                                  linarith only [h0, h22350, h22354, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p27134_1, p27216_1]
                                · have p27216_0 := h27216c.1
                                  have p27216_1 := h27216c.2.1
                                  have p27216_2 := h27216c.2.2.1
                                  have p27216_3 := h27216c.2.2.2
                                  linarith only [hlam, p27216_0]
                        · linarith only [h25424, h27209, hlam]
                      · linarith only [h27208, hlam, p27193_0]
                    · have p27193_0 := h27193c.1
                      have p27193_1 := h27193c.2.1
                      have p27193_2 := h27193c.2.2.1
                      have p27193_3 := h27193c.2.2.2
                      linarith only [h22350, h22355, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p27134_1, p27193_1]
                    · have p27193_0 := h27193c.1
                      have p27193_1 := h27193c.2.1
                      have p27193_2 := h27193c.2.2.1
                      have p27193_3 := h27193c.2.2.2
                      linarith only [hlam, p27193_0]
                    · have p27193_0 := h27193c.1
                      have p27193_1 := h27193c.2.1
                      have p27193_2 := h27193c.2.2.1
                      have p27193_3 := h27193c.2.2.2
                      linarith only [h0, h22350, h22353, h22355, h26147, hlam, p27134_1, p27193_2]
                    · have p27193_0 := h27193c.1
                      have p27193_1 := h27193c.2.1
                      have p27193_2 := h27193c.2.2.1
                      have p27193_3 := h27193c.2.2.2
                      rcases p27193_3 (m.d 0 2) (by simp) with h27296 | h27296
                      · linarith only [h0, h27296, hlam]
                      · linarith only [h22351, h27296, hlam]
                    · have p27193_0 := h27193c.1
                      have p27193_1 := h27193c.2.1
                      have p27193_2 := h27193c.2.2.1
                      have p27193_3 := h27193c.2.2.2
                      rcases p27193_3 (m.d 0 2) (by simp) with h27299 | h27299
                      · linarith only [h0, h27299, hlam]
                      · linarith only [h22352, h27299, hlam]
                    · have p27193_0 := h27193c.1
                      have p27193_1 := h27193c.2.1
                      have p27193_2 := h27193c.2.2.1
                      have p27193_3 := h27193c.2.2.2
                      linarith only [h22350, hlam, p27193_0]
                    · have p27193_0 := h27193c.1
                      have p27193_1 := h27193c.2.1
                      have p27193_2 := h27193c.2.2.1
                      have p27193_3 := h27193c.2.2.2
                      linarith only [h25422, hlam, p27193_0]
                    · have p27193_0 := h27193c.1
                      have p27193_1 := h27193c.2.1
                      have p27193_2 := h27193c.2.2.1
                      have p27193_3 := h27193c.2.2.2
                      linarith only [hlam, p27193_0]
                    · have p27193_0 := h27193c.1
                      have p27193_1 := h27193c.2.1
                      have p27193_2 := h27193c.2.2.1
                      have p27193_3 := h27193c.2.2.2
                      linarith only [h26147, hlam, p27193_0]
                    · have p27193_0 := h27193c.1
                      have p27193_1 := h27193c.2.1
                      have p27193_2 := h27193c.2.2.1
                      have p27193_3 := h27193c.2.2.2
                      linarith only [h27126, hlam, p27193_0]
                    · have p27193_0 := h27193c.1
                      have p27193_1 := h27193c.2.1
                      have p27193_2 := h27193c.2.2.1
                      have p27193_3 := h27193c.2.2.2
                      linarith only [h22351, hlam, p27193_0]
                    · have p27193_0 := h27193c.1
                      have p27193_1 := h27193c.2.1
                      have p27193_2 := h27193c.2.2.1
                      have p27193_3 := h27193c.2.2.2
                      linarith only [h25423, hlam, p27193_0]
                    · have p27193_0 := h27193c.1
                      have p27193_1 := h27193c.2.1
                      have p27193_2 := h27193c.2.2.1
                      have p27193_3 := h27193c.2.2.2
                      linarith only [h22350, h22351, h22355, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p27134_1, p27193_1]
                    · have p27193_0 := h27193c.1
                      have p27193_1 := h27193c.2.1
                      have p27193_2 := h27193c.2.2.1
                      have p27193_3 := h27193c.2.2.2
                      linarith only [hlam, p27193_0]
                    · have p27193_0 := h27193c.1
                      have p27193_1 := h27193c.2.1
                      have p27193_2 := h27193c.2.2.1
                      have p27193_3 := h27193c.2.2.2
                      linarith only [h27130, hlam, p27193_1]
                    · have p27193_0 := h27193c.1
                      have p27193_1 := h27193c.2.1
                      have p27193_2 := h27193c.2.2.1
                      have p27193_3 := h27193c.2.2.2
                      linarith only [h22352, hlam, p27193_0]
                    · have p27193_0 := h27193c.1
                      have p27193_1 := h27193c.2.1
                      have p27193_2 := h27193c.2.2.1
                      have p27193_3 := h27193c.2.2.2
                      linarith only [h25424, hlam, p27193_0]
                    · have p27193_0 := h27193c.1
                      have p27193_1 := h27193c.2.1
                      have p27193_2 := h27193c.2.2.1
                      have p27193_3 := h27193c.2.2.2
                      linarith only [h0, h22350, h22352, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p27134_1, p27193_1]
                    · have p27193_0 := h27193c.1
                      have p27193_1 := h27193c.2.1
                      have p27193_2 := h27193c.2.2.1
                      have p27193_3 := h27193c.2.2.2
                      linarith only [h0, h22350, h22354, h27126, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p27134_1, p27193_1]
                    · have p27193_0 := h27193c.1
                      have p27193_1 := h27193c.2.1
                      have p27193_2 := h27193c.2.2.1
                      have p27193_3 := h27193c.2.2.2
                      linarith only [hlam, p27193_0]
              · linarith only [h22354, h27188, hlam]
            · linarith only [h22352, h27187, hlam]
        · have p27134_0 := h27134c.1
          have p27134_1 := h27134c.2.1
          have p27134_2 := h27134c.2.2.1
          have p27134_3 := h27134c.2.2.2
          linarith only [h18443, h25427, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p27134_1]
        · have p27134_0 := h27134c.1
          have p27134_1 := h27134c.2.1
          have p27134_2 := h27134c.2.2.1
          have p27134_3 := h27134c.2.2.2
          linarith only [h22351, hlam, p27134_0]
        · have p27134_0 := h27134c.1
          have p27134_1 := h27134c.2.1
          have p27134_2 := h27134c.2.2.1
          have p27134_3 := h27134c.2.2.2
          linarith only [h22353, hlam, p27134_0]
        · have p27134_0 := h27134c.1
          have p27134_1 := h27134c.2.1
          have p27134_2 := h27134c.2.2.1
          have p27134_3 := h27134c.2.2.2
          linarith only [hlam, p27134_0]
        · have p27134_0 := h27134c.1
          have p27134_1 := h27134c.2.1
          have p27134_2 := h27134c.2.2.1
          have p27134_3 := h27134c.2.2.2
          linarith only [h22355, hlam, p27134_0]
        · have p27134_0 := h27134c.1
          have p27134_1 := h27134c.2.1
          have p27134_2 := h27134c.2.2.1
          have p27134_3 := h27134c.2.2.2
          rcases p27134_3 (m.d 0 1) (by simp) with h27324 | h27324
          · linarith only [h20697, h27324, hlam]
          · rcases p27134_3 (m.d 0 2) (by simp) with h27326 | h27326
            · rcases p27134_3 (m.d 0 3) (by simp) with h27327 | h27327
              · rcases p27134_3 (m.d 0 4) (by simp) with h27328 | h27328
                · linarith only [h22355, h27328, hlam]
                · linarith only [h18443, h27328, hlam]
              · linarith only [h15532, h27327, hlam]
            · linarith only [h0, h27326, hlam]
        · have p27134_0 := h27134c.1
          have p27134_1 := h27134c.2.1
          have p27134_2 := h27134c.2.2.1
          have p27134_3 := h27134c.2.2.2
          linarith only [h22352, hlam, p27134_1]
        · have p27134_0 := h27134c.1
          have p27134_1 := h27134c.2.1
          have p27134_2 := h27134c.2.2.1
          have p27134_3 := h27134c.2.2.2
          linarith only [h22354, hlam, p27134_0]
        · have p27134_0 := h27134c.1
          have p27134_1 := h27134c.2.1
          have p27134_2 := h27134c.2.2.1
          have p27134_3 := h27134c.2.2.2
          linarith only [h22353, h22355, h26147, hc23, hc45, hlam, hphi, ht34, p27134_1]
        · have p27134_0 := h27134c.1
          have p27134_1 := h27134c.2.1
          have p27134_2 := h27134c.2.2.1
          have p27134_3 := h27134c.2.2.2
          linarith only [hlam, p27134_0]

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25423 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25424 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h25425 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h25426 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h25427 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  rcases m.htr 2 3 4 (by decide) (by decide) with h26147 | h26147
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427 h26147

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25423 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25424 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h25425 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h25426 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  rcases m.htr 1 4 5 (by decide) (by decide) with h25427 | h25427
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426 h25427

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25423 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25424 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h25425 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h25426 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  linarith only [h0, h15532, h22350, h22354, h25426, hc01, hc12, hlam, hphi]

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25423 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25424 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h25425 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  rcases m.htr 1 3 5 (by decide) (by decide) with h25426 | h25426
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425 h25426

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25423 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25424 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h25425 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  linarith only [h15532, h22353, h25425, hlam]

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25423 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25424 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  rcases m.htr 1 3 4 (by decide) (by decide) with h25425 | h25425
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424 h25425

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25423 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h25424 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  linarith only [h0, h22352, h25424, hlam]

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25423 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  rcases m.htr 1 2 5 (by decide) (by decide) with h25424 | h25424
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423 h25424

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h25423 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  linarith only [h0, h22351, h25423, hlam]

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  rcases m.htr 1 2 4 (by decide) (by decide) with h25423 | h25423
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422 h25423

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h25422 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  linarith only [h0, h22350, h25422, hlam]

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h22355 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  rcases m.htr 1 2 3 (by decide) (by decide) with h25422 | h25422
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355 h25422

set_option maxHeartbeats 9974000 in
set_option maxHeartbeats 9974000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  rcases m.htr 0 4 5 (by decide) (by decide) with h22355 | h22355
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s25_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 h22355

end R2N4
