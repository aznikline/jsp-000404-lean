import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S29
import Jsp000404.R1LeavesN7_0S33

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h14159 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  rcases m.htr 1 2 3 (by decide) (by decide) with h16969 | h16969
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159 h16969

set_option maxHeartbeats 9600000 in
set_option maxHeartbeats 9600000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (hg13284 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h13284 := hg13284
  rcases m.htr 0 4 5 (by decide) (by decide) with h14159 | h14159
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s19_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg13284 h14159

set_option maxHeartbeats 11350000 in
set_option maxHeartbeats 11350000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s18_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h13284 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h13285 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h13286 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 2 4 (by decide) (by decide) with h13287 | h13287
  · rcases m.htr 1 2 5 (by decide) (by decide) with h13288 | h13288
    · rcases m.htr 1 3 4 (by decide) (by decide) with h13289 | h13289
      · linarith only [h1, h13289, h7, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h13291 | h13291
        · rcases m.htr 1 4 5 (by decide) (by decide) with h13292 | h13292
          · rcases m.htr 2 3 4 (by decide) (by decide) with h13293 | h13293
            · linarith only [h1, h13286, h13293, h7, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h13295 | h13295
              · rcases m.htr 2 4 5 (by decide) (by decide) with h13296 | h13296
                · rcases m.htr 3 4 5 (by decide) (by decide) with h13297 | h13297
                  · rcases h1bigk with h13298c | h13298c | h13298c | h13298c | h13298c | h13298c | h13298c | h13298c | h13298c | h13298c | h13298c | h13298c | h13298c | h13298c | h13298c | h13298c | h13298c | h13298c | h13298c | h13298c | h13298c | h13298c | h13298c | h13298c | h13298c
                    · have p13298_0 := h13298c.1
                      have p13298_1 := h13298c.2.1
                      have p13298_2 := h13298c.2.2.1
                      have p13298_3 := h13298c.2.2.2
                      linarith only [hlam, p13298_0]
                    · have p13298_0 := h13298c.1
                      have p13298_1 := h13298c.2.1
                      have p13298_2 := h13298c.2.2.1
                      have p13298_3 := h13298c.2.2.2
                      linarith only [h13287, h13293, h13295, h13297, hc01, hc45, hlam, hphi, ht0b, ht5b, p13298_1]
                    · have p13298_0 := h13298c.1
                      have p13298_1 := h13298c.2.1
                      have p13298_2 := h13298c.2.2.1
                      have p13298_3 := h13298c.2.2.2
                      rcases p13298_3 (m.d 0 1) (by simp) with h13301 | h13301
                      · rcases p13298_3 (m.d 1 2) (by simp) with h13302 | h13302
                        · linarith only [h0, h13302, hlam]
                        · linarith only [h13286, h13302, hlam]
                      · linarith only [h13301, hlam, p13298_0]
                    · have p13298_0 := h13298c.1
                      have p13298_1 := h13298c.2.1
                      have p13298_2 := h13298c.2.2.1
                      have p13298_3 := h13298c.2.2.2
                      rcases p13298_3 (m.d 0 1) (by simp) with h13306 | h13306
                      · rcases p13298_3 (m.d 1 2) (by simp) with h13307 | h13307
                        · linarith only [h0, h13307, hlam]
                        · linarith only [h13287, h13307, hlam]
                      · linarith only [h13306, hlam, p13298_0]
                    · have p13298_0 := h13298c.1
                      have p13298_1 := h13298c.2.1
                      have p13298_2 := h13298c.2.2.1
                      have p13298_3 := h13298c.2.2.2
                      rcases p13298_3 (m.d 0 1) (by simp) with h13311 | h13311
                      · rcases p13298_3 (m.d 1 2) (by simp) with h13312 | h13312
                        · linarith only [h0, h13312, hlam]
                        · linarith only [h13288, h13312, hlam]
                      · linarith only [h13311, hlam, p13298_0]
                    · have p13298_0 := h13298c.1
                      have p13298_1 := h13298c.2.1
                      have p13298_2 := h13298c.2.2.1
                      have p13298_3 := h13298c.2.2.2
                      linarith only [h0, hlam, p13298_0]
                    · have p13298_0 := h13298c.1
                      have p13298_1 := h13298c.2.1
                      have p13298_2 := h13298c.2.2.1
                      have p13298_3 := h13298c.2.2.2
                      linarith only [hlam, p13298_0]
                    · have p13298_0 := h13298c.1
                      have p13298_1 := h13298c.2.1
                      have p13298_2 := h13298c.2.2.1
                      have p13298_3 := h13298c.2.2.2
                      linarith only [h0, h13286, h13295, h13297, hc01, hc45, hlam, hphi, ht0b, ht5b, p13298_1]
                    · have p13298_0 := h13298c.1
                      have p13298_1 := h13298c.2.1
                      have p13298_2 := h13298c.2.2.1
                      have p13298_3 := h13298c.2.2.2
                      linarith only [h0, h13286, h13289, h13295, h13297, hc01, hc45, hlam, hphi, ht0b, ht5b, p13298_1]
                    · have p13298_0 := h13298c.1
                      have p13298_1 := h13298c.2.1
                      have p13298_2 := h13298c.2.2.1
                      have p13298_3 := h13298c.2.2.2
                      rcases p13298_3 (m.d 0 1) (by simp) with h13320 | h13320
                      · rcases p13298_3 (m.d 1 2) (by simp) with h13321 | h13321
                        · rcases p13298_3 (m.d 1 3) (by simp) with h13322 | h13322
                          · linarith only [h13286, h13322, hlam]
                          · linarith only [h13291, h13322, hlam]
                        · linarith only [h13288, h13321, hlam]
                      · linarith only [h13320, h3, hlam]
                    · have p13298_0 := h13298c.1
                      have p13298_1 := h13298c.2.1
                      have p13298_2 := h13298c.2.2.1
                      have p13298_3 := h13298c.2.2.2
                      linarith only [h1, hlam, p13298_0]
                    · have p13298_0 := h13298c.1
                      have p13298_1 := h13298c.2.1
                      have p13298_2 := h13298c.2.2.1
                      have p13298_3 := h13298c.2.2.2
                      linarith only [h13286, hlam, p13298_0]
                    · have p13298_0 := h13298c.1
                      have p13298_1 := h13298c.2.1
                      have p13298_2 := h13298c.2.2.1
                      have p13298_3 := h13298c.2.2.2
                      linarith only [hlam, p13298_0]
                    · have p13298_0 := h13298c.1
                      have p13298_1 := h13298c.2.1
                      have p13298_2 := h13298c.2.2.1
                      have p13298_3 := h13298c.2.2.2
                      linarith only [h13289, hlam, p13298_0]
                    · have p13298_0 := h13298c.1
                      have p13298_1 := h13298c.2.1
                      have p13298_2 := h13298c.2.2.1
                      have p13298_3 := h13298c.2.2.2
                      rcases p13298_3 (m.d 0 1) (by simp) with h13331 | h13331
                      · rcases p13298_3 (m.d 1 2) (by simp) with h13332 | h13332
                        · rcases p13298_3 (m.d 1 3) (by simp) with h13333 | h13333
                          · rcases p13298_3 (m.d 1 4) (by simp) with h13334 | h13334
                            · rcases p13298_3 (m.d 1 5) (by simp) with h13335 | h13335
                              · linarith only [h13291, h13335, hlam]
                              · rcases h1emax with h13337 | h13337 | h13337 | h13337 | h13337
                                · linarith only [h0, h13287, h13293, h13337, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                · linarith only [h13287, h13288, h13289, h13295, h13297, h13337, hc45, hlam, hphi, ht01, ht0b, ht5b, p13298_1]
                                · linarith only [h13288, h13295, h13297, h13337, hc45, hlam, hphi, ht01, ht0b, ht5b, p13298_1]
                                · linarith only [h13288, h13289, h13295, h13297, h13337, hc45, hlam, hphi, ht01, ht0b, ht5b, p13298_1]
                                · rcases h2bigk with h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c | h13342c
                                  · have p13342_0 := h13342c.1
                                    have p13342_1 := h13342c.2.1
                                    have p13342_2 := h13342c.2.2.1
                                    have p13342_3 := h13342c.2.2.2
                                    linarith only [hlam, p13342_0]
                                  · have p13342_0 := h13342c.1
                                    have p13342_1 := h13342c.2.1
                                    have p13342_2 := h13342c.2.2.1
                                    have p13342_3 := h13342c.2.2.2
                                    linarith only [h0, h13287, h13288, h13289, h13295, h13297, hc01, hc45, hlam, hphi, ht0b, ht5b, p13298_1, p13342_1]
                                  · have p13342_0 := h13342c.1
                                    have p13342_1 := h13342c.2.1
                                    have p13342_2 := h13342c.2.2.1
                                    have p13342_3 := h13342c.2.2.2
                                    rcases p13342_3 (m.d 0 2) (by simp) with h13345 | h13345
                                    · rcases p13342_3 (m.d 1 2) (by simp) with h13346 | h13346
                                      · linarith only [h0, h13346, hlam]
                                      · linarith only [h13286, h13346, hlam]
                                    · linarith only [h13345, hlam, p13342_0]
                                  · have p13342_0 := h13342c.1
                                    have p13342_1 := h13342c.2.1
                                    have p13342_2 := h13342c.2.2.1
                                    have p13342_3 := h13342c.2.2.2
                                    rcases p13342_3 (m.d 0 2) (by simp) with h13350 | h13350
                                    · rcases p13342_3 (m.d 1 2) (by simp) with h13351 | h13351
                                      · linarith only [h0, h13351, hlam]
                                      · linarith only [h13287, h13351, hlam]
                                    · linarith only [h13350, hlam, p13342_0]
                                  · have p13342_0 := h13342c.1
                                    have p13342_1 := h13342c.2.1
                                    have p13342_2 := h13342c.2.2.1
                                    have p13342_3 := h13342c.2.2.2
                                    rcases p13342_3 (m.d 0 2) (by simp) with h13355 | h13355
                                    · rcases p13342_3 (m.d 1 2) (by simp) with h13356 | h13356
                                      · linarith only [h0, h13356, hlam]
                                      · linarith only [h13288, h13356, hlam]
                                    · linarith only [h13355, hlam, p13342_0]
                                  · have p13342_0 := h13342c.1
                                    have p13342_1 := h13342c.2.1
                                    have p13342_2 := h13342c.2.2.1
                                    have p13342_3 := h13342c.2.2.2
                                    linarith only [h0, hlam, p13342_1]
                                  · have p13342_0 := h13342c.1
                                    have p13342_1 := h13342c.2.1
                                    have p13342_2 := h13342c.2.2.1
                                    have p13342_3 := h13342c.2.2.2
                                    linarith only [hlam, p13342_0]
                                  · have p13342_0 := h13342c.1
                                    have p13342_1 := h13342c.2.1
                                    have p13342_2 := h13342c.2.2.1
                                    have p13342_3 := h13342c.2.2.2
                                    linarith only [h0, h13295, h13297, hc01, hc45, hlam, hphi, ht0b, ht5b, p13342_1]
                                  · have p13342_0 := h13342c.1
                                    have p13342_1 := h13342c.2.1
                                    have p13342_2 := h13342c.2.2.1
                                    have p13342_3 := h13342c.2.2.2
                                    linarith only [h0, h13293, h13295, h13297, hc01, hc45, hlam, hphi, ht0b, ht5b, p13342_1]
                                  · have p13342_0 := h13342c.1
                                    have p13342_1 := h13342c.2.1
                                    have p13342_2 := h13342c.2.2.1
                                    have p13342_3 := h13342c.2.2.2
                                    rcases p13342_3 (m.d 0 2) (by simp) with h13364 | h13364
                                    · rcases p13342_3 (m.d 1 2) (by simp) with h13365 | h13365
                                      · rcases p13342_3 (m.d 2 3) (by simp) with h13366 | h13366
                                        · linarith only [h13286, h13366, hlam]
                                        · linarith only [h13295, h13366, hlam]
                                      · linarith only [h13365, hlam, p13342_0]
                                    · linarith only [h13364, h6, hlam]
                                  · have p13342_0 := h13342c.1
                                    have p13342_1 := h13342c.2.1
                                    have p13342_2 := h13342c.2.2.1
                                    have p13342_3 := h13342c.2.2.2
                                    linarith only [h4, hlam, p13342_0]
                                  · have p13342_0 := h13342c.1
                                    have p13342_1 := h13342c.2.1
                                    have p13342_2 := h13342c.2.2.1
                                    have p13342_3 := h13342c.2.2.2
                                    linarith only [h13286, hlam, p13342_0]
                                  · have p13342_0 := h13342c.1
                                    have p13342_1 := h13342c.2.1
                                    have p13342_2 := h13342c.2.2.1
                                    have p13342_3 := h13342c.2.2.2
                                    linarith only [hlam, p13342_0]
                                  · have p13342_0 := h13342c.1
                                    have p13342_1 := h13342c.2.1
                                    have p13342_2 := h13342c.2.2.1
                                    have p13342_3 := h13342c.2.2.2
                                    linarith only [h13293, hlam, p13342_1]
                                  · have p13342_0 := h13342c.1
                                    have p13342_1 := h13342c.2.1
                                    have p13342_2 := h13342c.2.2.1
                                    have p13342_3 := h13342c.2.2.2
                                    linarith only [h0, h13286, h13295, h13297, hc01, hc45, hlam, hphi, ht0b, ht5b, p13342_1]
                                  · have p13342_0 := h13342c.1
                                    have p13342_1 := h13342c.2.1
                                    have p13342_2 := h13342c.2.2.1
                                    have p13342_3 := h13342c.2.2.2
                                    linarith only [h5, hlam, p13342_0]
                                  · have p13342_0 := h13342c.1
                                    have p13342_1 := h13342c.2.1
                                    have p13342_2 := h13342c.2.2.1
                                    have p13342_3 := h13342c.2.2.2
                                    linarith only [h13287, hlam, p13342_0]
                                  · have p13342_0 := h13342c.1
                                    have p13342_1 := h13342c.2.1
                                    have p13342_2 := h13342c.2.2.1
                                    have p13342_3 := h13342c.2.2.2
                                    linarith only [h0, h1, h13287, h13288, h13295, h13297, h7, hc01, hc23, hc34, hc45, hlam, hphi, ht0b, ht5b, p13298_1, p13342_1]
                                  · have p13342_0 := h13342c.1
                                    have p13342_1 := h13342c.2.1
                                    have p13342_2 := h13342c.2.2.1
                                    have p13342_3 := h13342c.2.2.2
                                    linarith only [hlam, p13342_0]
                                  · have p13342_0 := h13342c.1
                                    have p13342_1 := h13342c.2.1
                                    have p13342_2 := h13342c.2.2.1
                                    have p13342_3 := h13342c.2.2.2
                                    linarith only [h0, h13287, h13295, h13297, hc01, hc45, hlam, hphi, ht0b, ht5b, p13342_1]
                                  · have p13342_0 := h13342c.1
                                    have p13342_1 := h13342c.2.1
                                    have p13342_2 := h13342c.2.2.1
                                    have p13342_3 := h13342c.2.2.2
                                    linarith only [h6, hlam, p13342_0]
                                  · have p13342_0 := h13342c.1
                                    have p13342_1 := h13342c.2.1
                                    have p13342_2 := h13342c.2.2.1
                                    have p13342_3 := h13342c.2.2.2
                                    linarith only [h13288, hlam, p13342_0]
                                  · have p13342_0 := h13342c.1
                                    have p13342_1 := h13342c.2.1
                                    have p13342_2 := h13342c.2.2.1
                                    have p13342_3 := h13342c.2.2.2
                                    linarith only [h13295, hlam, p13342_0]
                                  · have p13342_0 := h13342c.1
                                    have p13342_1 := h13342c.2.1
                                    have p13342_2 := h13342c.2.2.1
                                    have p13342_3 := h13342c.2.2.2
                                    linarith only [h13296, hlam, p13342_1]
                                  · have p13342_0 := h13342c.1
                                    have p13342_1 := h13342c.2.1
                                    have p13342_2 := h13342c.2.2.1
                                    have p13342_3 := h13342c.2.2.2
                                    linarith only [hlam, p13342_0]
                            · linarith only [h13292, h13334, hlam]
                          · linarith only [h13291, h13333, hlam]
                        · linarith only [h13288, h13332, hlam]
                      · linarith only [h13331, h3, hlam]
                    · have p13298_0 := h13298c.1
                      have p13298_1 := h13298c.2.1
                      have p13298_2 := h13298c.2.2.1
                      have p13298_3 := h13298c.2.2.2
                      linarith only [h2, hlam, p13298_0]
                    · have p13298_0 := h13298c.1
                      have p13298_1 := h13298c.2.1
                      have p13298_2 := h13298c.2.2.1
                      have p13298_3 := h13298c.2.2.2
                      linarith only [h13287, hlam, p13298_0]
                    · have p13298_0 := h13298c.1
                      have p13298_1 := h13298c.2.1
                      have p13298_2 := h13298c.2.2.1
                      have p13298_3 := h13298c.2.2.2
                      linarith only [h13286, h13295, h13297, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p13298_1]
                    · have p13298_0 := h13298c.1
                      have p13298_1 := h13298c.2.1
                      have p13298_2 := h13298c.2.2.1
                      have p13298_3 := h13298c.2.2.2
                      linarith only [hlam, p13298_0]
                    · have p13298_0 := h13298c.1
                      have p13298_1 := h13298c.2.1
                      have p13298_2 := h13298c.2.2.1
                      have p13298_3 := h13298c.2.2.2
                      rcases p13298_3 (m.d 0 1) (by simp) with h13394 | h13394
                      · rcases p13298_3 (m.d 1 2) (by simp) with h13395 | h13395
                        · rcases p13298_3 (m.d 1 3) (by simp) with h13396 | h13396
                          · linarith only [h13289, h13396, hlam]
                          · linarith only [h13291, h13396, hlam]
                        · linarith only [h13288, h13395, hlam]
                      · linarith only [h13394, h3, hlam]
                    · have p13298_0 := h13298c.1
                      have p13298_1 := h13298c.2.1
                      have p13298_2 := h13298c.2.2.1
                      have p13298_3 := h13298c.2.2.2
                      linarith only [h3, hlam, p13298_0]
                    · have p13298_0 := h13298c.1
                      have p13298_1 := h13298c.2.1
                      have p13298_2 := h13298c.2.2.1
                      have p13298_3 := h13298c.2.2.2
                      linarith only [h13288, hlam, p13298_0]
                    · have p13298_0 := h13298c.1
                      have p13298_1 := h13298c.2.1
                      have p13298_2 := h13298c.2.2.1
                      have p13298_3 := h13298c.2.2.2
                      linarith only [h13291, hlam, p13298_0]
                    · have p13298_0 := h13298c.1
                      have p13298_1 := h13298c.2.1
                      have p13298_2 := h13298c.2.2.1
                      have p13298_3 := h13298c.2.2.2
                      linarith only [h13292, hlam, p13298_0]
                    · have p13298_0 := h13298c.1
                      have p13298_1 := h13298c.2.1
                      have p13298_2 := h13298c.2.2.1
                      have p13298_3 := h13298c.2.2.2
                      linarith only [hlam, p13298_0]
                  · linarith only [h1, h13285, h13286, h13295, h13297, h7, hc04, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h13292, h13293, h13295, h13296, h2, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · linarith only [h13284, h13295, h7, hc23, hc34, hlam, hphi]
          · linarith only [h13289, h13291, h13292, hlam]
        · linarith only [h13284, h13291, h7, hc13, hc34, hlam, hphi]
    · linarith only [h13284, h13286, h13288, h6, h7, hc23, hc34, hlam, hphi]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h13412 | h13412
    · rcases m.htr 1 3 4 (by decide) (by decide) with h13413 | h13413
      · linarith only [h1, h13284, h13413, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h13415 | h13415
        · rcases m.htr 1 4 5 (by decide) (by decide) with h13416 | h13416
          · rcases m.htr 2 3 4 (by decide) (by decide) with h13417 | h13417
            · linarith only [h13286, h13287, h13417, h5, h7, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h13419 | h13419
              · linarith only [h0, h13286, h13287, h13419, h5, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · linarith only [h1, h13415, h13419, h7, hc23, hc34, hlam, hphi]
          · linarith only [h13284, h13285, h13286, h13287, h13416, h7, hc23, hc34, hlam, hphi]
        · linarith only [h13284, h13415, h7, hc13, hc34, hlam, hphi]
    · linarith only [h13284, h13286, h13412, h6, h7, hc23, hc34, hlam, hphi]

end R2N4
