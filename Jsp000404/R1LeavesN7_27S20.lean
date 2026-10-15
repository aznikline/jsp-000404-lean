import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_27S16
import Jsp000404.R1LeavesN7_27S17
import Jsp000404.R1LeavesN7_27S18
import Jsp000404.R1LeavesN7_27S19

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10998000 in
set_option maxHeartbeats 10998000 in
theorem r1l7_11_25_L_0_H_I_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3355 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3885 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h4515 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h4683 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h4972 | h4972
  · rcases m.htr 1 2 4 (by decide) (by decide) with h4973 | h4973
    · rcases m.htr 1 2 5 (by decide) (by decide) with h4974 | h4974
      · rcases m.htr 1 3 4 (by decide) (by decide) with h4975 | h4975
        · rcases m.htr 1 3 5 (by decide) (by decide) with h4976 | h4976
          · rcases m.htr 1 4 5 (by decide) (by decide) with h4977 | h4977
            · rcases m.htr 2 3 4 (by decide) (by decide) with h4978 | h4978
              · rcases m.htr 2 3 5 (by decide) (by decide) with h4979 | h4979
                · rcases m.htr 2 4 5 (by decide) (by decide) with h4980 | h4980
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4981 | h4981
                    · rcases h5bigk with h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c | h4982c
                      · have p4982_0 := h4982c.1
                        have p4982_1 := h4982c.2.1
                        have p4982_2 := h4982c.2.2.1
                        have p4982_3 := h4982c.2.2.2
                        linarith only [hlam, p4982_0]
                      · have p4982_0 := h4982c.1
                        have p4982_1 := h4982c.2.1
                        have p4982_2 := h4982c.2.2.1
                        have p4982_3 := h4982c.2.2.2
                        linarith only [h3355, hlam, p4982_1]
                      · have p4982_0 := h4982c.1
                        have p4982_1 := h4982c.2.1
                        have p4982_2 := h4982c.2.2.1
                        have p4982_3 := h4982c.2.2.2
                        linarith only [h4515, hlam, p4982_0]
                      · have p4982_0 := h4982c.1
                        have p4982_1 := h4982c.2.1
                        have p4982_2 := h4982c.2.2.1
                        have p4982_3 := h4982c.2.2.2
                        linarith only [h4683, hlam, p4982_1]
                      · have p4982_0 := h4982c.1
                        have p4982_1 := h4982c.2.1
                        have p4982_2 := h4982c.2.2.1
                        have p4982_3 := h4982c.2.2.2
                        linarith only [h4683, h4973, h4979, h4980, hc45, hlam, hphi, ht01, ht0b, ht5b, p4982_1, u1elo1]
                      · have p4982_0 := h4982c.1
                        have p4982_1 := h4982c.2.1
                        have p4982_2 := h4982c.2.2.1
                        have p4982_3 := h4982c.2.2.2
                        linarith only [h4977, hc05, hlam, hphi, ht01, ht0b, ht5b, p4982_1, u1elo3]
                      · have p4982_0 := h4982c.1
                        have p4982_1 := h4982c.2.1
                        have p4982_2 := h4982c.2.2.1
                        have p4982_3 := h4982c.2.2.2
                        linarith only [hlam, p4982_0]
                      · have p4982_0 := h4982c.1
                        have p4982_1 := h4982c.2.1
                        have p4982_2 := h4982c.2.2.1
                        have p4982_3 := h4982c.2.2.2
                        linarith only [h4683, h4973, h4977, h4979, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4982_1, u1elo1]
                      · have p4982_0 := h4982c.1
                        have p4982_1 := h4982c.2.1
                        have p4982_2 := h4982c.2.2.1
                        have p4982_3 := h4982c.2.2.2
                        linarith only [h4683, h4973, h4977, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4982_1, u1elo1]
                      · have p4982_0 := h4982c.1
                        have p4982_1 := h4982c.2.1
                        have p4982_2 := h4982c.2.2.1
                        have p4982_3 := h4982c.2.2.2
                        linarith only [h4973, h4977, hc45, hlam, hphi, ht01, ht0b, ht5b, p4982_1, u1elo1]
                      · have p4982_0 := h4982c.1
                        have p4982_1 := h4982c.2.1
                        have p4982_2 := h4982c.2.2.1
                        have p4982_3 := h4982c.2.2.2
                        linarith only [h3355, hc01, hc25, hlam, hphi, ht12, p4982_1]
                      · have p4982_0 := h4982c.1
                        have p4982_1 := h4982c.2.1
                        have p4982_2 := h4982c.2.2.1
                        have p4982_3 := h4982c.2.2.2
                        linarith only [h4974, hlam, p4982_1]
                      · have p4982_0 := h4982c.1
                        have p4982_1 := h4982c.2.1
                        have p4982_2 := h4982c.2.2.1
                        have p4982_3 := h4982c.2.2.2
                        linarith only [hlam, p4982_0]
                      · have p4982_0 := h4982c.1
                        have p4982_1 := h4982c.2.1
                        have p4982_2 := h4982c.2.2.1
                        have p4982_3 := h4982c.2.2.2
                        linarith only [h4683, h4974, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p4982_1, u1elo1]
                      · have p4982_0 := h4982c.1
                        have p4982_1 := h4982c.2.1
                        have p4982_2 := h4982c.2.2.1
                        have p4982_3 := h4982c.2.2.2
                        linarith only [h4973, h4980, hc45, hlam, hphi, ht01, ht0b, ht5b, p4982_1, u1elo1]
                      · have p4982_0 := h4982c.1
                        have p4982_1 := h4982c.2.1
                        have p4982_2 := h4982c.2.2.1
                        have p4982_3 := h4982c.2.2.2
                        linarith only [h3355, h4515, h4973, h4980, hc01, hc02, hc35, hlam, hphi, ht23, p4982_1, u1elo1]
                      · have p4982_0 := h4982c.1
                        have p4982_1 := h4982c.2.1
                        have p4982_2 := h4982c.2.2.1
                        have p4982_3 := h4982c.2.2.2
                        linarith only [h4976, hlam, p4982_0]
                      · have p4982_0 := h4982c.1
                        have p4982_1 := h4982c.2.1
                        have p4982_2 := h4982c.2.2.1
                        have p4982_3 := h4982c.2.2.2
                        linarith only [h4979, hlam, p4982_0]
                      · have p4982_0 := h4982c.1
                        have p4982_1 := h4982c.2.1
                        have p4982_2 := h4982c.2.2.1
                        have p4982_3 := h4982c.2.2.2
                        linarith only [hlam, p4982_0]
                      · have p4982_0 := h4982c.1
                        have p4982_1 := h4982c.2.1
                        have p4982_2 := h4982c.2.2.1
                        have p4982_3 := h4982c.2.2.2
                        linarith only [h4973, h4979, h4980, hc45, hlam, hphi, ht01, ht0b, ht5b, p4982_1, u1elo1]
                      · have p4982_0 := h4982c.1
                        have p4982_1 := h4982c.2.1
                        have p4982_2 := h4982c.2.2.1
                        have p4982_3 := h4982c.2.2.2
                        linarith only [h4972, hlam, p4982_0]
                      · have p4982_0 := h4982c.1
                        have p4982_1 := h4982c.2.1
                        have p4982_2 := h4982c.2.2.1
                        have p4982_3 := h4982c.2.2.2
                        linarith only [h4977, hlam, p4982_0]
                      · have p4982_0 := h4982c.1
                        have p4982_1 := h4982c.2.1
                        have p4982_2 := h4982c.2.2.1
                        have p4982_3 := h4982c.2.2.2
                        linarith only [h4980, hlam, p4982_0]
                      · have p4982_0 := h4982c.1
                        have p4982_1 := h4982c.2.1
                        have p4982_2 := h4982c.2.2.1
                        have p4982_3 := h4982c.2.2.2
                        linarith only [h4981, hlam, p4982_0]
                      · have p4982_0 := h4982c.1
                        have p4982_1 := h4982c.2.1
                        have p4982_2 := h4982c.2.2.1
                        have p4982_3 := h4982c.2.2.2
                        linarith only [hlam, p4982_0]
                    · linarith only [h3885, h4972, h4973, h4981, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · linarith only [h3885, h4972, h4980, hlam]
                · linarith only [h4976, h4978, h4979, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5011 | h5011
                · linarith only [h4975, h4978, h5011, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5013 | h5013
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5014 | h5014
                    · rcases h5bigk with h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c | h5015c
                      · have p5015_0 := h5015c.1
                        have p5015_1 := h5015c.2.1
                        have p5015_2 := h5015c.2.2.1
                        have p5015_3 := h5015c.2.2.2
                        linarith only [hlam, p5015_0]
                      · have p5015_0 := h5015c.1
                        have p5015_1 := h5015c.2.1
                        have p5015_2 := h5015c.2.2.1
                        have p5015_3 := h5015c.2.2.2
                        linarith only [h3355, hlam, p5015_1]
                      · have p5015_0 := h5015c.1
                        have p5015_1 := h5015c.2.1
                        have p5015_2 := h5015c.2.2.1
                        have p5015_3 := h5015c.2.2.2
                        linarith only [h4515, hlam, p5015_0]
                      · have p5015_0 := h5015c.1
                        have p5015_1 := h5015c.2.1
                        have p5015_2 := h5015c.2.2.1
                        have p5015_3 := h5015c.2.2.2
                        linarith only [h4683, hlam, p5015_1]
                      · have p5015_0 := h5015c.1
                        have p5015_1 := h5015c.2.1
                        have p5015_2 := h5015c.2.2.1
                        have p5015_3 := h5015c.2.2.2
                        linarith only [h3355, h4973, h4977, hc45, hlam, hphi, ht01, ht0b, ht5b, p5015_1, u1elo1]
                      · have p5015_0 := h5015c.1
                        have p5015_1 := h5015c.2.1
                        have p5015_2 := h5015c.2.2.1
                        have p5015_3 := h5015c.2.2.2
                        linarith only [h4973, h4977, hc05, hlam, hphi, ht01, ht0b, ht5b, p5015_1, u1elo1]
                      · have p5015_0 := h5015c.1
                        have p5015_1 := h5015c.2.1
                        have p5015_2 := h5015c.2.2.1
                        have p5015_3 := h5015c.2.2.2
                        linarith only [hlam, p5015_0]
                      · have p5015_0 := h5015c.1
                        have p5015_1 := h5015c.2.1
                        have p5015_2 := h5015c.2.2.1
                        have p5015_3 := h5015c.2.2.2
                        linarith only [h4515, h4973, h4977, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5015_1, u1elo1]
                      · have p5015_0 := h5015c.1
                        have p5015_1 := h5015c.2.1
                        have p5015_2 := h5015c.2.2.1
                        have p5015_3 := h5015c.2.2.2
                        linarith only [h4515, h4973, h4977, h5011, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5015_1, u1elo1]
                      · have p5015_0 := h5015c.1
                        have p5015_1 := h5015c.2.1
                        have p5015_2 := h5015c.2.2.1
                        have p5015_3 := h5015c.2.2.2
                        linarith only [h4973, h4977, hc45, hlam, hphi, ht01, ht0b, ht5b, p5015_1, u1elo1]
                      · have p5015_0 := h5015c.1
                        have p5015_1 := h5015c.2.1
                        have p5015_2 := h5015c.2.2.1
                        have p5015_3 := h5015c.2.2.2
                        linarith only [h3355, hc01, hc25, hlam, hphi, ht12, p5015_1]
                      · have p5015_0 := h5015c.1
                        have p5015_1 := h5015c.2.1
                        have p5015_2 := h5015c.2.2.1
                        have p5015_3 := h5015c.2.2.2
                        linarith only [h4974, hlam, p5015_1]
                      · have p5015_0 := h5015c.1
                        have p5015_1 := h5015c.2.1
                        have p5015_2 := h5015c.2.2.1
                        have p5015_3 := h5015c.2.2.2
                        linarith only [hlam, p5015_0]
                      · have p5015_0 := h5015c.1
                        have p5015_1 := h5015c.2.1
                        have p5015_2 := h5015c.2.2.1
                        have p5015_3 := h5015c.2.2.2
                        linarith only [h5011, hlam, p5015_1]
                      · have p5015_0 := h5015c.1
                        have p5015_1 := h5015c.2.1
                        have p5015_2 := h5015c.2.2.1
                        have p5015_3 := h5015c.2.2.2
                        linarith only [h4975, h4978, h5013, hc45, hlam, hphi, ht01, ht0b, ht5b, p5015_1, u1elo2]
                      · have p5015_0 := h5015c.1
                        have p5015_1 := h5015c.2.1
                        have p5015_2 := h5015c.2.2.1
                        have p5015_3 := h5015c.2.2.2
                        linarith only [h3355, h4976, hc01, hlam, hphi, p5015_1, u1elo2]
                      · have p5015_0 := h5015c.1
                        have p5015_1 := h5015c.2.1
                        have p5015_2 := h5015c.2.2.1
                        have p5015_3 := h5015c.2.2.2
                        linarith only [h4976, hlam, p5015_0]
                      · have p5015_0 := h5015c.1
                        have p5015_1 := h5015c.2.1
                        have p5015_2 := h5015c.2.2.1
                        have p5015_3 := h5015c.2.2.2
                        linarith only [h4515, h4976, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5015_1, u1elo2]
                      · have p5015_0 := h5015c.1
                        have p5015_1 := h5015c.2.1
                        have p5015_2 := h5015c.2.2.1
                        have p5015_3 := h5015c.2.2.2
                        linarith only [hlam, p5015_0]
                      · have p5015_0 := h5015c.1
                        have p5015_1 := h5015c.2.1
                        have p5015_2 := h5015c.2.2.1
                        have p5015_3 := h5015c.2.2.2
                        linarith only [h4975, h5014, hc45, hlam, hphi, ht01, ht0b, ht5b, p5015_1, u1elo2]
                      · have p5015_0 := h5015c.1
                        have p5015_1 := h5015c.2.1
                        have p5015_2 := h5015c.2.2.1
                        have p5015_3 := h5015c.2.2.2
                        linarith only [h4972, hlam, p5015_0]
                      · have p5015_0 := h5015c.1
                        have p5015_1 := h5015c.2.1
                        have p5015_2 := h5015c.2.2.1
                        have p5015_3 := h5015c.2.2.2
                        linarith only [h4977, hlam, p5015_0]
                      · have p5015_0 := h5015c.1
                        have p5015_1 := h5015c.2.1
                        have p5015_2 := h5015c.2.2.1
                        have p5015_3 := h5015c.2.2.2
                        linarith only [h5013, hlam, p5015_0]
                      · have p5015_0 := h5015c.1
                        have p5015_1 := h5015c.2.1
                        have p5015_2 := h5015c.2.2.1
                        have p5015_3 := h5015c.2.2.2
                        linarith only [h5014, hlam, p5015_0]
                      · have p5015_0 := h5015c.1
                        have p5015_1 := h5015c.2.1
                        have p5015_2 := h5015c.2.2.1
                        have p5015_3 := h5015c.2.2.2
                        linarith only [hlam, p5015_0]
                    · linarith only [h3885, h4972, h4978, h5014, hlam]
                  · linarith only [h3885, h4972, h5013, hlam]
            · linarith only [h0, h3885, h4972, h4977, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5044 | h5044
            · linarith only [h4975, h4976, h5044, hlam]
            · linarith only [h3885, h4972, h4973, h5044, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h5047 | h5047
          · linarith only [h4683, h4975, h5047, hc03, hc34, hlam, hphi]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5049 | h5049
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5050 | h5050
              · linarith only [h3355, h4973, h4975, h5049, h5050, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5052 | h5052
                · linarith only [h5047, h5050, h5052, hc13, hc34, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5054 | h5054
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5055 | h5055
                    · rcases h5bigk with h5056c | h5056c | h5056c | h5056c | h5056c | h5056c | h5056c | h5056c | h5056c | h5056c | h5056c | h5056c | h5056c | h5056c | h5056c | h5056c | h5056c | h5056c | h5056c | h5056c | h5056c | h5056c | h5056c | h5056c | h5056c
                      · have p5056_0 := h5056c.1
                        have p5056_1 := h5056c.2.1
                        have p5056_2 := h5056c.2.2.1
                        have p5056_3 := h5056c.2.2.2
                        linarith only [hlam, p5056_0]
                      · have p5056_0 := h5056c.1
                        have p5056_1 := h5056c.2.1
                        have p5056_2 := h5056c.2.2.1
                        have p5056_3 := h5056c.2.2.2
                        linarith only [h3355, hlam, p5056_1]
                      · have p5056_0 := h5056c.1
                        have p5056_1 := h5056c.2.1
                        have p5056_2 := h5056c.2.2.1
                        have p5056_3 := h5056c.2.2.2
                        linarith only [h4515, hlam, p5056_0]
                      · have p5056_0 := h5056c.1
                        have p5056_1 := h5056c.2.1
                        have p5056_2 := h5056c.2.2.1
                        have p5056_3 := h5056c.2.2.2
                        linarith only [h4683, hlam, p5056_1]
                      · have p5056_0 := h5056c.1
                        have p5056_1 := h5056c.2.1
                        have p5056_2 := h5056c.2.2.1
                        have p5056_3 := h5056c.2.2.2
                        linarith only [h3355, h5049, hc45, hlam, hphi, ht01, ht0b, ht5b, p5056_1, u1elo3]
                      · have p5056_0 := h5056c.1
                        have p5056_1 := h5056c.2.1
                        have p5056_2 := h5056c.2.2.1
                        have p5056_3 := h5056c.2.2.2
                        linarith only [h5049, hc05, hlam, hphi, ht01, ht0b, ht5b, p5056_1, u1elo3]
                      · have p5056_0 := h5056c.1
                        have p5056_1 := h5056c.2.1
                        have p5056_2 := h5056c.2.2.1
                        have p5056_3 := h5056c.2.2.2
                        linarith only [hlam, p5056_0]
                      · have p5056_0 := h5056c.1
                        have p5056_1 := h5056c.2.1
                        have p5056_2 := h5056c.2.2.1
                        have p5056_3 := h5056c.2.2.2
                        linarith only [h4515, h4973, h5049, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5056_1, u1elo1]
                      · have p5056_0 := h5056c.1
                        have p5056_1 := h5056c.2.1
                        have p5056_2 := h5056c.2.2.1
                        have p5056_3 := h5056c.2.2.2
                        linarith only [h5047, hlam, p5056_1]
                      · have p5056_0 := h5056c.1
                        have p5056_1 := h5056c.2.1
                        have p5056_2 := h5056c.2.2.1
                        have p5056_3 := h5056c.2.2.2
                        linarith only [h4973, h5049, hc45, hlam, hphi, ht01, ht0b, ht5b, p5056_1, u1elo1]
                      · have p5056_0 := h5056c.1
                        have p5056_1 := h5056c.2.1
                        have p5056_2 := h5056c.2.2.1
                        have p5056_3 := h5056c.2.2.2
                        linarith only [h3355, hc01, hc25, hlam, hphi, ht12, p5056_1]
                      · have p5056_0 := h5056c.1
                        have p5056_1 := h5056c.2.1
                        have p5056_2 := h5056c.2.2.1
                        have p5056_3 := h5056c.2.2.2
                        linarith only [h4974, hlam, p5056_1]
                      · have p5056_0 := h5056c.1
                        have p5056_1 := h5056c.2.1
                        have p5056_2 := h5056c.2.2.1
                        have p5056_3 := h5056c.2.2.2
                        linarith only [hlam, p5056_0]
                      · have p5056_0 := h5056c.1
                        have p5056_1 := h5056c.2.1
                        have p5056_2 := h5056c.2.2.1
                        have p5056_3 := h5056c.2.2.2
                        linarith only [h5052, hlam, p5056_1]
                      · have p5056_0 := h5056c.1
                        have p5056_1 := h5056c.2.1
                        have p5056_2 := h5056c.2.2.1
                        have p5056_3 := h5056c.2.2.2
                        linarith only [h4973, h5054, hc45, hlam, hphi, ht01, ht0b, ht5b, p5056_1, u1elo1]
                      · have p5056_0 := h5056c.1
                        have p5056_1 := h5056c.2.1
                        have p5056_2 := h5056c.2.2.1
                        have p5056_3 := h5056c.2.2.2
                        linarith only [h3355, h4515, h4973, h5054, hc01, hc02, hc35, hlam, hphi, ht23, p5056_1, u1elo1]
                      · have p5056_0 := h5056c.1
                        have p5056_1 := h5056c.2.1
                        have p5056_2 := h5056c.2.2.1
                        have p5056_3 := h5056c.2.2.2
                        linarith only [h3355, h4515, h4973, h5054, hc01, hc02, hc35, hlam, hphi, ht23, p5056_1, u1elo1]
                      · have p5056_0 := h5056c.1
                        have p5056_1 := h5056c.2.1
                        have p5056_2 := h5056c.2.2.1
                        have p5056_3 := h5056c.2.2.2
                        linarith only [h4515, hc02, hc35, hlam, hphi, ht23, p5056_1]
                      · have p5056_0 := h5056c.1
                        have p5056_1 := h5056c.2.1
                        have p5056_2 := h5056c.2.2.1
                        have p5056_3 := h5056c.2.2.2
                        linarith only [hlam, p5056_0]
                      · have p5056_0 := h5056c.1
                        have p5056_1 := h5056c.2.1
                        have p5056_2 := h5056c.2.2.1
                        have p5056_3 := h5056c.2.2.2
                        rcases p5056_3 (m.d 0 5) (by simp) with h5076 | h5076
                        · linarith only [h4683, h5076, hlam]
                        · linarith only [h4972, h5076, hlam]
                      · have p5056_0 := h5056c.1
                        have p5056_1 := h5056c.2.1
                        have p5056_2 := h5056c.2.2.1
                        have p5056_3 := h5056c.2.2.2
                        linarith only [h4972, hlam, p5056_0]
                      · have p5056_0 := h5056c.1
                        have p5056_1 := h5056c.2.1
                        have p5056_2 := h5056c.2.2.1
                        have p5056_3 := h5056c.2.2.2
                        linarith only [h5049, hlam, p5056_0]
                      · have p5056_0 := h5056c.1
                        have p5056_1 := h5056c.2.1
                        have p5056_2 := h5056c.2.2.1
                        have p5056_3 := h5056c.2.2.2
                        linarith only [h5054, hlam, p5056_0]
                      · have p5056_0 := h5056c.1
                        have p5056_1 := h5056c.2.1
                        have p5056_2 := h5056c.2.2.1
                        have p5056_3 := h5056c.2.2.2
                        linarith only [h5055, hlam, p5056_0]
                      · have p5056_0 := h5056c.1
                        have p5056_1 := h5056c.2.1
                        have p5056_2 := h5056c.2.2.1
                        have p5056_3 := h5056c.2.2.2
                        linarith only [hlam, p5056_0]
                    · linarith only [h3885, h4972, h4973, h5055, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · linarith only [h3885, h4972, h5054, hlam]
            · linarith only [h3885, h4972, h4973, h5049, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
      · linarith only [h3885, h4973, h4974, hc02, hc25, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h5088 | h5088
      · linarith only [h4515, h4973, h5088, hc02, hc24, hlam, hphi]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h5090 | h5090
        · rcases m.htr 1 3 5 (by decide) (by decide) with h5091 | h5091
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5092 | h5092
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5093 | h5093
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5094 | h5094
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5095 | h5095
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5096 | h5096
                    · rcases h5bigk with h5097c | h5097c | h5097c | h5097c | h5097c | h5097c | h5097c | h5097c | h5097c | h5097c | h5097c | h5097c | h5097c | h5097c | h5097c | h5097c | h5097c | h5097c | h5097c | h5097c | h5097c | h5097c | h5097c | h5097c | h5097c
                      · have p5097_0 := h5097c.1
                        have p5097_1 := h5097c.2.1
                        have p5097_2 := h5097c.2.2.1
                        have p5097_3 := h5097c.2.2.2
                        linarith only [hlam, p5097_0]
                      · have p5097_0 := h5097c.1
                        have p5097_1 := h5097c.2.1
                        have p5097_2 := h5097c.2.2.1
                        have p5097_3 := h5097c.2.2.2
                        linarith only [h3355, hlam, p5097_1]
                      · have p5097_0 := h5097c.1
                        have p5097_1 := h5097c.2.1
                        have p5097_2 := h5097c.2.2.1
                        have p5097_3 := h5097c.2.2.2
                        linarith only [h4515, hlam, p5097_0]
                      · have p5097_0 := h5097c.1
                        have p5097_1 := h5097c.2.1
                        have p5097_2 := h5097c.2.2.1
                        have p5097_3 := h5097c.2.2.2
                        linarith only [h4683, hlam, p5097_1]
                      · have p5097_0 := h5097c.1
                        have p5097_1 := h5097c.2.1
                        have p5097_2 := h5097c.2.2.1
                        have p5097_3 := h5097c.2.2.2
                        linarith only [h3355, h5092, hc45, hlam, hphi, ht01, ht0b, ht5b, p5097_1, u1elo3]
                      · have p5097_0 := h5097c.1
                        have p5097_1 := h5097c.2.1
                        have p5097_2 := h5097c.2.2.1
                        have p5097_3 := h5097c.2.2.2
                        linarith only [h5092, hc05, hlam, hphi, ht01, ht0b, ht5b, p5097_1, u1elo3]
                      · have p5097_0 := h5097c.1
                        have p5097_1 := h5097c.2.1
                        have p5097_2 := h5097c.2.2.1
                        have p5097_3 := h5097c.2.2.2
                        linarith only [hlam, p5097_0]
                      · have p5097_0 := h5097c.1
                        have p5097_1 := h5097c.2.1
                        have p5097_2 := h5097c.2.2.1
                        have p5097_3 := h5097c.2.2.2
                        linarith only [h5088, hlam, p5097_0]
                      · have p5097_0 := h5097c.1
                        have p5097_1 := h5097c.2.1
                        have p5097_2 := h5097c.2.2.1
                        have p5097_3 := h5097c.2.2.2
                        linarith only [h5090, h5092, hc35, hlam, hphi, ht01, ht0b, ht5b, p5097_1, u1elo2]
                      · have p5097_0 := h5097c.1
                        have p5097_1 := h5097c.2.1
                        have p5097_2 := h5097c.2.2.1
                        have p5097_3 := h5097c.2.2.2
                        linarith only [h5090, h5092, hc45, hlam, hphi, ht01, ht0b, ht5b, p5097_1, u1elo2]
                      · have p5097_0 := h5097c.1
                        have p5097_1 := h5097c.2.1
                        have p5097_2 := h5097c.2.2.1
                        have p5097_3 := h5097c.2.2.2
                        linarith only [h3355, hc01, hc25, hlam, hphi, ht12, p5097_1]
                      · have p5097_0 := h5097c.1
                        have p5097_1 := h5097c.2.1
                        have p5097_2 := h5097c.2.2.1
                        have p5097_3 := h5097c.2.2.2
                        linarith only [h5088, hc12, hc25, hlam, hphi, p5097_1]
                      · have p5097_0 := h5097c.1
                        have p5097_1 := h5097c.2.1
                        have p5097_2 := h5097c.2.2.1
                        have p5097_3 := h5097c.2.2.2
                        linarith only [hlam, p5097_0]
                      · have p5097_0 := h5097c.1
                        have p5097_1 := h5097c.2.1
                        have p5097_2 := h5097c.2.2.1
                        have p5097_3 := h5097c.2.2.2
                        linarith only [h4683, h5094, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p5097_1]
                      · have p5097_0 := h5097c.1
                        have p5097_1 := h5097c.2.1
                        have p5097_2 := h5097c.2.2.1
                        have p5097_3 := h5097c.2.2.2
                        rcases p5097_3 (m.d 0 5) (by simp) with h5112 | h5112
                        · linarith only [h4515, h5112, hlam]
                        · linarith only [h4972, h5112, hlam]
                      · have p5097_0 := h5097c.1
                        have p5097_1 := h5097c.2.1
                        have p5097_2 := h5097c.2.2.1
                        have p5097_3 := h5097c.2.2.2
                        linarith only [h3355, hc01, hc35, hlam, hphi, ht12, ht23, p5097_1]
                      · have p5097_0 := h5097c.1
                        have p5097_1 := h5097c.2.1
                        have p5097_2 := h5097c.2.2.1
                        have p5097_3 := h5097c.2.2.2
                        linarith only [h5091, hlam, p5097_0]
                      · have p5097_0 := h5097c.1
                        have p5097_1 := h5097c.2.1
                        have p5097_2 := h5097c.2.2.1
                        have p5097_3 := h5097c.2.2.2
                        linarith only [h5094, hlam, p5097_0]
                      · have p5097_0 := h5097c.1
                        have p5097_1 := h5097c.2.1
                        have p5097_2 := h5097c.2.2.1
                        have p5097_3 := h5097c.2.2.2
                        linarith only [hlam, p5097_0]
                      · have p5097_0 := h5097c.1
                        have p5097_1 := h5097c.2.1
                        have p5097_2 := h5097c.2.2.1
                        have p5097_3 := h5097c.2.2.2
                        linarith only [h5090, h5096, hc45, hlam, hphi, ht01, ht0b, ht5b, p5097_1, u1elo2]
                      · have p5097_0 := h5097c.1
                        have p5097_1 := h5097c.2.1
                        have p5097_2 := h5097c.2.2.1
                        have p5097_3 := h5097c.2.2.2
                        linarith only [h4972, hlam, p5097_0]
                      · have p5097_0 := h5097c.1
                        have p5097_1 := h5097c.2.1
                        have p5097_2 := h5097c.2.2.1
                        have p5097_3 := h5097c.2.2.2
                        linarith only [h5092, hlam, p5097_0]
                      · have p5097_0 := h5097c.1
                        have p5097_1 := h5097c.2.1
                        have p5097_2 := h5097c.2.2.1
                        have p5097_3 := h5097c.2.2.2
                        linarith only [h5095, hlam, p5097_0]
                      · have p5097_0 := h5097c.1
                        have p5097_1 := h5097c.2.1
                        have p5097_2 := h5097c.2.2.1
                        have p5097_3 := h5097c.2.2.2
                        linarith only [h5096, hlam, p5097_0]
                      · have p5097_0 := h5097c.1
                        have p5097_1 := h5097c.2.1
                        have p5097_2 := h5097c.2.2.1
                        have p5097_3 := h5097c.2.2.2
                        linarith only [hlam, p5097_0]
                    · linarith only [h4683, h4972, h5096, hlam]
                  · linarith only [h3885, h4972, h5095, hlam]
                · linarith only [h5091, h5093, h5094, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
              · linarith only [h3355, h4973, h5090, h5092, h5093, hc01, hlam, hphi, u1elo2]
            · linarith only [h0, h4972, h5092, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5130 | h5130
            · linarith only [h5090, h5091, h5130, hlam]
            · linarith only [h0, h4972, h5130, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h5133 | h5133
          · linarith only [h4683, h5090, h5133, hc03, hc34, hlam, hphi]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5135 | h5135
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5136 | h5136
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5137 | h5137
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5138 | h5138
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5139 | h5139
                    · rcases h5bigk with h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c | h5140c
                      · have p5140_0 := h5140c.1
                        have p5140_1 := h5140c.2.1
                        have p5140_2 := h5140c.2.2.1
                        have p5140_3 := h5140c.2.2.2
                        linarith only [hlam, p5140_0]
                      · have p5140_0 := h5140c.1
                        have p5140_1 := h5140c.2.1
                        have p5140_2 := h5140c.2.2.1
                        have p5140_3 := h5140c.2.2.2
                        linarith only [h3355, hlam, p5140_1]
                      · have p5140_0 := h5140c.1
                        have p5140_1 := h5140c.2.1
                        have p5140_2 := h5140c.2.2.1
                        have p5140_3 := h5140c.2.2.2
                        linarith only [h4515, hlam, p5140_0]
                      · have p5140_0 := h5140c.1
                        have p5140_1 := h5140c.2.1
                        have p5140_2 := h5140c.2.2.1
                        have p5140_3 := h5140c.2.2.2
                        linarith only [h4683, hlam, p5140_1]
                      · have p5140_0 := h5140c.1
                        have p5140_1 := h5140c.2.1
                        have p5140_2 := h5140c.2.2.1
                        have p5140_3 := h5140c.2.2.2
                        linarith only [h3355, hc45, hlam, hphi, ht01, ht0b, ht5b, p5140_1, u1elo4]
                      · have p5140_0 := h5140c.1
                        have p5140_1 := h5140c.2.1
                        have p5140_2 := h5140c.2.2.1
                        have p5140_3 := h5140c.2.2.2
                        linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p5140_1, u1elo4]
                      · have p5140_0 := h5140c.1
                        have p5140_1 := h5140c.2.1
                        have p5140_2 := h5140c.2.2.1
                        have p5140_3 := h5140c.2.2.2
                        linarith only [hlam, p5140_0]
                      · have p5140_0 := h5140c.1
                        have p5140_1 := h5140c.2.1
                        have p5140_2 := h5140c.2.2.1
                        have p5140_3 := h5140c.2.2.2
                        linarith only [h5088, hlam, p5140_0]
                      · have p5140_0 := h5140c.1
                        have p5140_1 := h5140c.2.1
                        have p5140_2 := h5140c.2.2.1
                        have p5140_3 := h5140c.2.2.2
                        linarith only [h5133, hlam, p5140_1]
                      · have p5140_0 := h5140c.1
                        have p5140_1 := h5140c.2.1
                        have p5140_2 := h5140c.2.2.1
                        have p5140_3 := h5140c.2.2.2
                        linarith only [h5135, hc45, hlam, hphi, ht01, ht0b, ht5b, p5140_1, u1elo3]
                      · have p5140_0 := h5140c.1
                        have p5140_1 := h5140c.2.1
                        have p5140_2 := h5140c.2.2.1
                        have p5140_3 := h5140c.2.2.2
                        linarith only [h3355, h5138, hc01, hc24, hlam, hphi, ht12, p5140_1]
                      · have p5140_0 := h5140c.1
                        have p5140_1 := h5140c.2.1
                        have p5140_2 := h5140c.2.2.1
                        have p5140_3 := h5140c.2.2.2
                        linarith only [h3355, h5138, hc01, hc24, hlam, hphi, ht12, p5140_1]
                      · have p5140_0 := h5140c.1
                        have p5140_1 := h5140c.2.1
                        have p5140_2 := h5140c.2.2.1
                        have p5140_3 := h5140c.2.2.2
                        linarith only [hlam, p5140_0]
                      · have p5140_0 := h5140c.1
                        have p5140_1 := h5140c.2.1
                        have p5140_2 := h5140c.2.2.1
                        have p5140_3 := h5140c.2.2.2
                        linarith only [h3355, h5133, h5136, h5138, hc01, hc23, hlam, hphi, ht12, p5140_1]
                      · have p5140_0 := h5140c.1
                        have p5140_1 := h5140c.2.1
                        have p5140_2 := h5140c.2.2.1
                        have p5140_3 := h5140c.2.2.2
                        rcases p5140_3 (m.d 0 5) (by simp) with h5155 | h5155
                        · linarith only [h4515, h5155, hlam]
                        · linarith only [h4972, h5155, hlam]
                      · have p5140_0 := h5140c.1
                        have p5140_1 := h5140c.2.1
                        have p5140_2 := h5140c.2.2.1
                        have p5140_3 := h5140c.2.2.2
                        linarith only [h3355, hc01, hc35, hlam, hphi, ht12, ht23, p5140_1]
                      · have p5140_0 := h5140c.1
                        have p5140_1 := h5140c.2.1
                        have p5140_2 := h5140c.2.2.1
                        have p5140_3 := h5140c.2.2.2
                        linarith only [h3355, hc01, hc35, hlam, hphi, ht12, ht23, p5140_1]
                      · have p5140_0 := h5140c.1
                        have p5140_1 := h5140c.2.1
                        have p5140_2 := h5140c.2.2.1
                        have p5140_3 := h5140c.2.2.2
                        linarith only [h5137, hlam, p5140_0]
                      · have p5140_0 := h5140c.1
                        have p5140_1 := h5140c.2.1
                        have p5140_2 := h5140c.2.2.1
                        have p5140_3 := h5140c.2.2.2
                        linarith only [hlam, p5140_0]
                      · have p5140_0 := h5140c.1
                        have p5140_1 := h5140c.2.1
                        have p5140_2 := h5140c.2.2.1
                        have p5140_3 := h5140c.2.2.2
                        linarith only [h5136, h5139, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5140_1]
                      · have p5140_0 := h5140c.1
                        have p5140_1 := h5140c.2.1
                        have p5140_2 := h5140c.2.2.1
                        have p5140_3 := h5140c.2.2.2
                        linarith only [h4972, hlam, p5140_0]
                      · have p5140_0 := h5140c.1
                        have p5140_1 := h5140c.2.1
                        have p5140_2 := h5140c.2.2.1
                        have p5140_3 := h5140c.2.2.2
                        linarith only [h5135, hlam, p5140_0]
                      · have p5140_0 := h5140c.1
                        have p5140_1 := h5140c.2.1
                        have p5140_2 := h5140c.2.2.1
                        have p5140_3 := h5140c.2.2.2
                        linarith only [h5138, hlam, p5140_0]
                      · have p5140_0 := h5140c.1
                        have p5140_1 := h5140c.2.1
                        have p5140_2 := h5140c.2.2.1
                        have p5140_3 := h5140c.2.2.2
                        linarith only [h5139, hlam, p5140_0]
                      · have p5140_0 := h5140c.1
                        have p5140_1 := h5140c.2.1
                        have p5140_2 := h5140c.2.2.1
                        have p5140_3 := h5140c.2.2.2
                        linarith only [hlam, p5140_0]
                    · linarith only [h0, h4972, h5090, h5139, hlam]
                  · linarith only [h3885, h4972, h5138, hlam]
                · linarith only [h3355, h5090, h5135, h5136, h5137, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5171 | h5171
                · linarith only [h4683, h5136, h5171, hc03, hc34, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5173 | h5173
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5174 | h5174
                    · rcases h5bigk with h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c | h5175c
                      · have p5175_0 := h5175c.1
                        have p5175_1 := h5175c.2.1
                        have p5175_2 := h5175c.2.2.1
                        have p5175_3 := h5175c.2.2.2
                        linarith only [hlam, p5175_0]
                      · have p5175_0 := h5175c.1
                        have p5175_1 := h5175c.2.1
                        have p5175_2 := h5175c.2.2.1
                        have p5175_3 := h5175c.2.2.2
                        linarith only [h3355, hlam, p5175_1]
                      · have p5175_0 := h5175c.1
                        have p5175_1 := h5175c.2.1
                        have p5175_2 := h5175c.2.2.1
                        have p5175_3 := h5175c.2.2.2
                        linarith only [h4515, hlam, p5175_0]
                      · have p5175_0 := h5175c.1
                        have p5175_1 := h5175c.2.1
                        have p5175_2 := h5175c.2.2.1
                        have p5175_3 := h5175c.2.2.2
                        linarith only [h4683, hlam, p5175_1]
                      · have p5175_0 := h5175c.1
                        have p5175_1 := h5175c.2.1
                        have p5175_2 := h5175c.2.2.1
                        have p5175_3 := h5175c.2.2.2
                        linarith only [h0, h4972, hc45, hlam, hphi, ht01, ht0b, ht5b, p5175_1, u1elo3]
                      · have p5175_0 := h5175c.1
                        have p5175_1 := h5175c.2.1
                        have p5175_2 := h5175c.2.2.1
                        have p5175_3 := h5175c.2.2.2
                        linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p5175_1, u1elo4]
                      · have p5175_0 := h5175c.1
                        have p5175_1 := h5175c.2.1
                        have p5175_2 := h5175c.2.2.1
                        have p5175_3 := h5175c.2.2.2
                        linarith only [hlam, p5175_0]
                      · have p5175_0 := h5175c.1
                        have p5175_1 := h5175c.2.1
                        have p5175_2 := h5175c.2.2.1
                        have p5175_3 := h5175c.2.2.2
                        linarith only [h5088, hlam, p5175_0]
                      · have p5175_0 := h5175c.1
                        have p5175_1 := h5175c.2.1
                        have p5175_2 := h5175c.2.2.1
                        have p5175_3 := h5175c.2.2.2
                        linarith only [h5133, hlam, p5175_1]
                      · have p5175_0 := h5175c.1
                        have p5175_1 := h5175c.2.1
                        have p5175_2 := h5175c.2.2.1
                        have p5175_3 := h5175c.2.2.2
                        linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p5175_1, u1elo4]
                      · have p5175_0 := h5175c.1
                        have p5175_1 := h5175c.2.1
                        have p5175_2 := h5175c.2.2.1
                        have p5175_3 := h5175c.2.2.2
                        linarith only [h4515, h5173, hc02, hc24, hlam, hphi, p5175_1]
                      · have p5175_0 := h5175c.1
                        have p5175_1 := h5175c.2.1
                        have p5175_2 := h5175c.2.2.1
                        have p5175_3 := h5175c.2.2.2
                        linarith only [h3355, h5171, hc01, hc35, hlam, hphi, ht12, ht23, p5175_1]
                      · have p5175_0 := h5175c.1
                        have p5175_1 := h5175c.2.1
                        have p5175_2 := h5175c.2.2.1
                        have p5175_3 := h5175c.2.2.2
                        linarith only [hlam, p5175_0]
                      · have p5175_0 := h5175c.1
                        have p5175_1 := h5175c.2.1
                        have p5175_2 := h5175c.2.2.1
                        have p5175_3 := h5175c.2.2.2
                        linarith only [h5171, hlam, p5175_1]
                      · have p5175_0 := h5175c.1
                        have p5175_1 := h5175c.2.1
                        have p5175_2 := h5175c.2.2.1
                        have p5175_3 := h5175c.2.2.2
                        rcases p5175_3 (m.d 0 5) (by simp) with h5190 | h5190
                        · linarith only [h4515, h5190, hlam]
                        · linarith only [h4972, h5190, hlam]
                      · have p5175_0 := h5175c.1
                        have p5175_1 := h5175c.2.1
                        have p5175_2 := h5175c.2.2.1
                        have p5175_3 := h5175c.2.2.2
                        linarith only [h3355, h5174, hc01, hc34, hlam, hphi, ht12, ht23, p5175_1]
                      · have p5175_0 := h5175c.1
                        have p5175_1 := h5175c.2.1
                        have p5175_2 := h5175c.2.2.1
                        have p5175_3 := h5175c.2.2.2
                        linarith only [h3355, h5174, hc01, hc34, hlam, hphi, ht12, ht23, p5175_1]
                      · have p5175_0 := h5175c.1
                        have p5175_1 := h5175c.2.1
                        have p5175_2 := h5175c.2.2.1
                        have p5175_3 := h5175c.2.2.2
                        linarith only [h4515, h5174, hc02, hc34, hlam, hphi, ht23, p5175_1]
                      · have p5175_0 := h5175c.1
                        have p5175_1 := h5175c.2.1
                        have p5175_2 := h5175c.2.2.1
                        have p5175_3 := h5175c.2.2.2
                        linarith only [hlam, p5175_0]
                      · have p5175_0 := h5175c.1
                        have p5175_1 := h5175c.2.1
                        have p5175_2 := h5175c.2.2.1
                        have p5175_3 := h5175c.2.2.2
                        rcases p5175_3 (m.d 0 5) (by simp) with h5197 | h5197
                        · linarith only [h4683, h5197, hlam]
                        · linarith only [h4972, h5197, hlam]
                      · have p5175_0 := h5175c.1
                        have p5175_1 := h5175c.2.1
                        have p5175_2 := h5175c.2.2.1
                        have p5175_3 := h5175c.2.2.2
                        linarith only [h4972, hlam, p5175_0]
                      · have p5175_0 := h5175c.1
                        have p5175_1 := h5175c.2.1
                        have p5175_2 := h5175c.2.2.1
                        have p5175_3 := h5175c.2.2.2
                        linarith only [h5135, hlam, p5175_0]
                      · have p5175_0 := h5175c.1
                        have p5175_1 := h5175c.2.1
                        have p5175_2 := h5175c.2.2.1
                        have p5175_3 := h5175c.2.2.2
                        linarith only [h5173, hlam, p5175_0]
                      · have p5175_0 := h5175c.1
                        have p5175_1 := h5175c.2.1
                        have p5175_2 := h5175c.2.2.1
                        have p5175_3 := h5175c.2.2.2
                        linarith only [h5174, hlam, p5175_0]
                      · have p5175_0 := h5175c.1
                        have p5175_1 := h5175c.2.1
                        have p5175_2 := h5175c.2.2.1
                        have p5175_3 := h5175c.2.2.2
                        linarith only [hlam, p5175_0]
                    · linarith only [h3885, h4972, h5136, h5174, hlam]
                  · linarith only [h0, h3355, h4972, h4973, h5173, hc01, hlam, hphi, u1elo4]
            · linarith only [h0, h4972, h5135, hlam]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h5208 | h5208
    · rcases m.htr 1 2 5 (by decide) (by decide) with h5209 | h5209
      · rcases m.htr 1 3 4 (by decide) (by decide) with h5210 | h5210
        · rcases m.htr 1 3 5 (by decide) (by decide) with h5211 | h5211
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5212 | h5212
            · linarith only [h0, h4972, h5212, hc01, hlam, hphi, u1elo3]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5214 | h5214
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5215 | h5215
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5216 | h5216
                  · linarith only [h5208, h5212, h5216, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5218 | h5218
                    · linarith only [h0, h5209, h5212, h5214, h5216, h5218, hc01, hlam, hphi, u1elo1]
                    · rcases h5bigk with h5220c | h5220c | h5220c | h5220c | h5220c | h5220c | h5220c | h5220c | h5220c | h5220c | h5220c | h5220c | h5220c | h5220c | h5220c | h5220c | h5220c | h5220c | h5220c | h5220c | h5220c | h5220c | h5220c | h5220c | h5220c
                      · have p5220_0 := h5220c.1
                        have p5220_1 := h5220c.2.1
                        have p5220_2 := h5220c.2.2.1
                        have p5220_3 := h5220c.2.2.2
                        linarith only [hlam, p5220_0]
                      · have p5220_0 := h5220c.1
                        have p5220_1 := h5220c.2.1
                        have p5220_2 := h5220c.2.2.1
                        have p5220_3 := h5220c.2.2.2
                        linarith only [h3355, hlam, p5220_1]
                      · have p5220_0 := h5220c.1
                        have p5220_1 := h5220c.2.1
                        have p5220_2 := h5220c.2.2.1
                        have p5220_3 := h5220c.2.2.2
                        linarith only [h4515, hlam, p5220_0]
                      · have p5220_0 := h5220c.1
                        have p5220_1 := h5220c.2.1
                        have p5220_2 := h5220c.2.2.1
                        have p5220_3 := h5220c.2.2.2
                        linarith only [h4683, hlam, p5220_1]
                      · have p5220_0 := h5220c.1
                        have p5220_1 := h5220c.2.1
                        have p5220_2 := h5220c.2.2.1
                        have p5220_3 := h5220c.2.2.2
                        linarith only [h4972, hlam, p5220_1]
                      · have p5220_0 := h5220c.1
                        have p5220_1 := h5220c.2.1
                        have p5220_2 := h5220c.2.2.1
                        have p5220_3 := h5220c.2.2.2
                        linarith only [h5209, hc05, hlam, hphi, ht01, ht0b, ht5b, p5220_1, u1elo1]
                      · have p5220_0 := h5220c.1
                        have p5220_1 := h5220c.2.1
                        have p5220_2 := h5220c.2.2.1
                        have p5220_3 := h5220c.2.2.2
                        linarith only [hlam, p5220_0]
                      · have p5220_0 := h5220c.1
                        have p5220_1 := h5220c.2.1
                        have p5220_2 := h5220c.2.2.1
                        have p5220_3 := h5220c.2.2.2
                        linarith only [h3885, h5209, h5216, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5220_1, u1elo1]
                      · have p5220_0 := h5220c.1
                        have p5220_1 := h5220c.2.1
                        have p5220_2 := h5220c.2.2.1
                        have p5220_3 := h5220c.2.2.2
                        linarith only [h5209, hc35, hlam, hphi, ht01, ht0b, ht5b, p5220_1, u1elo1]
                      · have p5220_0 := h5220c.1
                        have p5220_1 := h5220c.2.1
                        have p5220_2 := h5220c.2.2.1
                        have p5220_3 := h5220c.2.2.2
                        linarith only [h5212, hlam, p5220_1]
                      · have p5220_0 := h5220c.1
                        have p5220_1 := h5220c.2.1
                        have p5220_2 := h5220c.2.2.1
                        have p5220_3 := h5220c.2.2.2
                        linarith only [h0, h4972, hc01, hc25, hlam, hphi, ht12, p5220_1]
                      · have p5220_0 := h5220c.1
                        have p5220_1 := h5220c.2.1
                        have p5220_2 := h5220c.2.2.1
                        have p5220_3 := h5220c.2.2.2
                        linarith only [h5209, hlam, p5220_1]
                      · have p5220_0 := h5220c.1
                        have p5220_1 := h5220c.2.1
                        have p5220_2 := h5220c.2.2.1
                        have p5220_3 := h5220c.2.2.2
                        linarith only [hlam, p5220_0]
                      · have p5220_0 := h5220c.1
                        have p5220_1 := h5220c.2.1
                        have p5220_2 := h5220c.2.2.1
                        have p5220_3 := h5220c.2.2.2
                        linarith only [h4683, h5209, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5220_1, u1elo1]
                      · have p5220_0 := h5220c.1
                        have p5220_1 := h5220c.2.1
                        have p5220_2 := h5220c.2.2.1
                        have p5220_3 := h5220c.2.2.2
                        linarith only [h5216, hlam, p5220_1]
                      · have p5220_0 := h5220c.1
                        have p5220_1 := h5220c.2.1
                        have p5220_2 := h5220c.2.2.1
                        have p5220_3 := h5220c.2.2.2
                        linarith only [h0, h4972, hc01, hc35, hlam, hphi, ht12, ht23, p5220_1]
                      · have p5220_0 := h5220c.1
                        have p5220_1 := h5220c.2.1
                        have p5220_2 := h5220c.2.2.1
                        have p5220_3 := h5220c.2.2.2
                        linarith only [h5211, hlam, p5220_0]
                      · have p5220_0 := h5220c.1
                        have p5220_1 := h5220c.2.1
                        have p5220_2 := h5220c.2.2.1
                        have p5220_3 := h5220c.2.2.2
                        linarith only [h5215, hlam, p5220_0]
                      · have p5220_0 := h5220c.1
                        have p5220_1 := h5220c.2.1
                        have p5220_2 := h5220c.2.2.1
                        have p5220_3 := h5220c.2.2.2
                        linarith only [hlam, p5220_0]
                      · have p5220_0 := h5220c.1
                        have p5220_1 := h5220c.2.1
                        have p5220_2 := h5220c.2.2.1
                        have p5220_3 := h5220c.2.2.2
                        linarith only [h5218, hlam, p5220_1]
                      · have p5220_0 := h5220c.1
                        have p5220_1 := h5220c.2.1
                        have p5220_2 := h5220c.2.2.1
                        have p5220_3 := h5220c.2.2.2
                        linarith only [h0, h4972, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5220_1]
                      · have p5220_0 := h5220c.1
                        have p5220_1 := h5220c.2.1
                        have p5220_2 := h5220c.2.2.1
                        have p5220_3 := h5220c.2.2.2
                        linarith only [h3355, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5220_1]
                      · have p5220_0 := h5220c.1
                        have p5220_1 := h5220c.2.1
                        have p5220_2 := h5220c.2.2.1
                        have p5220_3 := h5220c.2.2.2
                        linarith only [h4515, hc02, hc45, hlam, hphi, ht23, ht34, p5220_1]
                      · have p5220_0 := h5220c.1
                        have p5220_1 := h5220c.2.1
                        have p5220_2 := h5220c.2.2.1
                        have p5220_3 := h5220c.2.2.2
                        linarith only [h4683, hc03, hc45, hlam, hphi, ht34, p5220_1]
                      · have p5220_0 := h5220c.1
                        have p5220_1 := h5220c.2.1
                        have p5220_2 := h5220c.2.2.1
                        have p5220_3 := h5220c.2.2.2
                        linarith only [hlam, p5220_0]
                · linarith only [h5211, h5214, h5215, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5247 | h5247
                · linarith only [h4683, h5214, h5247, hc03, hc34, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5249 | h5249
                  · linarith only [h0, h4972, h5208, h5249, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5251 | h5251
                    · linarith only [h0, h5210, h5212, h5251, hc01, hlam, hphi, u1elo2]
                    · rcases h5bigk with h5253c | h5253c | h5253c | h5253c | h5253c | h5253c | h5253c | h5253c | h5253c | h5253c | h5253c | h5253c | h5253c | h5253c | h5253c | h5253c | h5253c | h5253c | h5253c | h5253c | h5253c | h5253c | h5253c | h5253c | h5253c
                      · have p5253_0 := h5253c.1
                        have p5253_1 := h5253c.2.1
                        have p5253_2 := h5253c.2.2.1
                        have p5253_3 := h5253c.2.2.2
                        linarith only [hlam, p5253_0]
                      · have p5253_0 := h5253c.1
                        have p5253_1 := h5253c.2.1
                        have p5253_2 := h5253c.2.2.1
                        have p5253_3 := h5253c.2.2.2
                        linarith only [h3355, hlam, p5253_1]
                      · have p5253_0 := h5253c.1
                        have p5253_1 := h5253c.2.1
                        have p5253_2 := h5253c.2.2.1
                        have p5253_3 := h5253c.2.2.2
                        linarith only [h4515, hlam, p5253_0]
                      · have p5253_0 := h5253c.1
                        have p5253_1 := h5253c.2.1
                        have p5253_2 := h5253c.2.2.1
                        have p5253_3 := h5253c.2.2.2
                        linarith only [h4683, hlam, p5253_1]
                      · have p5253_0 := h5253c.1
                        have p5253_1 := h5253c.2.1
                        have p5253_2 := h5253c.2.2.1
                        have p5253_3 := h5253c.2.2.2
                        linarith only [h4972, hlam, p5253_1]
                      · have p5253_0 := h5253c.1
                        have p5253_1 := h5253c.2.1
                        have p5253_2 := h5253c.2.2.1
                        have p5253_3 := h5253c.2.2.2
                        linarith only [h0, h4972, hc01, hlam, hphi, p5253_1, u1elo4]
                      · have p5253_0 := h5253c.1
                        have p5253_1 := h5253c.2.1
                        have p5253_2 := h5253c.2.2.1
                        have p5253_3 := h5253c.2.2.2
                        linarith only [hlam, p5253_0]
                      · have p5253_0 := h5253c.1
                        have p5253_1 := h5253c.2.1
                        have p5253_2 := h5253c.2.2.1
                        have p5253_3 := h5253c.2.2.2
                        linarith only [h3885, h5209, h5249, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5253_1, u1elo1]
                      · have p5253_0 := h5253c.1
                        have p5253_1 := h5253c.2.1
                        have p5253_2 := h5253c.2.2.1
                        have p5253_3 := h5253c.2.2.2
                        linarith only [h5209, h5214, h5251, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5253_1, u1elo1]
                      · have p5253_0 := h5253c.1
                        have p5253_1 := h5253c.2.1
                        have p5253_2 := h5253c.2.2.1
                        have p5253_3 := h5253c.2.2.2
                        linarith only [h5212, hlam, p5253_1]
                      · have p5253_0 := h5253c.1
                        have p5253_1 := h5253c.2.1
                        have p5253_2 := h5253c.2.2.1
                        have p5253_3 := h5253c.2.2.2
                        linarith only [h0, h4972, hc01, hc25, hlam, hphi, ht12, p5253_1]
                      · have p5253_0 := h5253c.1
                        have p5253_1 := h5253c.2.1
                        have p5253_2 := h5253c.2.2.1
                        have p5253_3 := h5253c.2.2.2
                        linarith only [h5209, hlam, p5253_1]
                      · have p5253_0 := h5253c.1
                        have p5253_1 := h5253c.2.1
                        have p5253_2 := h5253c.2.2.1
                        have p5253_3 := h5253c.2.2.2
                        linarith only [hlam, p5253_0]
                      · have p5253_0 := h5253c.1
                        have p5253_1 := h5253c.2.1
                        have p5253_2 := h5253c.2.2.1
                        have p5253_3 := h5253c.2.2.2
                        linarith only [h5247, hlam, p5253_1]
                      · have p5253_0 := h5253c.1
                        have p5253_1 := h5253c.2.1
                        have p5253_2 := h5253c.2.2.1
                        have p5253_3 := h5253c.2.2.2
                        linarith only [h5249, hlam, p5253_1]
                      · have p5253_0 := h5253c.1
                        have p5253_1 := h5253c.2.1
                        have p5253_2 := h5253c.2.2.1
                        have p5253_3 := h5253c.2.2.2
                        linarith only [h0, h4972, hc01, hc35, hlam, hphi, ht12, ht23, p5253_1]
                      · have p5253_0 := h5253c.1
                        have p5253_1 := h5253c.2.1
                        have p5253_2 := h5253c.2.2.1
                        have p5253_3 := h5253c.2.2.2
                        linarith only [h5211, hlam, p5253_0]
                      · have p5253_0 := h5253c.1
                        have p5253_1 := h5253c.2.1
                        have p5253_2 := h5253c.2.2.1
                        have p5253_3 := h5253c.2.2.2
                        linarith only [h5211, hc25, hlam, hphi, ht01, ht0b, ht5b, p5253_1, u1elo2]
                      · have p5253_0 := h5253c.1
                        have p5253_1 := h5253c.2.1
                        have p5253_2 := h5253c.2.2.1
                        have p5253_3 := h5253c.2.2.2
                        linarith only [hlam, p5253_0]
                      · have p5253_0 := h5253c.1
                        have p5253_1 := h5253c.2.1
                        have p5253_2 := h5253c.2.2.1
                        have p5253_3 := h5253c.2.2.2
                        linarith only [h5251, hlam, p5253_1]
                      · have p5253_0 := h5253c.1
                        have p5253_1 := h5253c.2.1
                        have p5253_2 := h5253c.2.2.1
                        have p5253_3 := h5253c.2.2.2
                        linarith only [h0, h3885, h4972, h5210, h5214, hc01, hc02, hc45, hlam, hphi, ht23, ht34, p5253_1, u1elo2]
                      · have p5253_0 := h5253c.1
                        have p5253_1 := h5253c.2.1
                        have p5253_2 := h5253c.2.2.1
                        have p5253_3 := h5253c.2.2.2
                        linarith only [h3355, h3885, h5210, h5214, hc01, hc02, hc45, hlam, hphi, ht23, ht34, p5253_1, u1elo2]
                      · have p5253_0 := h5253c.1
                        have p5253_1 := h5253c.2.1
                        have p5253_2 := h5253c.2.2.1
                        have p5253_3 := h5253c.2.2.2
                        linarith only [h4515, hc02, hc45, hlam, hphi, ht23, ht34, p5253_1]
                      · have p5253_0 := h5253c.1
                        have p5253_1 := h5253c.2.1
                        have p5253_2 := h5253c.2.2.1
                        have p5253_3 := h5253c.2.2.2
                        linarith only [h3885, h5247, h5249, hc02, hc45, hlam, hphi, ht23, ht34, p5253_1]
                      · have p5253_0 := h5253c.1
                        have p5253_1 := h5253c.2.1
                        have p5253_2 := h5253c.2.2.1
                        have p5253_3 := h5253c.2.2.2
                        linarith only [hlam, p5253_0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5279 | h5279
            · linarith only [h0, h4972, h5279, hc01, hlam, hphi, u1elo3]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5281 | h5281
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5282 | h5282
                · linarith only [h0, h5210, h5211, h5282, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5284 | h5284
                  · linarith only [h0, h5209, h5279, h5281, h5282, h5284, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5286 | h5286
                    · linarith only [h0, h5209, h5279, h5281, h5282, h5286, hc01, hlam, hphi, u1elo1]
                    · rcases h5bigk with h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c | h5288c
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [hlam, p5288_0]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h3355, hlam, p5288_1]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h4515, hlam, p5288_0]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h4683, hlam, p5288_1]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h4972, hlam, p5288_1]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h0, h4972, hc01, hlam, hphi, p5288_1, u1elo4]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [hlam, p5288_0]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h3885, h5209, h5281, h5282, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5288_1, u1elo1]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h5211, hlam, p5288_1]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h5279, hlam, p5288_1]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h0, h4972, hc01, hc25, hlam, hphi, ht12, p5288_1]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h5209, hlam, p5288_1]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [hlam, p5288_0]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h5282, hlam, p5288_1]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h5284, hlam, p5288_1]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h0, h4972, hc01, hc35, hlam, hphi, ht12, ht23, p5288_1]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h3355, h5286, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5288_1]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h4515, h5286, hc02, hc45, hlam, hphi, ht23, ht34, p5288_1]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [hlam, p5288_0]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h5286, hlam, p5288_1]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h0, h4972, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5288_1]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h0, h5210, h5211, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5288_1]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h3885, h5281, h5282, hc02, hc45, hlam, hphi, ht23, ht34, p5288_1]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [h4683, hc03, hc45, hlam, hphi, ht34, p5288_1]
                      · have p5288_0 := h5288c.1
                        have p5288_1 := h5288c.2.1
                        have p5288_2 := h5288c.2.2.1
                        have p5288_3 := h5288c.2.2.2
                        linarith only [hlam, p5288_0]
              · linarith only [h5210, h5211, h5281, hc23, hc35, hlam, hphi]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h5315 | h5315
          · linarith only [h4683, h5210, h5315, hc03, hc34, hlam, hphi]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5317 | h5317
            · linarith only [h0, h4972, h5317, hc01, hlam, hphi, u1elo3]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5319 | h5319
              · linarith only [h0, h5208, h5210, h5319, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5321 | h5321
                · linarith only [h0, h5315, h5317, h5319, h5321, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5323 | h5323
                  · linarith only [h0, h4972, h5208, h5323, hc01, hlam, hphi, u1elo3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5325 | h5325
                    · linarith only [h0, h3885, h5209, h5317, h5323, h5325, hc01, hc02, hc34, hlam, hphi, ht23, u1elo1]
                    · rcases h5bigk with h5327c | h5327c | h5327c | h5327c | h5327c | h5327c | h5327c | h5327c | h5327c | h5327c | h5327c | h5327c | h5327c | h5327c | h5327c | h5327c | h5327c | h5327c | h5327c | h5327c | h5327c | h5327c | h5327c | h5327c | h5327c
                      · have p5327_0 := h5327c.1
                        have p5327_1 := h5327c.2.1
                        have p5327_2 := h5327c.2.2.1
                        have p5327_3 := h5327c.2.2.2
                        linarith only [hlam, p5327_0]
                      · have p5327_0 := h5327c.1
                        have p5327_1 := h5327c.2.1
                        have p5327_2 := h5327c.2.2.1
                        have p5327_3 := h5327c.2.2.2
                        linarith only [h3355, hlam, p5327_1]
                      · have p5327_0 := h5327c.1
                        have p5327_1 := h5327c.2.1
                        have p5327_2 := h5327c.2.2.1
                        have p5327_3 := h5327c.2.2.2
                        linarith only [h4515, hlam, p5327_0]
                      · have p5327_0 := h5327c.1
                        have p5327_1 := h5327c.2.1
                        have p5327_2 := h5327c.2.2.1
                        have p5327_3 := h5327c.2.2.2
                        linarith only [h4683, hlam, p5327_1]
                      · have p5327_0 := h5327c.1
                        have p5327_1 := h5327c.2.1
                        have p5327_2 := h5327c.2.2.1
                        have p5327_3 := h5327c.2.2.2
                        linarith only [h4972, hlam, p5327_1]
                      · have p5327_0 := h5327c.1
                        have p5327_1 := h5327c.2.1
                        have p5327_2 := h5327c.2.2.1
                        have p5327_3 := h5327c.2.2.2
                        linarith only [h0, h4972, h5209, hc01, hlam, hphi, p5327_1, u1elo1]
                      · have p5327_0 := h5327c.1
                        have p5327_1 := h5327c.2.1
                        have p5327_2 := h5327c.2.2.1
                        have p5327_3 := h5327c.2.2.2
                        linarith only [hlam, p5327_0]
                      · have p5327_0 := h5327c.1
                        have p5327_1 := h5327c.2.1
                        have p5327_2 := h5327c.2.2.1
                        have p5327_3 := h5327c.2.2.2
                        linarith only [h3885, h5209, h5323, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5327_1, u1elo1]
                      · have p5327_0 := h5327c.1
                        have p5327_1 := h5327c.2.1
                        have p5327_2 := h5327c.2.2.1
                        have p5327_3 := h5327c.2.2.2
                        linarith only [h5315, hlam, p5327_1]
                      · have p5327_0 := h5327c.1
                        have p5327_1 := h5327c.2.1
                        have p5327_2 := h5327c.2.2.1
                        have p5327_3 := h5327c.2.2.2
                        linarith only [h5317, hlam, p5327_1]
                      · have p5327_0 := h5327c.1
                        have p5327_1 := h5327c.2.1
                        have p5327_2 := h5327c.2.2.1
                        have p5327_3 := h5327c.2.2.2
                        linarith only [h0, h4972, hc01, hc25, hlam, hphi, ht12, p5327_1]
                      · have p5327_0 := h5327c.1
                        have p5327_1 := h5327c.2.1
                        have p5327_2 := h5327c.2.2.1
                        have p5327_3 := h5327c.2.2.2
                        linarith only [h5209, hlam, p5327_1]
                      · have p5327_0 := h5327c.1
                        have p5327_1 := h5327c.2.1
                        have p5327_2 := h5327c.2.2.1
                        have p5327_3 := h5327c.2.2.2
                        linarith only [hlam, p5327_0]
                      · have p5327_0 := h5327c.1
                        have p5327_1 := h5327c.2.1
                        have p5327_2 := h5327c.2.2.1
                        have p5327_3 := h5327c.2.2.2
                        linarith only [h5321, hlam, p5327_1]
                      · have p5327_0 := h5327c.1
                        have p5327_1 := h5327c.2.1
                        have p5327_2 := h5327c.2.2.1
                        have p5327_3 := h5327c.2.2.2
                        linarith only [h5323, hlam, p5327_1]
                      · have p5327_0 := h5327c.1
                        have p5327_1 := h5327c.2.1
                        have p5327_2 := h5327c.2.2.1
                        have p5327_3 := h5327c.2.2.2
                        linarith only [h0, h4972, hc01, hc35, hlam, hphi, ht12, ht23, p5327_1]
                      · have p5327_0 := h5327c.1
                        have p5327_1 := h5327c.2.1
                        have p5327_2 := h5327c.2.2.1
                        have p5327_3 := h5327c.2.2.2
                        linarith only [h3355, hc01, hc35, hlam, hphi, ht12, ht23, p5327_1]
                      · have p5327_0 := h5327c.1
                        have p5327_1 := h5327c.2.1
                        have p5327_2 := h5327c.2.2.1
                        have p5327_3 := h5327c.2.2.2
                        linarith only [h4515, hc02, hc35, hlam, hphi, ht23, p5327_1]
                      · have p5327_0 := h5327c.1
                        have p5327_1 := h5327c.2.1
                        have p5327_2 := h5327c.2.2.1
                        have p5327_3 := h5327c.2.2.2
                        linarith only [hlam, p5327_0]
                      · have p5327_0 := h5327c.1
                        have p5327_1 := h5327c.2.1
                        have p5327_2 := h5327c.2.2.1
                        have p5327_3 := h5327c.2.2.2
                        linarith only [h5325, hlam, p5327_1]
                      · have p5327_0 := h5327c.1
                        have p5327_1 := h5327c.2.1
                        have p5327_2 := h5327c.2.2.1
                        have p5327_3 := h5327c.2.2.2
                        linarith only [h0, h4972, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5327_1]
                      · have p5327_0 := h5327c.1
                        have p5327_1 := h5327c.2.1
                        have p5327_2 := h5327c.2.2.1
                        have p5327_3 := h5327c.2.2.2
                        linarith only [h0, h5317, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5327_1]
                      · have p5327_0 := h5327c.1
                        have p5327_1 := h5327c.2.1
                        have p5327_2 := h5327c.2.2.1
                        have p5327_3 := h5327c.2.2.2
                        linarith only [h4515, hc02, hc45, hlam, hphi, ht23, ht34, p5327_1]
                      · have p5327_0 := h5327c.1
                        have p5327_1 := h5327c.2.1
                        have p5327_2 := h5327c.2.2.1
                        have p5327_3 := h5327c.2.2.2
                        linarith only [h4683, hc03, hc45, hlam, hphi, ht34, p5327_1]
                      · have p5327_0 := h5327c.1
                        have p5327_1 := h5327c.2.1
                        have p5327_2 := h5327c.2.2.1
                        have p5327_3 := h5327c.2.2.2
                        linarith only [hlam, p5327_0]
      · linarith only [h3885, h5208, h5209, hc02, hc25, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h5354 | h5354
      · linarith only [h4515, h5208, h5354, hc02, hc24, hlam, hphi]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h5356 | h5356
        · rcases m.htr 1 3 5 (by decide) (by decide) with h5357 | h5357
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5358 | h5358
            · linarith only [h0, h4972, h5356, h5358, hc01, hlam, hphi, u1elo2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5360 | h5360
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5361 | h5361
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5362 | h5362
                  · linarith only [h0, h5358, h5360, h5362, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5364 | h5364
                    · linarith only [h5208, h5356, h5362, h5364, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                    · rcases h5bigk with h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c
                      · have p5366_0 := h5366c.1
                        have p5366_1 := h5366c.2.1
                        have p5366_2 := h5366c.2.2.1
                        have p5366_3 := h5366c.2.2.2
                        linarith only [hlam, p5366_0]
                      · have p5366_0 := h5366c.1
                        have p5366_1 := h5366c.2.1
                        have p5366_2 := h5366c.2.2.1
                        have p5366_3 := h5366c.2.2.2
                        linarith only [h3355, hlam, p5366_1]
                      · have p5366_0 := h5366c.1
                        have p5366_1 := h5366c.2.1
                        have p5366_2 := h5366c.2.2.1
                        have p5366_3 := h5366c.2.2.2
                        linarith only [h4515, hlam, p5366_0]
                      · have p5366_0 := h5366c.1
                        have p5366_1 := h5366c.2.1
                        have p5366_2 := h5366c.2.2.1
                        have p5366_3 := h5366c.2.2.2
                        linarith only [h4683, hlam, p5366_1]
                      · have p5366_0 := h5366c.1
                        have p5366_1 := h5366c.2.1
                        have p5366_2 := h5366c.2.2.1
                        have p5366_3 := h5366c.2.2.2
                        linarith only [h4972, hlam, p5366_1]
                      · have p5366_0 := h5366c.1
                        have p5366_1 := h5366c.2.1
                        have p5366_2 := h5366c.2.2.1
                        have p5366_3 := h5366c.2.2.2
                        linarith only [h0, h4972, hc01, hlam, hphi, p5366_1, u1elo4]
                      · have p5366_0 := h5366c.1
                        have p5366_1 := h5366c.2.1
                        have p5366_2 := h5366c.2.2.1
                        have p5366_3 := h5366c.2.2.2
                        linarith only [hlam, p5366_0]
                      · have p5366_0 := h5366c.1
                        have p5366_1 := h5366c.2.1
                        have p5366_2 := h5366c.2.2.1
                        have p5366_3 := h5366c.2.2.2
                        linarith only [h5354, hlam, p5366_0]
                      · have p5366_0 := h5366c.1
                        have p5366_1 := h5366c.2.1
                        have p5366_2 := h5366c.2.2.1
                        have p5366_3 := h5366c.2.2.2
                        linarith only [h4683, h5357, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5366_1, u1elo2]
                      · have p5366_0 := h5366c.1
                        have p5366_1 := h5366c.2.1
                        have p5366_2 := h5366c.2.2.1
                        have p5366_3 := h5366c.2.2.2
                        linarith only [h5358, hlam, p5366_1]
                      · have p5366_0 := h5366c.1
                        have p5366_1 := h5366c.2.1
                        have p5366_2 := h5366c.2.2.1
                        have p5366_3 := h5366c.2.2.2
                        linarith only [h0, h4972, hc01, hc25, hlam, hphi, ht12, p5366_1]
                      · have p5366_0 := h5366c.1
                        have p5366_1 := h5366c.2.1
                        have p5366_2 := h5366c.2.2.1
                        have p5366_3 := h5366c.2.2.2
                        linarith only [h3355, hc01, hc25, hlam, hphi, ht12, p5366_1]
                      · have p5366_0 := h5366c.1
                        have p5366_1 := h5366c.2.1
                        have p5366_2 := h5366c.2.2.1
                        have p5366_3 := h5366c.2.2.2
                        linarith only [hlam, p5366_0]
                      · have p5366_0 := h5366c.1
                        have p5366_1 := h5366c.2.1
                        have p5366_2 := h5366c.2.2.1
                        have p5366_3 := h5366c.2.2.2
                        linarith only [h4683, h5361, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p5366_1]
                      · have p5366_0 := h5366c.1
                        have p5366_1 := h5366c.2.1
                        have p5366_2 := h5366c.2.2.1
                        have p5366_3 := h5366c.2.2.2
                        linarith only [h5362, hlam, p5366_1]
                      · have p5366_0 := h5366c.1
                        have p5366_1 := h5366c.2.1
                        have p5366_2 := h5366c.2.2.1
                        have p5366_3 := h5366c.2.2.2
                        linarith only [h0, h4972, hc01, hc35, hlam, hphi, ht12, ht23, p5366_1]
                      · have p5366_0 := h5366c.1
                        have p5366_1 := h5366c.2.1
                        have p5366_2 := h5366c.2.2.1
                        have p5366_3 := h5366c.2.2.2
                        linarith only [h5357, hlam, p5366_0]
                      · have p5366_0 := h5366c.1
                        have p5366_1 := h5366c.2.1
                        have p5366_2 := h5366c.2.2.1
                        have p5366_3 := h5366c.2.2.2
                        linarith only [h5361, hlam, p5366_0]
                      · have p5366_0 := h5366c.1
                        have p5366_1 := h5366c.2.1
                        have p5366_2 := h5366c.2.2.1
                        have p5366_3 := h5366c.2.2.2
                        linarith only [hlam, p5366_0]
                      · have p5366_0 := h5366c.1
                        have p5366_1 := h5366c.2.1
                        have p5366_2 := h5366c.2.2.1
                        have p5366_3 := h5366c.2.2.2
                        linarith only [h5364, hlam, p5366_1]
                      · have p5366_0 := h5366c.1
                        have p5366_1 := h5366c.2.1
                        have p5366_2 := h5366c.2.2.1
                        have p5366_3 := h5366c.2.2.2
                        linarith only [h0, h4972, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5366_1]
                      · have p5366_0 := h5366c.1
                        have p5366_1 := h5366c.2.1
                        have p5366_2 := h5366c.2.2.1
                        have p5366_3 := h5366c.2.2.2
                        linarith only [h0, h5358, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5366_1]
                      · have p5366_0 := h5366c.1
                        have p5366_1 := h5366c.2.1
                        have p5366_2 := h5366c.2.2.1
                        have p5366_3 := h5366c.2.2.2
                        linarith only [h4515, hc02, hc45, hlam, hphi, ht23, ht34, p5366_1]
                      · have p5366_0 := h5366c.1
                        have p5366_1 := h5366c.2.1
                        have p5366_2 := h5366c.2.2.1
                        have p5366_3 := h5366c.2.2.2
                        linarith only [h4683, hc03, hc45, hlam, hphi, ht34, p5366_1]
                      · have p5366_0 := h5366c.1
                        have p5366_1 := h5366c.2.1
                        have p5366_2 := h5366c.2.2.1
                        have p5366_3 := h5366c.2.2.2
                        linarith only [hlam, p5366_0]
                · linarith only [h5357, h5360, h5361, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
              · linarith only [h0, h5208, h5356, h5360, hc01, hlam, hphi, u1elo2]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5394 | h5394
            · linarith only [h0, h4972, h5356, h5394, hc01, hlam, hphi, u1elo2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5396 | h5396
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5397 | h5397
                · linarith only [h0, h5356, h5357, h5397, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5399 | h5399
                  · linarith only [h0, h4972, h5396, h5397, h5399, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5401 | h5401
                    · linarith only [h5208, h5356, h5399, h5401, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                    · rcases h5bigk with h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c | h5403c
                      · have p5403_0 := h5403c.1
                        have p5403_1 := h5403c.2.1
                        have p5403_2 := h5403c.2.2.1
                        have p5403_3 := h5403c.2.2.2
                        linarith only [hlam, p5403_0]
                      · have p5403_0 := h5403c.1
                        have p5403_1 := h5403c.2.1
                        have p5403_2 := h5403c.2.2.1
                        have p5403_3 := h5403c.2.2.2
                        linarith only [h3355, hlam, p5403_1]
                      · have p5403_0 := h5403c.1
                        have p5403_1 := h5403c.2.1
                        have p5403_2 := h5403c.2.2.1
                        have p5403_3 := h5403c.2.2.2
                        linarith only [h4515, hlam, p5403_0]
                      · have p5403_0 := h5403c.1
                        have p5403_1 := h5403c.2.1
                        have p5403_2 := h5403c.2.2.1
                        have p5403_3 := h5403c.2.2.2
                        linarith only [h4683, hlam, p5403_1]
                      · have p5403_0 := h5403c.1
                        have p5403_1 := h5403c.2.1
                        have p5403_2 := h5403c.2.2.1
                        have p5403_3 := h5403c.2.2.2
                        linarith only [h4972, hlam, p5403_1]
                      · have p5403_0 := h5403c.1
                        have p5403_1 := h5403c.2.1
                        have p5403_2 := h5403c.2.2.1
                        have p5403_3 := h5403c.2.2.2
                        linarith only [h0, h4972, hc01, hlam, hphi, p5403_1, u1elo4]
                      · have p5403_0 := h5403c.1
                        have p5403_1 := h5403c.2.1
                        have p5403_2 := h5403c.2.2.1
                        have p5403_3 := h5403c.2.2.2
                        linarith only [hlam, p5403_0]
                      · have p5403_0 := h5403c.1
                        have p5403_1 := h5403c.2.1
                        have p5403_2 := h5403c.2.2.1
                        have p5403_3 := h5403c.2.2.2
                        linarith only [h5354, hlam, p5403_0]
                      · have p5403_0 := h5403c.1
                        have p5403_1 := h5403c.2.1
                        have p5403_2 := h5403c.2.2.1
                        have p5403_3 := h5403c.2.2.2
                        linarith only [h5357, hlam, p5403_1]
                      · have p5403_0 := h5403c.1
                        have p5403_1 := h5403c.2.1
                        have p5403_2 := h5403c.2.2.1
                        have p5403_3 := h5403c.2.2.2
                        linarith only [h5394, hlam, p5403_1]
                      · have p5403_0 := h5403c.1
                        have p5403_1 := h5403c.2.1
                        have p5403_2 := h5403c.2.2.1
                        have p5403_3 := h5403c.2.2.2
                        linarith only [h0, h4972, hc01, hc25, hlam, hphi, ht12, p5403_1]
                      · have p5403_0 := h5403c.1
                        have p5403_1 := h5403c.2.1
                        have p5403_2 := h5403c.2.2.1
                        have p5403_3 := h5403c.2.2.2
                        linarith only [h3355, hc01, hc25, hlam, hphi, ht12, p5403_1]
                      · have p5403_0 := h5403c.1
                        have p5403_1 := h5403c.2.1
                        have p5403_2 := h5403c.2.2.1
                        have p5403_3 := h5403c.2.2.2
                        linarith only [hlam, p5403_0]
                      · have p5403_0 := h5403c.1
                        have p5403_1 := h5403c.2.1
                        have p5403_2 := h5403c.2.2.1
                        have p5403_3 := h5403c.2.2.2
                        linarith only [h5397, hlam, p5403_1]
                      · have p5403_0 := h5403c.1
                        have p5403_1 := h5403c.2.1
                        have p5403_2 := h5403c.2.2.1
                        have p5403_3 := h5403c.2.2.2
                        linarith only [h5399, hlam, p5403_1]
                      · have p5403_0 := h5403c.1
                        have p5403_1 := h5403c.2.1
                        have p5403_2 := h5403c.2.2.1
                        have p5403_3 := h5403c.2.2.2
                        linarith only [h0, h4972, h5401, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5403_1]
                      · have p5403_0 := h5403c.1
                        have p5403_1 := h5403c.2.1
                        have p5403_2 := h5403c.2.2.1
                        have p5403_3 := h5403c.2.2.2
                        linarith only [h3355, h5401, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5403_1]
                      · have p5403_0 := h5403c.1
                        have p5403_1 := h5403c.2.1
                        have p5403_2 := h5403c.2.2.1
                        have p5403_3 := h5403c.2.2.2
                        linarith only [h4515, h5401, hc02, hc45, hlam, hphi, ht23, ht34, p5403_1]
                      · have p5403_0 := h5403c.1
                        have p5403_1 := h5403c.2.1
                        have p5403_2 := h5403c.2.2.1
                        have p5403_3 := h5403c.2.2.2
                        linarith only [hlam, p5403_0]
                      · have p5403_0 := h5403c.1
                        have p5403_1 := h5403c.2.1
                        have p5403_2 := h5403c.2.2.1
                        have p5403_3 := h5403c.2.2.2
                        linarith only [h5401, hlam, p5403_1]
                      · have p5403_0 := h5403c.1
                        have p5403_1 := h5403c.2.1
                        have p5403_2 := h5403c.2.2.1
                        have p5403_3 := h5403c.2.2.2
                        linarith only [h0, h4972, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5403_1]
                      · have p5403_0 := h5403c.1
                        have p5403_1 := h5403c.2.1
                        have p5403_2 := h5403c.2.2.1
                        have p5403_3 := h5403c.2.2.2
                        linarith only [h5357, hc13, hc45, hlam, hphi, ht34, p5403_1]
                      · have p5403_0 := h5403c.1
                        have p5403_1 := h5403c.2.1
                        have p5403_2 := h5403c.2.2.1
                        have p5403_3 := h5403c.2.2.2
                        linarith only [h0, h5354, h5356, h5357, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5403_1]
                      · have p5403_0 := h5403c.1
                        have p5403_1 := h5403c.2.1
                        have p5403_2 := h5403c.2.2.1
                        have p5403_3 := h5403c.2.2.2
                        linarith only [h0, h5208, h5396, h5397, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5403_1]
                      · have p5403_0 := h5403c.1
                        have p5403_1 := h5403c.2.1
                        have p5403_2 := h5403c.2.2.1
                        have p5403_3 := h5403c.2.2.2
                        linarith only [hlam, p5403_0]
              · linarith only [h5356, h5357, h5396, hc23, hc35, hlam, hphi]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h5430 | h5430
          · linarith only [h4683, h5356, h5430, hc03, hc34, hlam, hphi]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5432 | h5432
            · linarith only [h0, h4972, h5432, hc01, hlam, hphi, u1elo3]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5434 | h5434
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5435 | h5435
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5436 | h5436
                  · linarith only [h0, h5432, h5436, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5438 | h5438
                    · linarith only [h5434, h5436, h5438, hlam]
                    · rcases h5bigk with h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c
                      · have p5440_0 := h5440c.1
                        have p5440_1 := h5440c.2.1
                        have p5440_2 := h5440c.2.2.1
                        have p5440_3 := h5440c.2.2.2
                        linarith only [hlam, p5440_0]
                      · have p5440_0 := h5440c.1
                        have p5440_1 := h5440c.2.1
                        have p5440_2 := h5440c.2.2.1
                        have p5440_3 := h5440c.2.2.2
                        linarith only [h3355, hlam, p5440_1]
                      · have p5440_0 := h5440c.1
                        have p5440_1 := h5440c.2.1
                        have p5440_2 := h5440c.2.2.1
                        have p5440_3 := h5440c.2.2.2
                        linarith only [h4515, hlam, p5440_0]
                      · have p5440_0 := h5440c.1
                        have p5440_1 := h5440c.2.1
                        have p5440_2 := h5440c.2.2.1
                        have p5440_3 := h5440c.2.2.2
                        linarith only [h4683, hlam, p5440_1]
                      · have p5440_0 := h5440c.1
                        have p5440_1 := h5440c.2.1
                        have p5440_2 := h5440c.2.2.1
                        have p5440_3 := h5440c.2.2.2
                        linarith only [h4972, hlam, p5440_1]
                      · have p5440_0 := h5440c.1
                        have p5440_1 := h5440c.2.1
                        have p5440_2 := h5440c.2.2.1
                        have p5440_3 := h5440c.2.2.2
                        linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p5440_1, u1elo4]
                      · have p5440_0 := h5440c.1
                        have p5440_1 := h5440c.2.1
                        have p5440_2 := h5440c.2.2.1
                        have p5440_3 := h5440c.2.2.2
                        linarith only [hlam, p5440_0]
                      · have p5440_0 := h5440c.1
                        have p5440_1 := h5440c.2.1
                        have p5440_2 := h5440c.2.2.1
                        have p5440_3 := h5440c.2.2.2
                        linarith only [h5354, hlam, p5440_0]
                      · have p5440_0 := h5440c.1
                        have p5440_1 := h5440c.2.1
                        have p5440_2 := h5440c.2.2.1
                        have p5440_3 := h5440c.2.2.2
                        linarith only [h5430, hlam, p5440_1]
                      · have p5440_0 := h5440c.1
                        have p5440_1 := h5440c.2.1
                        have p5440_2 := h5440c.2.2.1
                        have p5440_3 := h5440c.2.2.2
                        linarith only [h5432, hlam, p5440_1]
                      · have p5440_0 := h5440c.1
                        have p5440_1 := h5440c.2.1
                        have p5440_2 := h5440c.2.2.1
                        have p5440_3 := h5440c.2.2.2
                        linarith only [h3355, hc01, hc25, hlam, hphi, ht12, p5440_1]
                      · have p5440_0 := h5440c.1
                        have p5440_1 := h5440c.2.1
                        have p5440_2 := h5440c.2.2.1
                        have p5440_3 := h5440c.2.2.2
                        linarith only [h3355, hc01, hc25, hlam, hphi, ht12, p5440_1]
                      · have p5440_0 := h5440c.1
                        have p5440_1 := h5440c.2.1
                        have p5440_2 := h5440c.2.2.1
                        have p5440_3 := h5440c.2.2.2
                        linarith only [hlam, p5440_0]
                      · have p5440_0 := h5440c.1
                        have p5440_1 := h5440c.2.1
                        have p5440_2 := h5440c.2.2.1
                        have p5440_3 := h5440c.2.2.2
                        linarith only [h0, h5356, h5435, h5438, hc01, hc23, hlam, hphi, ht12, p5440_1]
                      · have p5440_0 := h5440c.1
                        have p5440_1 := h5440c.2.1
                        have p5440_2 := h5440c.2.2.1
                        have p5440_3 := h5440c.2.2.2
                        linarith only [h5436, hlam, p5440_1]
                      · have p5440_0 := h5440c.1
                        have p5440_1 := h5440c.2.1
                        have p5440_2 := h5440c.2.2.1
                        have p5440_3 := h5440c.2.2.2
                        linarith only [h0, h4972, hc01, hc35, hlam, hphi, ht12, ht23, p5440_1]
                      · have p5440_0 := h5440c.1
                        have p5440_1 := h5440c.2.1
                        have p5440_2 := h5440c.2.2.1
                        have p5440_3 := h5440c.2.2.2
                        linarith only [h0, h5432, hc01, hc35, hlam, hphi, ht12, ht23, p5440_1]
                      · have p5440_0 := h5440c.1
                        have p5440_1 := h5440c.2.1
                        have p5440_2 := h5440c.2.2.1
                        have p5440_3 := h5440c.2.2.2
                        linarith only [h5435, hlam, p5440_0]
                      · have p5440_0 := h5440c.1
                        have p5440_1 := h5440c.2.1
                        have p5440_2 := h5440c.2.2.1
                        have p5440_3 := h5440c.2.2.2
                        linarith only [hlam, p5440_0]
                      · have p5440_0 := h5440c.1
                        have p5440_1 := h5440c.2.1
                        have p5440_2 := h5440c.2.2.1
                        have p5440_3 := h5440c.2.2.2
                        linarith only [h5438, hlam, p5440_1]
                      · have p5440_0 := h5440c.1
                        have p5440_1 := h5440c.2.1
                        have p5440_2 := h5440c.2.2.1
                        have p5440_3 := h5440c.2.2.2
                        linarith only [h0, h4972, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5440_1]
                      · have p5440_0 := h5440c.1
                        have p5440_1 := h5440c.2.1
                        have p5440_2 := h5440c.2.2.1
                        have p5440_3 := h5440c.2.2.2
                        linarith only [h0, h5432, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5440_1]
                      · have p5440_0 := h5440c.1
                        have p5440_1 := h5440c.2.1
                        have p5440_2 := h5440c.2.2.1
                        have p5440_3 := h5440c.2.2.2
                        linarith only [h4515, hc02, hc45, hlam, hphi, ht23, ht34, p5440_1]
                      · have p5440_0 := h5440c.1
                        have p5440_1 := h5440c.2.1
                        have p5440_2 := h5440c.2.2.1
                        have p5440_3 := h5440c.2.2.2
                        linarith only [h4683, hc03, hc45, hlam, hphi, ht34, p5440_1]
                      · have p5440_0 := h5440c.1
                        have p5440_1 := h5440c.2.1
                        have p5440_2 := h5440c.2.2.1
                        have p5440_3 := h5440c.2.2.2
                        linarith only [hlam, p5440_0]
                · linarith only [h0, h5356, h5434, h5435, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5467 | h5467
                · linarith only [h4683, h5434, h5467, hc03, hc34, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5469 | h5469
                  · linarith only [h0, h5432, h5469, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5471 | h5471
                    · linarith only [h0, h5432, h5471, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases h5bigk with h5473c | h5473c | h5473c | h5473c | h5473c | h5473c | h5473c | h5473c | h5473c | h5473c | h5473c | h5473c | h5473c | h5473c | h5473c | h5473c | h5473c | h5473c | h5473c | h5473c | h5473c | h5473c | h5473c | h5473c | h5473c
                      · have p5473_0 := h5473c.1
                        have p5473_1 := h5473c.2.1
                        have p5473_2 := h5473c.2.2.1
                        have p5473_3 := h5473c.2.2.2
                        linarith only [hlam, p5473_0]
                      · have p5473_0 := h5473c.1
                        have p5473_1 := h5473c.2.1
                        have p5473_2 := h5473c.2.2.1
                        have p5473_3 := h5473c.2.2.2
                        linarith only [h3355, hlam, p5473_1]
                      · have p5473_0 := h5473c.1
                        have p5473_1 := h5473c.2.1
                        have p5473_2 := h5473c.2.2.1
                        have p5473_3 := h5473c.2.2.2
                        linarith only [h4515, hlam, p5473_0]
                      · have p5473_0 := h5473c.1
                        have p5473_1 := h5473c.2.1
                        have p5473_2 := h5473c.2.2.1
                        have p5473_3 := h5473c.2.2.2
                        linarith only [h4683, hlam, p5473_1]
                      · have p5473_0 := h5473c.1
                        have p5473_1 := h5473c.2.1
                        have p5473_2 := h5473c.2.2.1
                        have p5473_3 := h5473c.2.2.2
                        linarith only [h4972, hlam, p5473_1]
                      · have p5473_0 := h5473c.1
                        have p5473_1 := h5473c.2.1
                        have p5473_2 := h5473c.2.2.1
                        have p5473_3 := h5473c.2.2.2
                        linarith only [h0, h4972, hc01, hlam, hphi, p5473_1, u1elo4]
                      · have p5473_0 := h5473c.1
                        have p5473_1 := h5473c.2.1
                        have p5473_2 := h5473c.2.2.1
                        have p5473_3 := h5473c.2.2.2
                        linarith only [hlam, p5473_0]
                      · have p5473_0 := h5473c.1
                        have p5473_1 := h5473c.2.1
                        have p5473_2 := h5473c.2.2.1
                        have p5473_3 := h5473c.2.2.2
                        linarith only [h5354, hlam, p5473_0]
                      · have p5473_0 := h5473c.1
                        have p5473_1 := h5473c.2.1
                        have p5473_2 := h5473c.2.2.1
                        have p5473_3 := h5473c.2.2.2
                        linarith only [h5430, hlam, p5473_1]
                      · have p5473_0 := h5473c.1
                        have p5473_1 := h5473c.2.1
                        have p5473_2 := h5473c.2.2.1
                        have p5473_3 := h5473c.2.2.2
                        linarith only [h5432, hlam, p5473_1]
                      · have p5473_0 := h5473c.1
                        have p5473_1 := h5473c.2.1
                        have p5473_2 := h5473c.2.2.1
                        have p5473_3 := h5473c.2.2.2
                        linarith only [h0, h4972, hc01, hc25, hlam, hphi, ht12, p5473_1]
                      · have p5473_0 := h5473c.1
                        have p5473_1 := h5473c.2.1
                        have p5473_2 := h5473c.2.2.1
                        have p5473_3 := h5473c.2.2.2
                        linarith only [h3355, h5467, hc01, hc35, hlam, hphi, ht12, ht23, p5473_1]
                      · have p5473_0 := h5473c.1
                        have p5473_1 := h5473c.2.1
                        have p5473_2 := h5473c.2.2.1
                        have p5473_3 := h5473c.2.2.2
                        linarith only [hlam, p5473_0]
                      · have p5473_0 := h5473c.1
                        have p5473_1 := h5473c.2.1
                        have p5473_2 := h5473c.2.2.1
                        have p5473_3 := h5473c.2.2.2
                        linarith only [h5467, hlam, p5473_1]
                      · have p5473_0 := h5473c.1
                        have p5473_1 := h5473c.2.1
                        have p5473_2 := h5473c.2.2.1
                        have p5473_3 := h5473c.2.2.2
                        linarith only [h5469, hlam, p5473_1]
                      · have p5473_0 := h5473c.1
                        have p5473_1 := h5473c.2.1
                        have p5473_2 := h5473c.2.2.1
                        have p5473_3 := h5473c.2.2.2
                        linarith only [h0, h4972, hc01, hc35, hlam, hphi, ht12, ht23, p5473_1]
                      · have p5473_0 := h5473c.1
                        have p5473_1 := h5473c.2.1
                        have p5473_2 := h5473c.2.2.1
                        have p5473_3 := h5473c.2.2.2
                        linarith only [h3355, hc01, hc35, hlam, hphi, ht12, ht23, p5473_1]
                      · have p5473_0 := h5473c.1
                        have p5473_1 := h5473c.2.1
                        have p5473_2 := h5473c.2.2.1
                        have p5473_3 := h5473c.2.2.2
                        linarith only [h4515, hc02, hc35, hlam, hphi, ht23, p5473_1]
                      · have p5473_0 := h5473c.1
                        have p5473_1 := h5473c.2.1
                        have p5473_2 := h5473c.2.2.1
                        have p5473_3 := h5473c.2.2.2
                        linarith only [hlam, p5473_0]
                      · have p5473_0 := h5473c.1
                        have p5473_1 := h5473c.2.1
                        have p5473_2 := h5473c.2.2.1
                        have p5473_3 := h5473c.2.2.2
                        linarith only [h5471, hlam, p5473_1]
                      · have p5473_0 := h5473c.1
                        have p5473_1 := h5473c.2.1
                        have p5473_2 := h5473c.2.2.1
                        have p5473_3 := h5473c.2.2.2
                        linarith only [h0, h4972, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5473_1]
                      · have p5473_0 := h5473c.1
                        have p5473_1 := h5473c.2.1
                        have p5473_2 := h5473c.2.2.1
                        have p5473_3 := h5473c.2.2.2
                        linarith only [h3355, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5473_1]
                      · have p5473_0 := h5473c.1
                        have p5473_1 := h5473c.2.1
                        have p5473_2 := h5473c.2.2.1
                        have p5473_3 := h5473c.2.2.2
                        linarith only [h0, h5354, h5432, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p5473_1]
                      · have p5473_0 := h5473c.1
                        have p5473_1 := h5473c.2.1
                        have p5473_2 := h5473c.2.2.1
                        have p5473_3 := h5473c.2.2.2
                        linarith only [h4683, hc03, hc45, hlam, hphi, ht34, p5473_1]
                      · have p5473_0 := h5473c.1
                        have p5473_1 := h5473c.2.1
                        have p5473_2 := h5473c.2.2.1
                        have p5473_3 := h5473c.2.2.2
                        linarith only [hlam, p5473_0]

set_option maxHeartbeats 10998000 in
set_option maxHeartbeats 10998000 in
theorem r1l7_11_25_L_0_H_I_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3355 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3885 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h4515 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h4683 | h4683
  · exact r1l7_11_25_L_0_H_I_x1_x1_x1_x1_x0 m hb1 hb5 h0 h3355 h3885 h4515 h4683
  · exact r1l7_11_25_L_0_H_I_x1_x1_x1_x1_x1 m hb1 hb5 h0 h3355 h3885 h4515 h4683

set_option maxHeartbeats 10998000 in
set_option maxHeartbeats 10998000 in
theorem r1l7_11_25_L_0_H_I_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3355 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h3885 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h4515 | h4515
  · exact r1l7_11_25_L_0_H_I_x1_x1_x1_x0 m hb1 hb5 h0 h3355 h3885 h4515
  · exact r1l7_11_25_L_0_H_I_x1_x1_x1_x1 m hb1 hb5 h0 h3355 h3885 h4515

set_option maxHeartbeats 10998000 in
set_option maxHeartbeats 10998000 in
theorem r1l7_11_25_L_0_H_I_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h3355 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h3885 | h3885
  · exact r1l7_11_25_L_0_H_I_x1_x1_x0 m hb1 hb5 h0 h3355 h3885
  · exact r1l7_11_25_L_0_H_I_x1_x1_x1 m hb1 hb5 h0 h3355 h3885

set_option maxHeartbeats 10998000 in
set_option maxHeartbeats 10998000 in
theorem r1l7_11_25_L_0_H_I_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3355 | h3355
  · exact r1l7_11_25_L_0_H_I_x1_x0 m hb1 hb5 h0 h3355
  · exact r1l7_11_25_L_0_H_I_x1_x1 m hb1 hb5 h0 h3355

set_option maxHeartbeats 10998000 in
set_option maxHeartbeats 10998000 in
theorem r1l7_11_25_L_0_H_I (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h1elo := hb1.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_25_L_0_H_I_x0 m hb1 hb5 h0
  · exact r1l7_11_25_L_0_H_I_x1 m hb1 hb5 h0

end R2N4
