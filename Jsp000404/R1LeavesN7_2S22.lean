import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_2S20
import Jsp000404.R1LeavesN7_2S21

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 28790000 in
set_option maxHeartbeats 28790000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s0_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h13364 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h14017 | h14017
  · rcases m.htr 0 2 3 (by decide) (by decide) with h14018 | h14018
    · linarith only [h0, h1, h14018, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h14020 | h14020
      · linarith only [h0, h13364, h14020, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h14022 | h14022
        · rcases m.htr 0 3 4 (by decide) (by decide) with h14023 | h14023
          · rcases m.htr 0 3 5 (by decide) (by decide) with h14024 | h14024
            · rcases m.htr 0 4 5 (by decide) (by decide) with h14025 | h14025
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14026 | h14026
                · linarith only [h0, h1, h14018, h14022, h14026, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h14028 | h14028
                  · linarith only [h0, h13364, h14020, h14028, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h14030 | h14030
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h14031 | h14031
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h14032 | h14032
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h14033 | h14033
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h14034 | h14034
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h14035 | h14035
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h14036 | h14036
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h14037 | h14037
                                  · rcases h0bigk with h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c
                                    · have p14038_0 := h14038c.1
                                      have p14038_1 := h14038c.2.1
                                      have p14038_2 := h14038c.2.2.1
                                      have p14038_3 := h14038c.2.2.2
                                      linarith only [hlam, p14038_0]
                                    · have p14038_0 := h14038c.1
                                      have p14038_1 := h14038c.2.1
                                      have p14038_2 := h14038c.2.2.1
                                      have p14038_3 := h14038c.2.2.2
                                      linarith only [h13364, h14028, hc02, hc24, hlam, hphi, p14038_1]
                                    · have p14038_0 := h14038c.1
                                      have p14038_1 := h14038c.2.1
                                      have p14038_2 := h14038c.2.2.1
                                      have p14038_3 := h14038c.2.2.2
                                      linarith only [h1, hlam, p14038_0]
                                    · have p14038_0 := h14038c.1
                                      have p14038_1 := h14038c.2.1
                                      have p14038_2 := h14038c.2.2.1
                                      have p14038_3 := h14038c.2.2.2
                                      linarith only [h13364, hlam, p14038_1]
                                    · have p14038_0 := h14038c.1
                                      have p14038_1 := h14038c.2.1
                                      have p14038_2 := h14038c.2.2.1
                                      have p14038_3 := h14038c.2.2.2
                                      rcases p14038_3 (m.d 0 1) (by simp) with h14043 | h14043
                                      · rcases p14038_3 (m.d 0 2) (by simp) with h14044 | h14044
                                        · linarith only [h0, h14044, hlam]
                                        · linarith only [h14022, h14044, hlam]
                                      · linarith only [h14017, h14043, hlam]
                                    · have p14038_0 := h14038c.1
                                      have p14038_1 := h14038c.2.1
                                      have p14038_2 := h14038c.2.2.1
                                      have p14038_3 := h14038c.2.2.2
                                      linarith only [h0, hlam, p14038_0]
                                    · have p14038_0 := h14038c.1
                                      have p14038_1 := h14038c.2.1
                                      have p14038_2 := h14038c.2.2.1
                                      have p14038_3 := h14038c.2.2.2
                                      linarith only [hlam, p14038_0]
                                    · have p14038_0 := h14038c.1
                                      have p14038_1 := h14038c.2.1
                                      have p14038_2 := h14038c.2.2.1
                                      have p14038_3 := h14038c.2.2.2
                                      linarith only [h14018, hlam, p14038_0]
                                    · have p14038_0 := h14038c.1
                                      have p14038_1 := h14038c.2.1
                                      have p14038_2 := h14038c.2.2.1
                                      have p14038_3 := h14038c.2.2.2
                                      linarith only [h14020, hlam, p14038_1]
                                    · have p14038_0 := h14038c.1
                                      have p14038_1 := h14038c.2.1
                                      have p14038_2 := h14038c.2.2.1
                                      have p14038_3 := h14038c.2.2.2
                                      rcases p14038_3 (m.d 0 1) (by simp) with h14052 | h14052
                                      · rcases p14038_3 (m.d 0 2) (by simp) with h14053 | h14053
                                        · rcases p14038_3 (m.d 0 3) (by simp) with h14054 | h14054
                                          · rcases p14038_3 (m.d 0 4) (by simp) with h14055 | h14055
                                            · rcases p14038_3 (m.d 0 5) (by simp) with h14056 | h14056
                                              · linarith only [h14022, h14056, hlam]
                                              · rcases h2bigk with h14058c | h14058c | h14058c | h14058c | h14058c | h14058c | h14058c | h14058c | h14058c | h14058c | h14058c | h14058c | h14058c | h14058c | h14058c | h14058c | h14058c | h14058c | h14058c | h14058c | h14058c | h14058c | h14058c | h14058c | h14058c
                                                · have p14058_0 := h14058c.1
                                                  have p14058_1 := h14058c.2.1
                                                  have p14058_2 := h14058c.2.2.1
                                                  have p14058_3 := h14058c.2.2.2
                                                  linarith only [hlam, p14058_0]
                                                · have p14058_0 := h14058c.1
                                                  have p14058_1 := h14058c.2.1
                                                  have p14058_2 := h14058c.2.2.1
                                                  have p14058_3 := h14058c.2.2.2
                                                  linarith only [h0, h13364, h14026, h14030, h14031, h14035, h14037, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14058_1]
                                                · have p14058_0 := h14058c.1
                                                  have p14058_1 := h14058c.2.1
                                                  have p14058_2 := h14058c.2.2.1
                                                  have p14058_3 := h14058c.2.2.2
                                                  linarith only [h14018, hlam, p14058_0]
                                                · have p14058_0 := h14058c.1
                                                  have p14058_1 := h14058c.2.1
                                                  have p14058_2 := h14058c.2.2.1
                                                  have p14058_3 := h14058c.2.2.2
                                                  linarith only [h14020, hlam, p14058_0]
                                                · have p14058_0 := h14058c.1
                                                  have p14058_1 := h14058c.2.1
                                                  have p14058_2 := h14058c.2.2.1
                                                  have p14058_3 := h14058c.2.2.2
                                                  rcases p14058_3 (m.d 0 2) (by simp) with h14063 | h14063
                                                  · rcases p14058_3 (m.d 1 2) (by simp) with h14064 | h14064
                                                    · linarith only [h0, h14064, hlam]
                                                    · linarith only [h14030, h14064, hlam]
                                                  · linarith only [h14063, hlam, p14058_0]
                                                · have p14058_0 := h14058c.1
                                                  have p14058_1 := h14058c.2.1
                                                  have p14058_2 := h14058c.2.2.1
                                                  have p14058_3 := h14058c.2.2.2
                                                  linarith only [h0, hlam, p14058_0]
                                                · have p14058_0 := h14058c.1
                                                  have p14058_1 := h14058c.2.1
                                                  have p14058_2 := h14058c.2.2.1
                                                  have p14058_3 := h14058c.2.2.2
                                                  linarith only [hlam, p14058_0]
                                                · have p14058_0 := h14058c.1
                                                  have p14058_1 := h14058c.2.1
                                                  have p14058_2 := h14058c.2.2.1
                                                  have p14058_3 := h14058c.2.2.2
                                                  linarith only [h14026, hlam, p14058_0]
                                                · have p14058_0 := h14058c.1
                                                  have p14058_1 := h14058c.2.1
                                                  have p14058_2 := h14058c.2.2.1
                                                  have p14058_3 := h14058c.2.2.2
                                                  linarith only [h14028, hlam, p14058_0]
                                                · have p14058_0 := h14058c.1
                                                  have p14058_1 := h14058c.2.1
                                                  have p14058_2 := h14058c.2.2.1
                                                  have p14058_3 := h14058c.2.2.2
                                                  linarith only [h0, h13364, h14026, h14031, h14035, h14037, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14058_1]
                                                · have p14058_0 := h14058c.1
                                                  have p14058_1 := h14058c.2.1
                                                  have p14058_2 := h14058c.2.2.1
                                                  have p14058_3 := h14058c.2.2.2
                                                  linarith only [hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p14038_1, p14058_1]
                                                · have p14058_0 := h14058c.1
                                                  have p14058_1 := h14058c.2.1
                                                  have p14058_2 := h14058c.2.2.1
                                                  have p14058_3 := h14058c.2.2.2
                                                  rcases p14058_3 (m.d 0 2) (by simp) with h14074 | h14074
                                                  · linarith only [h14018, h14074, hlam]
                                                  · linarith only [h0, h14074, hlam]
                                                · have p14058_0 := h14058c.1
                                                  have p14058_1 := h14058c.2.1
                                                  have p14058_2 := h14058c.2.2.1
                                                  have p14058_3 := h14058c.2.2.2
                                                  linarith only [hlam, p14058_0]
                                                · have p14058_0 := h14058c.1
                                                  have p14058_1 := h14058c.2.1
                                                  have p14058_2 := h14058c.2.2.1
                                                  have p14058_3 := h14058c.2.2.2
                                                  linarith only [h14017, h14020, h14030, h14035, h14037, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14038_1, p14058_1]
                                                · have p14058_0 := h14058c.1
                                                  have p14058_1 := h14058c.2.1
                                                  have p14058_2 := h14058c.2.2.1
                                                  have p14058_3 := h14058c.2.2.2
                                                  linarith only [h0, h13364, h14017, h14026, h14030, h14031, hlam, p14038_1, p14058_2]
                                                · have p14058_0 := h14058c.1
                                                  have p14058_1 := h14058c.2.1
                                                  have p14058_2 := h14058c.2.2.1
                                                  have p14058_3 := h14058c.2.2.2
                                                  linarith only [hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p14038_1, p14058_1]
                                                · have p14058_0 := h14058c.1
                                                  have p14058_1 := h14058c.2.1
                                                  have p14058_2 := h14058c.2.2.1
                                                  have p14058_3 := h14058c.2.2.2
                                                  rcases p14058_3 (m.d 0 2) (by simp) with h14081 | h14081
                                                  · linarith only [h14020, h14081, hlam]
                                                  · linarith only [h0, h14081, hlam]
                                                · have p14058_0 := h14058c.1
                                                  have p14058_1 := h14058c.2.1
                                                  have p14058_2 := h14058c.2.2.1
                                                  have p14058_3 := h14058c.2.2.2
                                                  linarith only [h14034, hlam, p14058_1]
                                                · have p14058_0 := h14058c.1
                                                  have p14058_1 := h14058c.2.1
                                                  have p14058_2 := h14058c.2.2.1
                                                  have p14058_3 := h14058c.2.2.2
                                                  linarith only [hlam, p14058_0]
                                                · have p14058_0 := h14058c.1
                                                  have p14058_1 := h14058c.2.1
                                                  have p14058_2 := h14058c.2.2.1
                                                  have p14058_3 := h14058c.2.2.2
                                                  linarith only [h14017, h14020, h14030, hlam, p14038_1, p14058_2]
                                                · have p14058_0 := h14058c.1
                                                  have p14058_1 := h14058c.2.1
                                                  have p14058_2 := h14058c.2.2.1
                                                  have p14058_3 := h14058c.2.2.2
                                                  linarith only [h14022, hlam, p14058_0]
                                                · have p14058_0 := h14058c.1
                                                  have p14058_1 := h14058c.2.1
                                                  have p14058_2 := h14058c.2.2.1
                                                  have p14058_3 := h14058c.2.2.2
                                                  linarith only [h14030, hlam, p14058_0]
                                                · have p14058_0 := h14058c.1
                                                  have p14058_1 := h14058c.2.1
                                                  have p14058_2 := h14058c.2.2.1
                                                  have p14058_3 := h14058c.2.2.2
                                                  linarith only [h14035, hlam, p14058_1]
                                                · have p14058_0 := h14058c.1
                                                  have p14058_1 := h14058c.2.1
                                                  have p14058_2 := h14058c.2.2.1
                                                  have p14058_3 := h14058c.2.2.2
                                                  linarith only [h14036, hlam, p14058_0]
                                                · have p14058_0 := h14058c.1
                                                  have p14058_1 := h14058c.2.1
                                                  have p14058_2 := h14058c.2.2.1
                                                  have p14058_3 := h14058c.2.2.2
                                                  linarith only [hlam, p14058_0]
                                            · linarith only [h14025, h14055, hlam]
                                          · linarith only [h14024, h14054, hlam]
                                        · linarith only [h14022, h14053, hlam]
                                      · linarith only [h14017, h14052, hlam]
                                    · have p14038_0 := h14038c.1
                                      have p14038_1 := h14038c.2.1
                                      have p14038_2 := h14038c.2.2.1
                                      have p14038_3 := h14038c.2.2.2
                                      linarith only [h0, h1, h14026, hc12, hc23, hlam, hphi, p14038_1]
                                    · have p14038_0 := h14038c.1
                                      have p14038_1 := h14038c.2.1
                                      have p14038_2 := h14038c.2.2.1
                                      have p14038_3 := h14038c.2.2.2
                                      rcases p14038_3 (m.d 0 1) (by simp) with h14097 | h14097
                                      · linarith only [h1, h14097, hlam]
                                      · linarith only [h0, h14097, hlam]
                                    · have p14038_0 := h14038c.1
                                      have p14038_1 := h14038c.2.1
                                      have p14038_2 := h14038c.2.2.1
                                      have p14038_3 := h14038c.2.2.2
                                      linarith only [hlam, p14038_0]
                                    · have p14038_0 := h14038c.1
                                      have p14038_1 := h14038c.2.1
                                      have p14038_2 := h14038c.2.2.1
                                      have p14038_3 := h14038c.2.2.2
                                      linarith only [h0, h1, h13364, h14026, h14030, h14035, h14037, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14038_1]
                                    · have p14038_0 := h14038c.1
                                      have p14038_1 := h14038c.2.1
                                      have p14038_2 := h14038c.2.2.1
                                      have p14038_3 := h14038c.2.2.2
                                      rcases p14038_3 (m.d 0 1) (by simp) with h14102 | h14102
                                      · linarith only [h1, h14102, hlam]
                                      · linarith only [h14017, h14102, hlam]
                                    · have p14038_0 := h14038c.1
                                      have p14038_1 := h14038c.2.1
                                      have p14038_2 := h14038c.2.2.1
                                      have p14038_3 := h14038c.2.2.2
                                      linarith only [h0, h14030, h14035, h14037, hc04, hc45, hlam, hphi, ht0b, ht5b, p14038_1]
                                    · have p14038_0 := h14038c.1
                                      have p14038_1 := h14038c.2.1
                                      have p14038_2 := h14038c.2.2.1
                                      have p14038_3 := h14038c.2.2.2
                                      rcases p14038_3 (m.d 0 1) (by simp) with h14106 | h14106
                                      · linarith only [h13364, h14106, hlam]
                                      · linarith only [h0, h14106, hlam]
                                    · have p14038_0 := h14038c.1
                                      have p14038_1 := h14038c.2.1
                                      have p14038_2 := h14038c.2.2.1
                                      have p14038_3 := h14038c.2.2.2
                                      linarith only [h14023, hlam, p14038_0]
                                    · have p14038_0 := h14038c.1
                                      have p14038_1 := h14038c.2.1
                                      have p14038_2 := h14038c.2.2.1
                                      have p14038_3 := h14038c.2.2.2
                                      linarith only [hlam, p14038_0]
                                    · have p14038_0 := h14038c.1
                                      have p14038_1 := h14038c.2.1
                                      have p14038_2 := h14038c.2.2.1
                                      have p14038_3 := h14038c.2.2.2
                                      rcases p14038_3 (m.d 0 1) (by simp) with h14111 | h14111
                                      · linarith only [h13364, h14111, hlam]
                                      · linarith only [h14017, h14111, hlam]
                                    · have p14038_0 := h14038c.1
                                      have p14038_1 := h14038c.2.1
                                      have p14038_2 := h14038c.2.2.1
                                      have p14038_3 := h14038c.2.2.2
                                      linarith only [h14017, hlam, p14038_0]
                                    · have p14038_0 := h14038c.1
                                      have p14038_1 := h14038c.2.1
                                      have p14038_2 := h14038c.2.2.1
                                      have p14038_3 := h14038c.2.2.2
                                      linarith only [h14022, hlam, p14038_1]
                                    · have p14038_0 := h14038c.1
                                      have p14038_1 := h14038c.2.1
                                      have p14038_2 := h14038c.2.2.1
                                      have p14038_3 := h14038c.2.2.2
                                      linarith only [h14024, hlam, p14038_0]
                                    · have p14038_0 := h14038c.1
                                      have p14038_1 := h14038c.2.1
                                      have p14038_2 := h14038c.2.2.1
                                      have p14038_3 := h14038c.2.2.2
                                      linarith only [h14025, hlam, p14038_1]
                                    · have p14038_0 := h14038c.1
                                      have p14038_1 := h14038c.2.1
                                      have p14038_2 := h14038c.2.2.1
                                      have p14038_3 := h14038c.2.2.2
                                      linarith only [hlam, p14038_0]
                                  · linarith only [h0, h13364, h14026, h14030, h14031, h14036, h14037, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h0, h13364, h14017, h14020, h14026, h14030, h14031, h14033, h14035, h14036, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · linarith only [h0, h13364, h14026, h14030, h14031, h14035, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h0, h13364, h14026, h14030, h14031, h14034, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h0, h13364, h14030, h14033, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                        · linarith only [h0, h13364, h14030, h14031, h14032, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h1, h14023, h14031, hlam]
                    · linarith only [h0, h13364, h14022, h14028, h14030, hc12, hc24, hlam, hphi]
              · linarith only [h0, h13364, h14022, h14025, hlam]
            · linarith only [h0, h1, h14022, h14024, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h14129 | h14129
            · rcases m.htr 0 4 5 (by decide) (by decide) with h14130 | h14130
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14131 | h14131
                · linarith only [h0, h1, h14023, h14131, hc23, hc34, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h14133 | h14133
                  · linarith only [h0, h1, h14020, h14023, h14133, hc02, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h14135 | h14135
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h14136 | h14136
                      · linarith only [h0, h1, h14023, h14131, h14136, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h14135, h14136, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h0, h13364, h14022, h14133, h14135, hc12, hc24, hlam, hphi]
              · linarith only [h0, h1, h14022, h14023, h14130, hlam]
            · linarith only [h0, h1, h14022, h14129, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h14142 | h14142
          · rcases m.htr 0 3 5 (by decide) (by decide) with h14143 | h14143
            · rcases m.htr 0 4 5 (by decide) (by decide) with h14144 | h14144
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14145 | h14145
                · linarith only [h0, h1, h14018, h14145, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h14147 | h14147
                  · linarith only [h0, h14020, h14147, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h14149 | h14149
                    · linarith only [h0, h14022, h14149, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h14151 | h14151
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h14152 | h14152
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h14153 | h14153
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h14154 | h14154
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h14155 | h14155
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h14156 | h14156
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h14157 | h14157
                                  · rcases h0bigk with h14158c | h14158c | h14158c | h14158c | h14158c | h14158c | h14158c | h14158c | h14158c | h14158c | h14158c | h14158c | h14158c | h14158c | h14158c | h14158c | h14158c | h14158c | h14158c | h14158c | h14158c | h14158c | h14158c | h14158c | h14158c
                                    · have p14158_0 := h14158c.1
                                      have p14158_1 := h14158c.2.1
                                      have p14158_2 := h14158c.2.2.1
                                      have p14158_3 := h14158c.2.2.2
                                      linarith only [hlam, p14158_0]
                                    · have p14158_0 := h14158c.1
                                      have p14158_1 := h14158c.2.1
                                      have p14158_2 := h14158c.2.2.1
                                      have p14158_3 := h14158c.2.2.2
                                      linarith only [h13364, h14145, h14151, hc02, hc23, hlam, hphi, p14158_1]
                                    · have p14158_0 := h14158c.1
                                      have p14158_1 := h14158c.2.1
                                      have p14158_2 := h14158c.2.2.1
                                      have p14158_3 := h14158c.2.2.2
                                      linarith only [h1, hlam, p14158_0]
                                    · have p14158_0 := h14158c.1
                                      have p14158_1 := h14158c.2.1
                                      have p14158_2 := h14158c.2.2.1
                                      have p14158_3 := h14158c.2.2.2
                                      linarith only [h13364, hlam, p14158_1]
                                    · have p14158_0 := h14158c.1
                                      have p14158_1 := h14158c.2.1
                                      have p14158_2 := h14158c.2.2.1
                                      have p14158_3 := h14158c.2.2.2
                                      linarith only [h0, h13364, h14022, h14145, h14151, hc12, hc23, hlam, hphi, p14158_1]
                                    · have p14158_0 := h14158c.1
                                      have p14158_1 := h14158c.2.1
                                      have p14158_2 := h14158c.2.2.1
                                      have p14158_3 := h14158c.2.2.2
                                      linarith only [h0, hlam, p14158_0]
                                    · have p14158_0 := h14158c.1
                                      have p14158_1 := h14158c.2.1
                                      have p14158_2 := h14158c.2.2.1
                                      have p14158_3 := h14158c.2.2.2
                                      linarith only [hlam, p14158_0]
                                    · have p14158_0 := h14158c.1
                                      have p14158_1 := h14158c.2.1
                                      have p14158_2 := h14158c.2.2.1
                                      have p14158_3 := h14158c.2.2.2
                                      linarith only [h14018, hlam, p14158_0]
                                    · have p14158_0 := h14158c.1
                                      have p14158_1 := h14158c.2.1
                                      have p14158_2 := h14158c.2.2.1
                                      have p14158_3 := h14158c.2.2.2
                                      linarith only [h14020, hlam, p14158_1]
                                    · have p14158_0 := h14158c.1
                                      have p14158_1 := h14158c.2.1
                                      have p14158_2 := h14158c.2.2.1
                                      have p14158_3 := h14158c.2.2.2
                                      linarith only [h14022, hlam, p14158_0]
                                    · have p14158_0 := h14158c.1
                                      have p14158_1 := h14158c.2.1
                                      have p14158_2 := h14158c.2.2.1
                                      have p14158_3 := h14158c.2.2.2
                                      linarith only [h0, h1, h14145, hc12, hc23, hlam, hphi, p14158_1]
                                    · have p14158_0 := h14158c.1
                                      have p14158_1 := h14158c.2.1
                                      have p14158_2 := h14158c.2.2.1
                                      have p14158_3 := h14158c.2.2.2
                                      rcases p14158_3 (m.d 0 1) (by simp) with h14170 | h14170
                                      · linarith only [h1, h14170, hlam]
                                      · linarith only [h0, h14170, hlam]
                                    · have p14158_0 := h14158c.1
                                      have p14158_1 := h14158c.2.1
                                      have p14158_2 := h14158c.2.2.1
                                      have p14158_3 := h14158c.2.2.2
                                      linarith only [hlam, p14158_0]
                                    · have p14158_0 := h14158c.1
                                      have p14158_1 := h14158c.2.1
                                      have p14158_2 := h14158c.2.2.1
                                      have p14158_3 := h14158c.2.2.2
                                      linarith only [h1, h13364, h14017, h14145, h14149, hc12, hc23, hlam, hphi, p14158_1]
                                    · have p14158_0 := h14158c.1
                                      have p14158_1 := h14158c.2.1
                                      have p14158_2 := h14158c.2.2.1
                                      have p14158_3 := h14158c.2.2.2
                                      rcases p14158_3 (m.d 0 1) (by simp) with h14175 | h14175
                                      · linarith only [h1, h14175, hlam]
                                      · linarith only [h14017, h14175, hlam]
                                    · have p14158_0 := h14158c.1
                                      have p14158_1 := h14158c.2.1
                                      have p14158_2 := h14158c.2.2.1
                                      have p14158_3 := h14158c.2.2.2
                                      linarith only [h13364, h14017, h14147, h14149, hc12, hc24, hlam, hphi, p14158_1]
                                    · have p14158_0 := h14158c.1
                                      have p14158_1 := h14158c.2.1
                                      have p14158_2 := h14158c.2.2.1
                                      have p14158_3 := h14158c.2.2.2
                                      rcases p14158_3 (m.d 0 1) (by simp) with h14179 | h14179
                                      · linarith only [h13364, h14179, hlam]
                                      · linarith only [h0, h14179, hlam]
                                    · have p14158_0 := h14158c.1
                                      have p14158_1 := h14158c.2.1
                                      have p14158_2 := h14158c.2.2.1
                                      have p14158_3 := h14158c.2.2.2
                                      linarith only [h14142, hlam, p14158_0]
                                    · have p14158_0 := h14158c.1
                                      have p14158_1 := h14158c.2.1
                                      have p14158_2 := h14158c.2.2.1
                                      have p14158_3 := h14158c.2.2.2
                                      linarith only [hlam, p14158_0]
                                    · have p14158_0 := h14158c.1
                                      have p14158_1 := h14158c.2.1
                                      have p14158_2 := h14158c.2.2.1
                                      have p14158_3 := h14158c.2.2.2
                                      rcases p14158_3 (m.d 0 1) (by simp) with h14184 | h14184
                                      · linarith only [h13364, h14184, hlam]
                                      · linarith only [h14017, h14184, hlam]
                                    · have p14158_0 := h14158c.1
                                      have p14158_1 := h14158c.2.1
                                      have p14158_2 := h14158c.2.2.1
                                      have p14158_3 := h14158c.2.2.2
                                      linarith only [h14017, hlam, p14158_0]
                                    · have p14158_0 := h14158c.1
                                      have p14158_1 := h14158c.2.1
                                      have p14158_2 := h14158c.2.2.1
                                      have p14158_3 := h14158c.2.2.2
                                      linarith only [h0, h1, h14017, h14145, hc12, hc23, hlam, hphi, p14158_1]
                                    · have p14158_0 := h14158c.1
                                      have p14158_1 := h14158c.2.1
                                      have p14158_2 := h14158c.2.2.1
                                      have p14158_3 := h14158c.2.2.2
                                      linarith only [h14143, hlam, p14158_0]
                                    · have p14158_0 := h14158c.1
                                      have p14158_1 := h14158c.2.1
                                      have p14158_2 := h14158c.2.2.1
                                      have p14158_3 := h14158c.2.2.2
                                      linarith only [h14144, hlam, p14158_1]
                                    · have p14158_0 := h14158c.1
                                      have p14158_1 := h14158c.2.1
                                      have p14158_2 := h14158c.2.2.1
                                      have p14158_3 := h14158c.2.2.2
                                      linarith only [hlam, p14158_0]
                                  · rcases h0bigk with h14192c | h14192c | h14192c | h14192c | h14192c | h14192c | h14192c | h14192c | h14192c | h14192c | h14192c | h14192c | h14192c | h14192c | h14192c | h14192c | h14192c | h14192c | h14192c | h14192c | h14192c | h14192c | h14192c | h14192c | h14192c
                                    · have p14192_0 := h14192c.1
                                      have p14192_1 := h14192c.2.1
                                      have p14192_2 := h14192c.2.2.1
                                      have p14192_3 := h14192c.2.2.2
                                      linarith only [hlam, p14192_0]
                                    · have p14192_0 := h14192c.1
                                      have p14192_1 := h14192c.2.1
                                      have p14192_2 := h14192c.2.2.1
                                      have p14192_3 := h14192c.2.2.2
                                      linarith only [h0, h13364, h14145, h14151, hc12, hc23, hlam, hphi, p14192_1]
                                    · have p14192_0 := h14192c.1
                                      have p14192_1 := h14192c.2.1
                                      have p14192_2 := h14192c.2.2.1
                                      have p14192_3 := h14192c.2.2.2
                                      linarith only [h1, hlam, p14192_0]
                                    · have p14192_0 := h14192c.1
                                      have p14192_1 := h14192c.2.1
                                      have p14192_2 := h14192c.2.2.1
                                      have p14192_3 := h14192c.2.2.2
                                      linarith only [h13364, hlam, p14192_1]
                                    · have p14192_0 := h14192c.1
                                      have p14192_1 := h14192c.2.1
                                      have p14192_2 := h14192c.2.2.1
                                      have p14192_3 := h14192c.2.2.2
                                      linarith only [h13364, h14017, h14145, h14151, h14153, h14157, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14192_1]
                                    · have p14192_0 := h14192c.1
                                      have p14192_1 := h14192c.2.1
                                      have p14192_2 := h14192c.2.2.1
                                      have p14192_3 := h14192c.2.2.2
                                      linarith only [h0, hlam, p14192_0]
                                    · have p14192_0 := h14192c.1
                                      have p14192_1 := h14192c.2.1
                                      have p14192_2 := h14192c.2.2.1
                                      have p14192_3 := h14192c.2.2.2
                                      linarith only [hlam, p14192_0]
                                    · have p14192_0 := h14192c.1
                                      have p14192_1 := h14192c.2.1
                                      have p14192_2 := h14192c.2.2.1
                                      have p14192_3 := h14192c.2.2.2
                                      linarith only [h14018, hlam, p14192_0]
                                    · have p14192_0 := h14192c.1
                                      have p14192_1 := h14192c.2.1
                                      have p14192_2 := h14192c.2.2.1
                                      have p14192_3 := h14192c.2.2.2
                                      linarith only [h14020, hlam, p14192_1]
                                    · have p14192_0 := h14192c.1
                                      have p14192_1 := h14192c.2.1
                                      have p14192_2 := h14192c.2.2.1
                                      have p14192_3 := h14192c.2.2.2
                                      linarith only [h14022, hlam, p14192_0]
                                    · have p14192_0 := h14192c.1
                                      have p14192_1 := h14192c.2.1
                                      have p14192_2 := h14192c.2.2.1
                                      have p14192_3 := h14192c.2.2.2
                                      linarith only [h0, h1, h14145, hc12, hc23, hlam, hphi, p14192_1]
                                    · have p14192_0 := h14192c.1
                                      have p14192_1 := h14192c.2.1
                                      have p14192_2 := h14192c.2.2.1
                                      have p14192_3 := h14192c.2.2.2
                                      rcases p14192_3 (m.d 0 1) (by simp) with h14204 | h14204
                                      · linarith only [h1, h14204, hlam]
                                      · linarith only [h0, h14204, hlam]
                                    · have p14192_0 := h14192c.1
                                      have p14192_1 := h14192c.2.1
                                      have p14192_2 := h14192c.2.2.1
                                      have p14192_3 := h14192c.2.2.2
                                      linarith only [hlam, p14192_0]
                                    · have p14192_0 := h14192c.1
                                      have p14192_1 := h14192c.2.1
                                      have p14192_2 := h14192c.2.2.1
                                      have p14192_3 := h14192c.2.2.2
                                      linarith only [h1, h13364, h14017, h14145, h14153, h14157, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14192_1]
                                    · have p14192_0 := h14192c.1
                                      have p14192_1 := h14192c.2.1
                                      have p14192_2 := h14192c.2.2.1
                                      have p14192_3 := h14192c.2.2.2
                                      rcases p14192_3 (m.d 0 1) (by simp) with h14209 | h14209
                                      · linarith only [h1, h14209, hlam]
                                      · linarith only [h14017, h14209, hlam]
                                    · have p14192_0 := h14192c.1
                                      have p14192_1 := h14192c.2.1
                                      have p14192_2 := h14192c.2.2.1
                                      have p14192_3 := h14192c.2.2.2
                                      linarith only [h14017, h14153, h14157, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p14192_1]
                                    · have p14192_0 := h14192c.1
                                      have p14192_1 := h14192c.2.1
                                      have p14192_2 := h14192c.2.2.1
                                      have p14192_3 := h14192c.2.2.2
                                      rcases p14192_3 (m.d 0 1) (by simp) with h14213 | h14213
                                      · linarith only [h13364, h14213, hlam]
                                      · linarith only [h0, h14213, hlam]
                                    · have p14192_0 := h14192c.1
                                      have p14192_1 := h14192c.2.1
                                      have p14192_2 := h14192c.2.2.1
                                      have p14192_3 := h14192c.2.2.2
                                      linarith only [h14142, hlam, p14192_0]
                                    · have p14192_0 := h14192c.1
                                      have p14192_1 := h14192c.2.1
                                      have p14192_2 := h14192c.2.2.1
                                      have p14192_3 := h14192c.2.2.2
                                      linarith only [hlam, p14192_0]
                                    · have p14192_0 := h14192c.1
                                      have p14192_1 := h14192c.2.1
                                      have p14192_2 := h14192c.2.2.1
                                      have p14192_3 := h14192c.2.2.2
                                      rcases p14192_3 (m.d 0 1) (by simp) with h14218 | h14218
                                      · linarith only [h13364, h14218, hlam]
                                      · linarith only [h14017, h14218, hlam]
                                    · have p14192_0 := h14192c.1
                                      have p14192_1 := h14192c.2.1
                                      have p14192_2 := h14192c.2.2.1
                                      have p14192_3 := h14192c.2.2.2
                                      linarith only [h14017, hlam, p14192_0]
                                    · have p14192_0 := h14192c.1
                                      have p14192_1 := h14192c.2.1
                                      have p14192_2 := h14192c.2.2.1
                                      have p14192_3 := h14192c.2.2.2
                                      linarith only [h0, h1, h14017, h14145, hc12, hc23, hlam, hphi, p14192_1]
                                    · have p14192_0 := h14192c.1
                                      have p14192_1 := h14192c.2.1
                                      have p14192_2 := h14192c.2.2.1
                                      have p14192_3 := h14192c.2.2.2
                                      linarith only [h14143, hlam, p14192_0]
                                    · have p14192_0 := h14192c.1
                                      have p14192_1 := h14192c.2.1
                                      have p14192_2 := h14192c.2.2.1
                                      have p14192_3 := h14192c.2.2.2
                                      linarith only [h14144, hlam, p14192_1]
                                    · have p14192_0 := h14192c.1
                                      have p14192_1 := h14192c.2.1
                                      have p14192_2 := h14192c.2.2.1
                                      have p14192_3 := h14192c.2.2.2
                                      linarith only [hlam, p14192_0]
                                · linarith only [h0, h13364, h14017, h14020, h14145, h14151, h14153, h14156, hc12, hc23, hlam, hphi]
                              · linarith only [h13364, h14017, h14145, h14151, h14152, h14155, hlam]
                            · linarith only [h0, h13364, h14145, h14151, h14154, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h13364, h14017, h14149, h14153, hc12, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h13364, h14017, h14149, h14151, h14152, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1, h14142, h14151, hlam]
              · linarith only [h13364, h14017, h14144, hlam]
            · linarith only [h1, h14017, h14143, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h14234 | h14234
            · rcases m.htr 0 4 5 (by decide) (by decide) with h14235 | h14235
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14236 | h14236
                · linarith only [h0, h1, h14142, h14236, hc23, hc34, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h14238 | h14238
                  · linarith only [h0, h14020, h14238, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h14240 | h14240
                    · linarith only [h0, h14022, h14240, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h14242 | h14242
                      · linarith only [h1, h14017, h14142, h14236, h14240, h14242, hc12, hc23, hlam, hphi]
                      · linarith only [h1, h14017, h14240, h14242, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h14017, h14142, h14235, hlam]
            · linarith only [h1, h14017, h14234, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h14247 | h14247
    · linarith only [h0, h1, h14247, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h14249 | h14249
      · linarith only [h0, h13364, h14249, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h14251 | h14251
        · linarith only [h0, h14017, h14251, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h14253 | h14253
          · rcases m.htr 0 3 5 (by decide) (by decide) with h14254 | h14254
            · rcases m.htr 0 4 5 (by decide) (by decide) with h14255 | h14255
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14256 | h14256
                · linarith only [h0, h1, h14247, h14256, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h14258 | h14258
                  · linarith only [h0, h14017, h14249, h14255, h14258, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h14260 | h14260
                    · linarith only [h0, h14017, h14251, h14260, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h14262 | h14262
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h14263 | h14263
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h14264 | h14264
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h14265 | h14265
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h14266 | h14266
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h14267 | h14267
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h14268 | h14268
                                  · rcases h0bigk with h14269c | h14269c | h14269c | h14269c | h14269c | h14269c | h14269c | h14269c | h14269c | h14269c | h14269c | h14269c | h14269c | h14269c | h14269c | h14269c | h14269c | h14269c | h14269c | h14269c | h14269c | h14269c | h14269c | h14269c | h14269c
                                    · have p14269_0 := h14269c.1
                                      have p14269_1 := h14269c.2.1
                                      have p14269_2 := h14269c.2.2.1
                                      have p14269_3 := h14269c.2.2.2
                                      linarith only [hlam, p14269_0]
                                    · have p14269_0 := h14269c.1
                                      have p14269_1 := h14269c.2.1
                                      have p14269_2 := h14269c.2.2.1
                                      have p14269_3 := h14269c.2.2.2
                                      linarith only [h14017, h14256, h14262, h14264, hc02, hc23, hlam, hphi, p14269_1]
                                    · have p14269_0 := h14269c.1
                                      have p14269_1 := h14269c.2.1
                                      have p14269_2 := h14269c.2.2.1
                                      have p14269_3 := h14269c.2.2.2
                                      linarith only [h1, hlam, p14269_0]
                                    · have p14269_0 := h14269c.1
                                      have p14269_1 := h14269c.2.1
                                      have p14269_2 := h14269c.2.2.1
                                      have p14269_3 := h14269c.2.2.2
                                      linarith only [h13364, hlam, p14269_1]
                                    · have p14269_0 := h14269c.1
                                      have p14269_1 := h14269c.2.1
                                      have p14269_2 := h14269c.2.2.1
                                      have p14269_3 := h14269c.2.2.2
                                      linarith only [h14017, hlam, p14269_1]
                                    · have p14269_0 := h14269c.1
                                      have p14269_1 := h14269c.2.1
                                      have p14269_2 := h14269c.2.2.1
                                      have p14269_3 := h14269c.2.2.2
                                      linarith only [h0, hlam, p14269_0]
                                    · have p14269_0 := h14269c.1
                                      have p14269_1 := h14269c.2.1
                                      have p14269_2 := h14269c.2.2.1
                                      have p14269_3 := h14269c.2.2.2
                                      linarith only [hlam, p14269_0]
                                    · have p14269_0 := h14269c.1
                                      have p14269_1 := h14269c.2.1
                                      have p14269_2 := h14269c.2.2.1
                                      have p14269_3 := h14269c.2.2.2
                                      linarith only [h14247, hlam, p14269_0]
                                    · have p14269_0 := h14269c.1
                                      have p14269_1 := h14269c.2.1
                                      have p14269_2 := h14269c.2.2.1
                                      have p14269_3 := h14269c.2.2.2
                                      linarith only [h14249, hlam, p14269_1]
                                    · have p14269_0 := h14269c.1
                                      have p14269_1 := h14269c.2.1
                                      have p14269_2 := h14269c.2.2.1
                                      have p14269_3 := h14269c.2.2.2
                                      linarith only [h14251, hlam, p14269_0]
                                    · have p14269_0 := h14269c.1
                                      have p14269_1 := h14269c.2.1
                                      have p14269_2 := h14269c.2.2.1
                                      have p14269_3 := h14269c.2.2.2
                                      linarith only [h0, h1, h14256, hc12, hc23, hlam, hphi, p14269_1]
                                    · have p14269_0 := h14269c.1
                                      have p14269_1 := h14269c.2.1
                                      have p14269_2 := h14269c.2.2.1
                                      have p14269_3 := h14269c.2.2.2
                                      rcases p14269_3 (m.d 0 1) (by simp) with h14281 | h14281
                                      · linarith only [h1, h14281, hlam]
                                      · linarith only [h0, h14281, hlam]
                                    · have p14269_0 := h14269c.1
                                      have p14269_1 := h14269c.2.1
                                      have p14269_2 := h14269c.2.2.1
                                      have p14269_3 := h14269c.2.2.2
                                      linarith only [hlam, p14269_0]
                                    · have p14269_0 := h14269c.1
                                      have p14269_1 := h14269c.2.1
                                      have p14269_2 := h14269c.2.2.1
                                      have p14269_3 := h14269c.2.2.2
                                      linarith only [h0, h1, h13364, h14256, hc12, hc23, hlam, hphi, p14269_1]
                                    · have p14269_0 := h14269c.1
                                      have p14269_1 := h14269c.2.1
                                      have p14269_2 := h14269c.2.2.1
                                      have p14269_3 := h14269c.2.2.2
                                      linarith only [h0, h1, h14017, h14256, hc12, hc23, hlam, hphi, p14269_1]
                                    · have p14269_0 := h14269c.1
                                      have p14269_1 := h14269c.2.1
                                      have p14269_2 := h14269c.2.2.1
                                      have p14269_3 := h14269c.2.2.2
                                      linarith only [h0, h13364, h14258, hc12, hc24, hlam, hphi, p14269_1]
                                    · have p14269_0 := h14269c.1
                                      have p14269_1 := h14269c.2.1
                                      have p14269_2 := h14269c.2.2.1
                                      have p14269_3 := h14269c.2.2.2
                                      rcases p14269_3 (m.d 0 1) (by simp) with h14288 | h14288
                                      · linarith only [h13364, h14288, hlam]
                                      · linarith only [h0, h14288, hlam]
                                    · have p14269_0 := h14269c.1
                                      have p14269_1 := h14269c.2.1
                                      have p14269_2 := h14269c.2.2.1
                                      have p14269_3 := h14269c.2.2.2
                                      linarith only [h14253, hlam, p14269_0]
                                    · have p14269_0 := h14269c.1
                                      have p14269_1 := h14269c.2.1
                                      have p14269_2 := h14269c.2.2.1
                                      have p14269_3 := h14269c.2.2.2
                                      linarith only [hlam, p14269_0]
                                    · have p14269_0 := h14269c.1
                                      have p14269_1 := h14269c.2.1
                                      have p14269_2 := h14269c.2.2.1
                                      have p14269_3 := h14269c.2.2.2
                                      linarith only [h0, h1, h14017, h14253, h14256, hc12, hc23, hlam, hphi, p14269_1]
                                    · have p14269_0 := h14269c.1
                                      have p14269_1 := h14269c.2.1
                                      have p14269_2 := h14269c.2.2.1
                                      have p14269_3 := h14269c.2.2.2
                                      linarith only [h0, h14017, h14260, hc12, hc25, hlam, hphi, p14269_1]
                                    · have p14269_0 := h14269c.1
                                      have p14269_1 := h14269c.2.1
                                      have p14269_2 := h14269c.2.2.1
                                      have p14269_3 := h14269c.2.2.2
                                      rcases p14269_3 (m.d 0 1) (by simp) with h14295 | h14295
                                      · linarith only [h14017, h14295, hlam]
                                      · linarith only [h0, h14295, hlam]
                                    · have p14269_0 := h14269c.1
                                      have p14269_1 := h14269c.2.1
                                      have p14269_2 := h14269c.2.2.1
                                      have p14269_3 := h14269c.2.2.2
                                      linarith only [h14254, hlam, p14269_0]
                                    · have p14269_0 := h14269c.1
                                      have p14269_1 := h14269c.2.1
                                      have p14269_2 := h14269c.2.2.1
                                      have p14269_3 := h14269c.2.2.2
                                      linarith only [h14255, hlam, p14269_1]
                                    · have p14269_0 := h14269c.1
                                      have p14269_1 := h14269c.2.1
                                      have p14269_2 := h14269c.2.2.1
                                      have p14269_3 := h14269c.2.2.2
                                      linarith only [hlam, p14269_0]
                                  · rcases h0bigk with h14301c | h14301c | h14301c | h14301c | h14301c | h14301c | h14301c | h14301c | h14301c | h14301c | h14301c | h14301c | h14301c | h14301c | h14301c | h14301c | h14301c | h14301c | h14301c | h14301c | h14301c | h14301c | h14301c | h14301c | h14301c
                                    · have p14301_0 := h14301c.1
                                      have p14301_1 := h14301c.2.1
                                      have p14301_2 := h14301c.2.2.1
                                      have p14301_3 := h14301c.2.2.2
                                      linarith only [hlam, p14301_0]
                                    · have p14301_0 := h14301c.1
                                      have p14301_1 := h14301c.2.1
                                      have p14301_2 := h14301c.2.2.1
                                      have p14301_3 := h14301c.2.2.2
                                      linarith only [h0, h1, h14256, hc12, hc23, hlam, hphi, p14301_1]
                                    · have p14301_0 := h14301c.1
                                      have p14301_1 := h14301c.2.1
                                      have p14301_2 := h14301c.2.2.1
                                      have p14301_3 := h14301c.2.2.2
                                      linarith only [h1, hlam, p14301_0]
                                    · have p14301_0 := h14301c.1
                                      have p14301_1 := h14301c.2.1
                                      have p14301_2 := h14301c.2.2.1
                                      have p14301_3 := h14301c.2.2.2
                                      linarith only [h13364, hlam, p14301_1]
                                    · have p14301_0 := h14301c.1
                                      have p14301_1 := h14301c.2.1
                                      have p14301_2 := h14301c.2.2.1
                                      have p14301_3 := h14301c.2.2.2
                                      linarith only [h14017, hlam, p14301_1]
                                    · have p14301_0 := h14301c.1
                                      have p14301_1 := h14301c.2.1
                                      have p14301_2 := h14301c.2.2.1
                                      have p14301_3 := h14301c.2.2.2
                                      linarith only [h0, hlam, p14301_0]
                                    · have p14301_0 := h14301c.1
                                      have p14301_1 := h14301c.2.1
                                      have p14301_2 := h14301c.2.2.1
                                      have p14301_3 := h14301c.2.2.2
                                      linarith only [hlam, p14301_0]
                                    · have p14301_0 := h14301c.1
                                      have p14301_1 := h14301c.2.1
                                      have p14301_2 := h14301c.2.2.1
                                      have p14301_3 := h14301c.2.2.2
                                      linarith only [h14247, hlam, p14301_0]
                                    · have p14301_0 := h14301c.1
                                      have p14301_1 := h14301c.2.1
                                      have p14301_2 := h14301c.2.2.1
                                      have p14301_3 := h14301c.2.2.2
                                      linarith only [h14249, hlam, p14301_1]
                                    · have p14301_0 := h14301c.1
                                      have p14301_1 := h14301c.2.1
                                      have p14301_2 := h14301c.2.2.1
                                      have p14301_3 := h14301c.2.2.2
                                      linarith only [h14251, hlam, p14301_0]
                                    · have p14301_0 := h14301c.1
                                      have p14301_1 := h14301c.2.1
                                      have p14301_2 := h14301c.2.2.1
                                      have p14301_3 := h14301c.2.2.2
                                      linarith only [h0, h1, h14256, hc12, hc23, hlam, hphi, p14301_1]
                                    · have p14301_0 := h14301c.1
                                      have p14301_1 := h14301c.2.1
                                      have p14301_2 := h14301c.2.2.1
                                      have p14301_3 := h14301c.2.2.2
                                      rcases p14301_3 (m.d 0 1) (by simp) with h14313 | h14313
                                      · linarith only [h1, h14313, hlam]
                                      · linarith only [h0, h14313, hlam]
                                    · have p14301_0 := h14301c.1
                                      have p14301_1 := h14301c.2.1
                                      have p14301_2 := h14301c.2.2.1
                                      have p14301_3 := h14301c.2.2.2
                                      linarith only [hlam, p14301_0]
                                    · have p14301_0 := h14301c.1
                                      have p14301_1 := h14301c.2.1
                                      have p14301_2 := h14301c.2.2.1
                                      have p14301_3 := h14301c.2.2.2
                                      linarith only [h1, h14255, h14256, h14268, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14301_1]
                                    · have p14301_0 := h14301c.1
                                      have p14301_1 := h14301c.2.1
                                      have p14301_2 := h14301c.2.2.1
                                      have p14301_3 := h14301c.2.2.2
                                      linarith only [h0, h1, h14017, h14256, hc12, hc23, hlam, hphi, p14301_1]
                                    · have p14301_0 := h14301c.1
                                      have p14301_1 := h14301c.2.1
                                      have p14301_2 := h14301c.2.2.1
                                      have p14301_3 := h14301c.2.2.2
                                      linarith only [h0, h13364, h14256, h14262, hc12, hc23, hlam, hphi, p14301_1]
                                    · have p14301_0 := h14301c.1
                                      have p14301_1 := h14301c.2.1
                                      have p14301_2 := h14301c.2.2.1
                                      have p14301_3 := h14301c.2.2.2
                                      rcases p14301_3 (m.d 0 1) (by simp) with h14320 | h14320
                                      · linarith only [h13364, h14320, hlam]
                                      · linarith only [h0, h14320, hlam]
                                    · have p14301_0 := h14301c.1
                                      have p14301_1 := h14301c.2.1
                                      have p14301_2 := h14301c.2.2.1
                                      have p14301_3 := h14301c.2.2.2
                                      linarith only [h14253, hlam, p14301_0]
                                    · have p14301_0 := h14301c.1
                                      have p14301_1 := h14301c.2.1
                                      have p14301_2 := h14301c.2.2.1
                                      have p14301_3 := h14301c.2.2.2
                                      linarith only [hlam, p14301_0]
                                    · have p14301_0 := h14301c.1
                                      have p14301_1 := h14301c.2.1
                                      have p14301_2 := h14301c.2.2.1
                                      have p14301_3 := h14301c.2.2.2
                                      linarith only [h0, h13364, h14017, h14256, h14262, hc12, hc23, hlam, hphi, p14301_1]
                                    · have p14301_0 := h14301c.1
                                      have p14301_1 := h14301c.2.1
                                      have p14301_2 := h14301c.2.2.1
                                      have p14301_3 := h14301c.2.2.2
                                      linarith only [h0, h14017, h14256, h14262, h14264, hc12, hc23, hlam, hphi, p14301_1]
                                    · have p14301_0 := h14301c.1
                                      have p14301_1 := h14301c.2.1
                                      have p14301_2 := h14301c.2.2.1
                                      have p14301_3 := h14301c.2.2.2
                                      rcases p14301_3 (m.d 0 1) (by simp) with h14327 | h14327
                                      · linarith only [h14017, h14327, hlam]
                                      · linarith only [h0, h14327, hlam]
                                    · have p14301_0 := h14301c.1
                                      have p14301_1 := h14301c.2.1
                                      have p14301_2 := h14301c.2.2.1
                                      have p14301_3 := h14301c.2.2.2
                                      linarith only [h14254, hlam, p14301_0]
                                    · have p14301_0 := h14301c.1
                                      have p14301_1 := h14301c.2.1
                                      have p14301_2 := h14301c.2.2.1
                                      have p14301_3 := h14301c.2.2.2
                                      linarith only [h14255, hlam, p14301_1]
                                    · have p14301_0 := h14301c.1
                                      have p14301_1 := h14301c.2.1
                                      have p14301_2 := h14301c.2.2.1
                                      have p14301_3 := h14301c.2.2.2
                                      linarith only [hlam, p14301_0]
                                · linarith only [h14249, h14255, h14267, hlam]
                              · linarith only [h0, h1, h14256, h14266, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h14017, h14256, h14262, h14264, h14265, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h0, h13364, h14255, h14264, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · linarith only [h0, h1, h14263, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h0, h1, h14253, h14262, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14339 | h14339
                · linarith only [h0, h13364, h14247, h14254, h14339, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h14341 | h14341
                  · linarith only [h0, h14249, h14341, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h14343 | h14343
                    · linarith only [h0, h14251, h14343, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h14345 | h14345
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h14346 | h14346
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h14347 | h14347
                          · linarith only [h0, h13364, h14255, h14339, h14345, h14347, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h13364, h14347, hc12, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h0, h1, h14346, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h0, h1, h14253, h14345, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h14352 | h14352
              · linarith only [h14253, h14254, h14352, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14354 | h14354
                · linarith only [h0, h1, h14254, h14354, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h14356 | h14356
                  · linarith only [h0, h13364, h14352, h14356, hc24, hc45, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h14358 | h14358
                    · linarith only [h0, h14251, h14358, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h14360 | h14360
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h14361 | h14361
                        · linarith only [h0, h13364, h14253, h14254, h14354, h14361, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h14361, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h0, h1, h14253, h14360, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h14365 | h14365
            · rcases m.htr 0 4 5 (by decide) (by decide) with h14366 | h14366
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14367 | h14367
                · linarith only [h0, h14247, h14367, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h14369 | h14369
                  · linarith only [h0, h14249, h14369, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h14371 | h14371
                    · linarith only [h0, h14251, h14371, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h14373 | h14373
                      · linarith only [h0, h14017, h14253, h14365, h14367, h14373, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h14373, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h14253, h14365, h14366, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h14377 | h14377
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14378 | h14378
                · linarith only [h0, h1, h14365, h14378, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h14380 | h14380
                  · linarith only [h0, h14249, h14380, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h14382 | h14382
                    · linarith only [h0, h14251, h14382, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h14384 | h14384
                      · linarith only [h0, h1, h14253, h14378, h14384, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h14384, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14387 | h14387
                · linarith only [h0, h1, h14253, h14377, h14387, hc23, hc45, hlam, hphi, ht34]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h14389 | h14389
                  · linarith only [h0, h1, h14249, h14253, h14389, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h14391 | h14391
                    · linarith only [h0, h1, h14251, h14253, h14377, h14391, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h14393 | h14393
                      · linarith only [h0, h1, h14253, h14387, h14393, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h14393, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 28790000 in
set_option maxHeartbeats 28790000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h13364 | h13364
  · exact r1l7_10_12_23_L_I_L_I_H_I_s0_x1_x0 m hb0 hb2 hb3 hg0 h1 h13364
  · exact r1l7_10_12_23_L_I_L_I_H_I_s0_x1_x1 m hb0 hb2 hb3 hg0 h1 h13364

set_option maxHeartbeats 28790000 in
set_option maxHeartbeats 28790000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_10_12_23_L_I_L_I_H_I_s0_x0 m hb0 hb2 hb3 hg0 h1
  · exact r1l7_10_12_23_L_I_L_I_H_I_s0_x1 m hb0 hb2 hb3 hg0 h1

end R2N4
