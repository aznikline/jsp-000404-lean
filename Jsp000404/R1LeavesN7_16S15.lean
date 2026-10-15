import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_16S14

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6660000 in
set_option maxHeartbeats 6660000 in
theorem r1l7_21_15_H_I_L_I_s9 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6137 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7252 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0 := hg0
  have h6137 := hg6137
  have h7252 := hg7252
  rcases m.htr 0 1 5 (by decide) (by decide) with h8021 | h8021
  · rcases m.htr 0 2 3 (by decide) (by decide) with h8022 | h8022
    · rcases m.htr 0 2 4 (by decide) (by decide) with h8023 | h8023
      · rcases m.htr 0 2 5 (by decide) (by decide) with h8024 | h8024
        · rcases m.htr 0 3 4 (by decide) (by decide) with h8025 | h8025
          · rcases m.htr 0 3 5 (by decide) (by decide) with h8026 | h8026
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8027 | h8027
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8028 | h8028
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8029 | h8029
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8030 | h8030
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8031 | h8031
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8032 | h8032
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8033 | h8033
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8034 | h8034
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8035 | h8035
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8036 | h8036
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8037 | h8037
                                  · rcases h1bigk with h8038c | h8038c | h8038c | h8038c | h8038c | h8038c | h8038c | h8038c | h8038c | h8038c | h8038c | h8038c | h8038c | h8038c | h8038c | h8038c | h8038c | h8038c | h8038c | h8038c | h8038c | h8038c | h8038c | h8038c | h8038c
                                    · have p8038_0 := h8038c.1
                                      have p8038_1 := h8038c.2.1
                                      have p8038_2 := h8038c.2.2.1
                                      have p8038_3 := h8038c.2.2.2
                                      linarith only [hlam, p8038_0]
                                    · have p8038_0 := h8038c.1
                                      have p8038_1 := h8038c.2.1
                                      have p8038_2 := h8038c.2.2.1
                                      have p8038_3 := h8038c.2.2.2
                                      linarith only [h0, hlam, p8038_0]
                                    · have p8038_0 := h8038c.1
                                      have p8038_1 := h8038c.2.1
                                      have p8038_2 := h8038c.2.2.1
                                      have p8038_3 := h8038c.2.2.2
                                      linarith only [h6137, hlam, p8038_0]
                                    · have p8038_0 := h8038c.1
                                      have p8038_1 := h8038c.2.1
                                      have p8038_2 := h8038c.2.2.1
                                      have p8038_3 := h8038c.2.2.2
                                      linarith only [h7252, hlam, p8038_0]
                                    · have p8038_0 := h8038c.1
                                      have p8038_1 := h8038c.2.1
                                      have p8038_2 := h8038c.2.2.1
                                      have p8038_3 := h8038c.2.2.2
                                      linarith only [h7252, h8030, h8035, h8037, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p8038_1]
                                    · have p8038_0 := h8038c.1
                                      have p8038_1 := h8038c.2.1
                                      have p8038_2 := h8038c.2.2.1
                                      have p8038_3 := h8038c.2.2.2
                                      linarith only [hc01, hc12, hlam, hphi, p8038_1]
                                    · have p8038_0 := h8038c.1
                                      have p8038_1 := h8038c.2.1
                                      have p8038_2 := h8038c.2.2.1
                                      have p8038_3 := h8038c.2.2.2
                                      linarith only [hlam, p8038_0]
                                    · have p8038_0 := h8038c.1
                                      have p8038_1 := h8038c.2.1
                                      have p8038_2 := h8038c.2.2.1
                                      have p8038_3 := h8038c.2.2.2
                                      linarith only [h6137, h8021, h8030, h8035, h8037, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8038_1]
                                    · have p8038_0 := h8038c.1
                                      have p8038_1 := h8038c.2.1
                                      have p8038_2 := h8038c.2.2.1
                                      have p8038_3 := h8038c.2.2.2
                                      linarith only [h7252, h8021, h8030, h8035, h8037, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8038_1]
                                    · have p8038_0 := h8038c.1
                                      have p8038_1 := h8038c.2.1
                                      have p8038_2 := h8038c.2.2.1
                                      have p8038_3 := h8038c.2.2.2
                                      rcases p8038_3 (m.d 0 1) (by simp) with h8048 | h8048
                                      · linarith only [h0, h8048, hlam]
                                      · linarith only [h8021, h8048, hlam]
                                    · have p8038_0 := h8038c.1
                                      have p8038_1 := h8038c.2.1
                                      have p8038_2 := h8038c.2.2.1
                                      have p8038_3 := h8038c.2.2.2
                                      linarith only [h8021, h8030, h8035, h8037, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p8038_1]
                                    · have p8038_0 := h8038c.1
                                      have p8038_1 := h8038c.2.1
                                      have p8038_2 := h8038c.2.2.1
                                      have p8038_3 := h8038c.2.2.2
                                      linarith only [h8028, hlam, p8038_1]
                                    · have p8038_0 := h8038c.1
                                      have p8038_1 := h8038c.2.1
                                      have p8038_2 := h8038c.2.2.1
                                      have p8038_3 := h8038c.2.2.2
                                      linarith only [hlam, p8038_0]
                                    · have p8038_0 := h8038c.1
                                      have p8038_1 := h8038c.2.1
                                      have p8038_2 := h8038c.2.2.1
                                      have p8038_3 := h8038c.2.2.2
                                      linarith only [h7252, h8021, h8028, h8030, h8035, h8037, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8038_1]
                                    · have p8038_0 := h8038c.1
                                      have p8038_1 := h8038c.2.1
                                      have p8038_2 := h8038c.2.2.1
                                      have p8038_3 := h8038c.2.2.2
                                      rcases p8038_3 (m.d 0 1) (by simp) with h8055 | h8055
                                      · linarith only [h6137, h8055, hlam]
                                      · linarith only [h8021, h8055, hlam]
                                    · have p8038_0 := h8038c.1
                                      have p8038_1 := h8038c.2.1
                                      have p8038_2 := h8038c.2.2.1
                                      have p8038_3 := h8038c.2.2.2
                                      linarith only [h8021, h8030, h8035, h8037, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p8038_1]
                                    · have p8038_0 := h8038c.1
                                      have p8038_1 := h8038c.2.1
                                      have p8038_2 := h8038c.2.2.1
                                      have p8038_3 := h8038c.2.2.2
                                      linarith only [h8029, hlam, p8038_1]
                                    · have p8038_0 := h8038c.1
                                      have p8038_1 := h8038c.2.1
                                      have p8038_2 := h8038c.2.2.1
                                      have p8038_3 := h8038c.2.2.2
                                      linarith only [h8031, hlam, p8038_0]
                                    · have p8038_0 := h8038c.1
                                      have p8038_1 := h8038c.2.1
                                      have p8038_2 := h8038c.2.2.1
                                      have p8038_3 := h8038c.2.2.2
                                      linarith only [hlam, p8038_0]
                                    · have p8038_0 := h8038c.1
                                      have p8038_1 := h8038c.2.1
                                      have p8038_2 := h8038c.2.2.1
                                      have p8038_3 := h8038c.2.2.2
                                      rcases p8038_3 (m.d 0 1) (by simp) with h8062 | h8062
                                      · linarith only [h7252, h8062, hlam]
                                      · linarith only [h8021, h8062, hlam]
                                    · have p8038_0 := h8038c.1
                                      have p8038_1 := h8038c.2.1
                                      have p8038_2 := h8038c.2.2.1
                                      have p8038_3 := h8038c.2.2.2
                                      linarith only [h8021, hlam, p8038_0]
                                    · have p8038_0 := h8038c.1
                                      have p8038_1 := h8038c.2.1
                                      have p8038_2 := h8038c.2.2.1
                                      have p8038_3 := h8038c.2.2.2
                                      linarith only [h8030, hlam, p8038_1]
                                    · have p8038_0 := h8038c.1
                                      have p8038_1 := h8038c.2.1
                                      have p8038_2 := h8038c.2.2.1
                                      have p8038_3 := h8038c.2.2.2
                                      linarith only [h8032, hlam, p8038_0]
                                    · have p8038_0 := h8038c.1
                                      have p8038_1 := h8038c.2.1
                                      have p8038_2 := h8038c.2.2.1
                                      have p8038_3 := h8038c.2.2.2
                                      linarith only [h8033, hlam, p8038_0]
                                    · have p8038_0 := h8038c.1
                                      have p8038_1 := h8038c.2.1
                                      have p8038_2 := h8038c.2.2.1
                                      have p8038_3 := h8038c.2.2.2
                                      linarith only [hlam, p8038_0]
                                  · rcases h1bigk with h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c | h8070c
                                    · have p8070_0 := h8070c.1
                                      have p8070_1 := h8070c.2.1
                                      have p8070_2 := h8070c.2.2.1
                                      have p8070_3 := h8070c.2.2.2
                                      linarith only [hlam, p8070_0]
                                    · have p8070_0 := h8070c.1
                                      have p8070_1 := h8070c.2.1
                                      have p8070_2 := h8070c.2.2.1
                                      have p8070_3 := h8070c.2.2.2
                                      linarith only [h0, hlam, p8070_0]
                                    · have p8070_0 := h8070c.1
                                      have p8070_1 := h8070c.2.1
                                      have p8070_2 := h8070c.2.2.1
                                      have p8070_3 := h8070c.2.2.2
                                      linarith only [h6137, hlam, p8070_0]
                                    · have p8070_0 := h8070c.1
                                      have p8070_1 := h8070c.2.1
                                      have p8070_2 := h8070c.2.2.1
                                      have p8070_3 := h8070c.2.2.2
                                      linarith only [h7252, hlam, p8070_0]
                                    · have p8070_0 := h8070c.1
                                      have p8070_1 := h8070c.2.1
                                      have p8070_2 := h8070c.2.2.1
                                      have p8070_3 := h8070c.2.2.2
                                      linarith only [h8030, h8036, h8037, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8070_1]
                                    · have p8070_0 := h8070c.1
                                      have p8070_1 := h8070c.2.1
                                      have p8070_2 := h8070c.2.2.1
                                      have p8070_3 := h8070c.2.2.2
                                      linarith only [hc01, hc12, hlam, hphi, p8070_1]
                                    · have p8070_0 := h8070c.1
                                      have p8070_1 := h8070c.2.1
                                      have p8070_2 := h8070c.2.2.1
                                      have p8070_3 := h8070c.2.2.2
                                      linarith only [hlam, p8070_0]
                                    · have p8070_0 := h8070c.1
                                      have p8070_1 := h8070c.2.1
                                      have p8070_2 := h8070c.2.2.1
                                      have p8070_3 := h8070c.2.2.2
                                      linarith only [h6137, hc01, hc12, hlam, hphi, p8070_1]
                                    · have p8070_0 := h8070c.1
                                      have p8070_1 := h8070c.2.1
                                      have p8070_2 := h8070c.2.2.1
                                      have p8070_3 := h8070c.2.2.2
                                      linarith only [h7252, h8021, h8030, h8036, h8037, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8070_1]
                                    · have p8070_0 := h8070c.1
                                      have p8070_1 := h8070c.2.1
                                      have p8070_2 := h8070c.2.2.1
                                      have p8070_3 := h8070c.2.2.2
                                      linarith only [h8030, h8036, h8037, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8070_1]
                                    · have p8070_0 := h8070c.1
                                      have p8070_1 := h8070c.2.1
                                      have p8070_2 := h8070c.2.2.1
                                      have p8070_3 := h8070c.2.2.2
                                      linarith only [h8021, h8028, h8030, h8036, h8037, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8070_1]
                                    · have p8070_0 := h8070c.1
                                      have p8070_1 := h8070c.2.1
                                      have p8070_2 := h8070c.2.2.1
                                      have p8070_3 := h8070c.2.2.2
                                      linarith only [h8028, hlam, p8070_1]
                                    · have p8070_0 := h8070c.1
                                      have p8070_1 := h8070c.2.1
                                      have p8070_2 := h8070c.2.2.1
                                      have p8070_3 := h8070c.2.2.2
                                      linarith only [hlam, p8070_0]
                                    · have p8070_0 := h8070c.1
                                      have p8070_1 := h8070c.2.1
                                      have p8070_2 := h8070c.2.2.1
                                      have p8070_3 := h8070c.2.2.2
                                      linarith only [h7252, h8021, h8028, h8030, h8036, h8037, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8070_1]
                                    · have p8070_0 := h8070c.1
                                      have p8070_1 := h8070c.2.1
                                      have p8070_2 := h8070c.2.2.1
                                      have p8070_3 := h8070c.2.2.2
                                      linarith only [h8028, h8030, h8036, h8037, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8070_1]
                                    · have p8070_0 := h8070c.1
                                      have p8070_1 := h8070c.2.1
                                      have p8070_2 := h8070c.2.2.1
                                      have p8070_3 := h8070c.2.2.2
                                      linarith only [h8021, h8030, h8036, h8037, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8070_1]
                                    · have p8070_0 := h8070c.1
                                      have p8070_1 := h8070c.2.1
                                      have p8070_2 := h8070c.2.2.1
                                      have p8070_3 := h8070c.2.2.2
                                      linarith only [h8029, hlam, p8070_1]
                                    · have p8070_0 := h8070c.1
                                      have p8070_1 := h8070c.2.1
                                      have p8070_2 := h8070c.2.2.1
                                      have p8070_3 := h8070c.2.2.2
                                      linarith only [h8031, hlam, p8070_0]
                                    · have p8070_0 := h8070c.1
                                      have p8070_1 := h8070c.2.1
                                      have p8070_2 := h8070c.2.2.1
                                      have p8070_3 := h8070c.2.2.2
                                      linarith only [hlam, p8070_0]
                                    · have p8070_0 := h8070c.1
                                      have p8070_1 := h8070c.2.1
                                      have p8070_2 := h8070c.2.2.1
                                      have p8070_3 := h8070c.2.2.2
                                      linarith only [h8028, h8030, h8031, h8036, h8037, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8070_1]
                                    · have p8070_0 := h8070c.1
                                      have p8070_1 := h8070c.2.1
                                      have p8070_2 := h8070c.2.2.1
                                      have p8070_3 := h8070c.2.2.2
                                      linarith only [h8021, hlam, p8070_0]
                                    · have p8070_0 := h8070c.1
                                      have p8070_1 := h8070c.2.1
                                      have p8070_2 := h8070c.2.2.1
                                      have p8070_3 := h8070c.2.2.2
                                      linarith only [h8030, hlam, p8070_1]
                                    · have p8070_0 := h8070c.1
                                      have p8070_1 := h8070c.2.1
                                      have p8070_2 := h8070c.2.2.1
                                      have p8070_3 := h8070c.2.2.2
                                      linarith only [h8032, hlam, p8070_0]
                                    · have p8070_0 := h8070c.1
                                      have p8070_1 := h8070c.2.1
                                      have p8070_2 := h8070c.2.2.1
                                      have p8070_3 := h8070c.2.2.2
                                      linarith only [h8033, hlam, p8070_0]
                                    · have p8070_0 := h8070c.1
                                      have p8070_1 := h8070c.2.1
                                      have p8070_2 := h8070c.2.2.1
                                      have p8070_3 := h8070c.2.2.2
                                      linarith only [hlam, p8070_0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8096 | h8096
                                  · linarith only [h0, h8022, h8034, h8036, h8096, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · rcases h1bigk with h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [hlam, p8098_0]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h0, hlam, p8098_0]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h6137, hlam, p8098_0]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h7252, hlam, p8098_0]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h8033, h8034, h8036, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8098_1]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [hc01, hc12, hlam, hphi, p8098_1]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [hlam, p8098_0]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h6137, hc01, hc12, hlam, hphi, p8098_1]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h7252, h8021, h8033, h8034, h8036, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8098_1]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h8033, h8034, h8036, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8098_1]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h8021, h8033, h8034, h8036, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8098_1]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h8028, hlam, p8098_1]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [hlam, p8098_0]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h7252, h8021, h8028, h8033, h8034, h8036, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8098_1]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h8028, h8033, h8034, h8036, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8098_1]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h8021, h8033, h8034, h8036, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8098_1]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h8029, hlam, p8098_1]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h8031, hlam, p8098_0]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [hlam, p8098_0]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h8028, h8031, h8033, h8034, h8036, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8098_1]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h8021, hlam, p8098_0]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h8030, hlam, p8098_1]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h8032, hlam, p8098_0]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h8033, hlam, p8098_0]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [hlam, p8098_0]
                              · linarith only [h7252, h8021, h8028, h8031, h8032, h8034, h8035, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8125 | h8125
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8126 | h8126
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8127 | h8127
                                  · rcases h1bigk with h8128c | h8128c | h8128c | h8128c | h8128c | h8128c | h8128c | h8128c | h8128c | h8128c | h8128c | h8128c | h8128c | h8128c | h8128c | h8128c | h8128c | h8128c | h8128c | h8128c | h8128c | h8128c | h8128c | h8128c | h8128c
                                    · have p8128_0 := h8128c.1
                                      have p8128_1 := h8128c.2.1
                                      have p8128_2 := h8128c.2.2.1
                                      have p8128_3 := h8128c.2.2.2
                                      linarith only [hlam, p8128_0]
                                    · have p8128_0 := h8128c.1
                                      have p8128_1 := h8128c.2.1
                                      have p8128_2 := h8128c.2.2.1
                                      have p8128_3 := h8128c.2.2.2
                                      linarith only [h0, hlam, p8128_0]
                                    · have p8128_0 := h8128c.1
                                      have p8128_1 := h8128c.2.1
                                      have p8128_2 := h8128c.2.2.1
                                      have p8128_3 := h8128c.2.2.2
                                      linarith only [h6137, hlam, p8128_0]
                                    · have p8128_0 := h8128c.1
                                      have p8128_1 := h8128c.2.1
                                      have p8128_2 := h8128c.2.2.1
                                      have p8128_3 := h8128c.2.2.2
                                      linarith only [h7252, hlam, p8128_0]
                                    · have p8128_0 := h8128c.1
                                      have p8128_1 := h8128c.2.1
                                      have p8128_2 := h8128c.2.2.1
                                      have p8128_3 := h8128c.2.2.2
                                      linarith only [h7252, h8028, h8031, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p8128_1]
                                    · have p8128_0 := h8128c.1
                                      have p8128_1 := h8128c.2.1
                                      have p8128_2 := h8128c.2.2.1
                                      have p8128_3 := h8128c.2.2.2
                                      linarith only [hc01, hc12, hlam, hphi, p8128_1]
                                    · have p8128_0 := h8128c.1
                                      have p8128_1 := h8128c.2.1
                                      have p8128_2 := h8128c.2.2.1
                                      have p8128_3 := h8128c.2.2.2
                                      linarith only [hlam, p8128_0]
                                    · have p8128_0 := h8128c.1
                                      have p8128_1 := h8128c.2.1
                                      have p8128_2 := h8128c.2.2.1
                                      have p8128_3 := h8128c.2.2.2
                                      linarith only [h6137, hc01, hc12, hlam, hphi, p8128_1]
                                    · have p8128_0 := h8128c.1
                                      have p8128_1 := h8128c.2.1
                                      have p8128_2 := h8128c.2.2.1
                                      have p8128_3 := h8128c.2.2.2
                                      linarith only [h7252, h8021, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p8128_1]
                                    · have p8128_0 := h8128c.1
                                      have p8128_1 := h8128c.2.1
                                      have p8128_2 := h8128c.2.2.1
                                      have p8128_3 := h8128c.2.2.2
                                      rcases p8128_3 (m.d 0 1) (by simp) with h8138 | h8138
                                      · linarith only [h0, h8138, hlam]
                                      · linarith only [h8021, h8138, hlam]
                                    · have p8128_0 := h8128c.1
                                      have p8128_1 := h8128c.2.1
                                      have p8128_2 := h8128c.2.2.1
                                      have p8128_3 := h8128c.2.2.2
                                      linarith only [h8021, h8030, h8125, h8127, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p8128_1]
                                    · have p8128_0 := h8128c.1
                                      have p8128_1 := h8128c.2.1
                                      have p8128_2 := h8128c.2.2.1
                                      have p8128_3 := h8128c.2.2.2
                                      linarith only [h8028, hlam, p8128_1]
                                    · have p8128_0 := h8128c.1
                                      have p8128_1 := h8128c.2.1
                                      have p8128_2 := h8128c.2.2.1
                                      have p8128_3 := h8128c.2.2.2
                                      linarith only [hlam, p8128_0]
                                    · have p8128_0 := h8128c.1
                                      have p8128_1 := h8128c.2.1
                                      have p8128_2 := h8128c.2.2.1
                                      have p8128_3 := h8128c.2.2.2
                                      linarith only [h7252, h8025, h8028, h8034, h8125, h8127, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8128_1]
                                    · have p8128_0 := h8128c.1
                                      have p8128_1 := h8128c.2.1
                                      have p8128_2 := h8128c.2.2.1
                                      have p8128_3 := h8128c.2.2.2
                                      rcases p8128_3 (m.d 0 1) (by simp) with h8145 | h8145
                                      · linarith only [h6137, h8145, hlam]
                                      · linarith only [h8021, h8145, hlam]
                                    · have p8128_0 := h8128c.1
                                      have p8128_1 := h8128c.2.1
                                      have p8128_2 := h8128c.2.2.1
                                      have p8128_3 := h8128c.2.2.2
                                      linarith only [h8021, h8030, h8125, h8127, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p8128_1]
                                    · have p8128_0 := h8128c.1
                                      have p8128_1 := h8128c.2.1
                                      have p8128_2 := h8128c.2.2.1
                                      have p8128_3 := h8128c.2.2.2
                                      linarith only [h8029, hlam, p8128_1]
                                    · have p8128_0 := h8128c.1
                                      have p8128_1 := h8128c.2.1
                                      have p8128_2 := h8128c.2.2.1
                                      have p8128_3 := h8128c.2.2.2
                                      linarith only [h8031, hlam, p8128_0]
                                    · have p8128_0 := h8128c.1
                                      have p8128_1 := h8128c.2.1
                                      have p8128_2 := h8128c.2.2.1
                                      have p8128_3 := h8128c.2.2.2
                                      linarith only [hlam, p8128_0]
                                    · have p8128_0 := h8128c.1
                                      have p8128_1 := h8128c.2.1
                                      have p8128_2 := h8128c.2.2.1
                                      have p8128_3 := h8128c.2.2.2
                                      rcases p8128_3 (m.d 0 1) (by simp) with h8152 | h8152
                                      · linarith only [h7252, h8152, hlam]
                                      · linarith only [h8021, h8152, hlam]
                                    · have p8128_0 := h8128c.1
                                      have p8128_1 := h8128c.2.1
                                      have p8128_2 := h8128c.2.2.1
                                      have p8128_3 := h8128c.2.2.2
                                      linarith only [h8021, hlam, p8128_0]
                                    · have p8128_0 := h8128c.1
                                      have p8128_1 := h8128c.2.1
                                      have p8128_2 := h8128c.2.2.1
                                      have p8128_3 := h8128c.2.2.2
                                      linarith only [h8030, hlam, p8128_1]
                                    · have p8128_0 := h8128c.1
                                      have p8128_1 := h8128c.2.1
                                      have p8128_2 := h8128c.2.2.1
                                      have p8128_3 := h8128c.2.2.2
                                      linarith only [h8032, hlam, p8128_0]
                                    · have p8128_0 := h8128c.1
                                      have p8128_1 := h8128c.2.1
                                      have p8128_2 := h8128c.2.2.1
                                      have p8128_3 := h8128c.2.2.2
                                      linarith only [h8033, hlam, p8128_0]
                                    · have p8128_0 := h8128c.1
                                      have p8128_1 := h8128c.2.1
                                      have p8128_2 := h8128c.2.2.1
                                      have p8128_3 := h8128c.2.2.2
                                      linarith only [hlam, p8128_0]
                                  · linarith only [h8027, h8034, h8125, h8127, hc04, hc35, hlam, hphi, ht0b, ht5b]
                                · linarith only [h0, h8021, h8033, h8034, h8125, h8126, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8162 | h8162
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8163 | h8163
                                  · rcases h1bigk with h8164c | h8164c | h8164c | h8164c | h8164c | h8164c | h8164c | h8164c | h8164c | h8164c | h8164c | h8164c | h8164c | h8164c | h8164c | h8164c | h8164c | h8164c | h8164c | h8164c | h8164c | h8164c | h8164c | h8164c | h8164c
                                    · have p8164_0 := h8164c.1
                                      have p8164_1 := h8164c.2.1
                                      have p8164_2 := h8164c.2.2.1
                                      have p8164_3 := h8164c.2.2.2
                                      linarith only [hlam, p8164_0]
                                    · have p8164_0 := h8164c.1
                                      have p8164_1 := h8164c.2.1
                                      have p8164_2 := h8164c.2.2.1
                                      have p8164_3 := h8164c.2.2.2
                                      linarith only [h0, hlam, p8164_0]
                                    · have p8164_0 := h8164c.1
                                      have p8164_1 := h8164c.2.1
                                      have p8164_2 := h8164c.2.2.1
                                      have p8164_3 := h8164c.2.2.2
                                      linarith only [h6137, hlam, p8164_0]
                                    · have p8164_0 := h8164c.1
                                      have p8164_1 := h8164c.2.1
                                      have p8164_2 := h8164c.2.2.1
                                      have p8164_3 := h8164c.2.2.2
                                      linarith only [h7252, hlam, p8164_0]
                                    · have p8164_0 := h8164c.1
                                      have p8164_1 := h8164c.2.1
                                      have p8164_2 := h8164c.2.2.1
                                      have p8164_3 := h8164c.2.2.2
                                      linarith only [h7252, h8028, h8031, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p8164_1]
                                    · have p8164_0 := h8164c.1
                                      have p8164_1 := h8164c.2.1
                                      have p8164_2 := h8164c.2.2.1
                                      have p8164_3 := h8164c.2.2.2
                                      linarith only [hc01, hc12, hlam, hphi, p8164_1]
                                    · have p8164_0 := h8164c.1
                                      have p8164_1 := h8164c.2.1
                                      have p8164_2 := h8164c.2.2.1
                                      have p8164_3 := h8164c.2.2.2
                                      linarith only [hlam, p8164_0]
                                    · have p8164_0 := h8164c.1
                                      have p8164_1 := h8164c.2.1
                                      have p8164_2 := h8164c.2.2.1
                                      have p8164_3 := h8164c.2.2.2
                                      linarith only [h6137, hc01, hc12, hlam, hphi, p8164_1]
                                    · have p8164_0 := h8164c.1
                                      have p8164_1 := h8164c.2.1
                                      have p8164_2 := h8164c.2.2.1
                                      have p8164_3 := h8164c.2.2.2
                                      linarith only [h7252, h8021, h8032, h8125, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8164_1]
                                    · have p8164_0 := h8164c.1
                                      have p8164_1 := h8164c.2.1
                                      have p8164_2 := h8164c.2.2.1
                                      have p8164_3 := h8164c.2.2.2
                                      linarith only [h8032, h8125, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8164_1]
                                    · have p8164_0 := h8164c.1
                                      have p8164_1 := h8164c.2.1
                                      have p8164_2 := h8164c.2.2.1
                                      have p8164_3 := h8164c.2.2.2
                                      linarith only [h8021, h8032, h8125, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8164_1]
                                    · have p8164_0 := h8164c.1
                                      have p8164_1 := h8164c.2.1
                                      have p8164_2 := h8164c.2.2.1
                                      have p8164_3 := h8164c.2.2.2
                                      linarith only [h8028, hlam, p8164_1]
                                    · have p8164_0 := h8164c.1
                                      have p8164_1 := h8164c.2.1
                                      have p8164_2 := h8164c.2.2.1
                                      have p8164_3 := h8164c.2.2.2
                                      linarith only [hlam, p8164_0]
                                    · have p8164_0 := h8164c.1
                                      have p8164_1 := h8164c.2.1
                                      have p8164_2 := h8164c.2.2.1
                                      have p8164_3 := h8164c.2.2.2
                                      linarith only [h7252, h8021, h8028, h8032, h8125, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8164_1]
                                    · have p8164_0 := h8164c.1
                                      have p8164_1 := h8164c.2.1
                                      have p8164_2 := h8164c.2.2.1
                                      have p8164_3 := h8164c.2.2.2
                                      linarith only [h8028, h8032, h8125, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8164_1]
                                    · have p8164_0 := h8164c.1
                                      have p8164_1 := h8164c.2.1
                                      have p8164_2 := h8164c.2.2.1
                                      have p8164_3 := h8164c.2.2.2
                                      linarith only [h8021, h8032, h8125, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8164_1]
                                    · have p8164_0 := h8164c.1
                                      have p8164_1 := h8164c.2.1
                                      have p8164_2 := h8164c.2.2.1
                                      have p8164_3 := h8164c.2.2.2
                                      linarith only [h8029, hlam, p8164_1]
                                    · have p8164_0 := h8164c.1
                                      have p8164_1 := h8164c.2.1
                                      have p8164_2 := h8164c.2.2.1
                                      have p8164_3 := h8164c.2.2.2
                                      linarith only [h8031, hlam, p8164_0]
                                    · have p8164_0 := h8164c.1
                                      have p8164_1 := h8164c.2.1
                                      have p8164_2 := h8164c.2.2.1
                                      have p8164_3 := h8164c.2.2.2
                                      linarith only [hlam, p8164_0]
                                    · have p8164_0 := h8164c.1
                                      have p8164_1 := h8164c.2.1
                                      have p8164_2 := h8164c.2.2.1
                                      have p8164_3 := h8164c.2.2.2
                                      linarith only [h8028, h8031, h8032, h8125, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8164_1]
                                    · have p8164_0 := h8164c.1
                                      have p8164_1 := h8164c.2.1
                                      have p8164_2 := h8164c.2.2.1
                                      have p8164_3 := h8164c.2.2.2
                                      linarith only [h8021, hlam, p8164_0]
                                    · have p8164_0 := h8164c.1
                                      have p8164_1 := h8164c.2.1
                                      have p8164_2 := h8164c.2.2.1
                                      have p8164_3 := h8164c.2.2.2
                                      linarith only [h8030, hlam, p8164_1]
                                    · have p8164_0 := h8164c.1
                                      have p8164_1 := h8164c.2.1
                                      have p8164_2 := h8164c.2.2.1
                                      have p8164_3 := h8164c.2.2.2
                                      linarith only [h8032, hlam, p8164_0]
                                    · have p8164_0 := h8164c.1
                                      have p8164_1 := h8164c.2.1
                                      have p8164_2 := h8164c.2.2.1
                                      have p8164_3 := h8164c.2.2.2
                                      linarith only [h8033, hlam, p8164_0]
                                    · have p8164_0 := h8164c.1
                                      have p8164_1 := h8164c.2.1
                                      have p8164_2 := h8164c.2.2.1
                                      have p8164_3 := h8164c.2.2.2
                                      linarith only [hlam, p8164_0]
                                  · linarith only [h0, h8023, h8034, h8162, h8163, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8191 | h8191
                                  · rcases h1bigk with h8192c | h8192c | h8192c | h8192c | h8192c | h8192c | h8192c | h8192c | h8192c | h8192c | h8192c | h8192c | h8192c | h8192c | h8192c | h8192c | h8192c | h8192c | h8192c | h8192c | h8192c | h8192c | h8192c | h8192c | h8192c
                                    · have p8192_0 := h8192c.1
                                      have p8192_1 := h8192c.2.1
                                      have p8192_2 := h8192c.2.2.1
                                      have p8192_3 := h8192c.2.2.2
                                      linarith only [hlam, p8192_0]
                                    · have p8192_0 := h8192c.1
                                      have p8192_1 := h8192c.2.1
                                      have p8192_2 := h8192c.2.2.1
                                      have p8192_3 := h8192c.2.2.2
                                      linarith only [h0, hlam, p8192_0]
                                    · have p8192_0 := h8192c.1
                                      have p8192_1 := h8192c.2.1
                                      have p8192_2 := h8192c.2.2.1
                                      have p8192_3 := h8192c.2.2.2
                                      linarith only [h6137, hlam, p8192_0]
                                    · have p8192_0 := h8192c.1
                                      have p8192_1 := h8192c.2.1
                                      have p8192_2 := h8192c.2.2.1
                                      have p8192_3 := h8192c.2.2.2
                                      linarith only [h7252, hlam, p8192_0]
                                    · have p8192_0 := h8192c.1
                                      have p8192_1 := h8192c.2.1
                                      have p8192_2 := h8192c.2.2.1
                                      have p8192_3 := h8192c.2.2.2
                                      linarith only [h8032, h8034, h8162, h8191, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8192_1]
                                    · have p8192_0 := h8192c.1
                                      have p8192_1 := h8192c.2.1
                                      have p8192_2 := h8192c.2.2.1
                                      have p8192_3 := h8192c.2.2.2
                                      linarith only [hc01, hc12, hlam, hphi, p8192_1]
                                    · have p8192_0 := h8192c.1
                                      have p8192_1 := h8192c.2.1
                                      have p8192_2 := h8192c.2.2.1
                                      have p8192_3 := h8192c.2.2.2
                                      linarith only [hlam, p8192_0]
                                    · have p8192_0 := h8192c.1
                                      have p8192_1 := h8192c.2.1
                                      have p8192_2 := h8192c.2.2.1
                                      have p8192_3 := h8192c.2.2.2
                                      linarith only [h6137, hc01, hc12, hlam, hphi, p8192_1]
                                    · have p8192_0 := h8192c.1
                                      have p8192_1 := h8192c.2.1
                                      have p8192_2 := h8192c.2.2.1
                                      have p8192_3 := h8192c.2.2.2
                                      linarith only [h7252, h8021, h8032, h8034, h8162, h8191, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8192_1]
                                    · have p8192_0 := h8192c.1
                                      have p8192_1 := h8192c.2.1
                                      have p8192_2 := h8192c.2.2.1
                                      have p8192_3 := h8192c.2.2.2
                                      linarith only [h8032, h8034, h8162, h8191, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8192_1]
                                    · have p8192_0 := h8192c.1
                                      have p8192_1 := h8192c.2.1
                                      have p8192_2 := h8192c.2.2.1
                                      have p8192_3 := h8192c.2.2.2
                                      linarith only [h8021, h8032, h8034, h8162, h8191, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8192_1]
                                    · have p8192_0 := h8192c.1
                                      have p8192_1 := h8192c.2.1
                                      have p8192_2 := h8192c.2.2.1
                                      have p8192_3 := h8192c.2.2.2
                                      linarith only [h8028, hlam, p8192_1]
                                    · have p8192_0 := h8192c.1
                                      have p8192_1 := h8192c.2.1
                                      have p8192_2 := h8192c.2.2.1
                                      have p8192_3 := h8192c.2.2.2
                                      linarith only [hlam, p8192_0]
                                    · have p8192_0 := h8192c.1
                                      have p8192_1 := h8192c.2.1
                                      have p8192_2 := h8192c.2.2.1
                                      have p8192_3 := h8192c.2.2.2
                                      linarith only [h7252, h8021, h8028, h8032, h8034, h8162, h8191, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8192_1]
                                    · have p8192_0 := h8192c.1
                                      have p8192_1 := h8192c.2.1
                                      have p8192_2 := h8192c.2.2.1
                                      have p8192_3 := h8192c.2.2.2
                                      linarith only [h8028, h8032, h8034, h8162, h8191, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8192_1]
                                    · have p8192_0 := h8192c.1
                                      have p8192_1 := h8192c.2.1
                                      have p8192_2 := h8192c.2.2.1
                                      have p8192_3 := h8192c.2.2.2
                                      linarith only [h8021, h8032, h8034, h8162, h8191, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8192_1]
                                    · have p8192_0 := h8192c.1
                                      have p8192_1 := h8192c.2.1
                                      have p8192_2 := h8192c.2.2.1
                                      have p8192_3 := h8192c.2.2.2
                                      linarith only [h8029, hlam, p8192_1]
                                    · have p8192_0 := h8192c.1
                                      have p8192_1 := h8192c.2.1
                                      have p8192_2 := h8192c.2.2.1
                                      have p8192_3 := h8192c.2.2.2
                                      linarith only [h8031, hlam, p8192_0]
                                    · have p8192_0 := h8192c.1
                                      have p8192_1 := h8192c.2.1
                                      have p8192_2 := h8192c.2.2.1
                                      have p8192_3 := h8192c.2.2.2
                                      linarith only [hlam, p8192_0]
                                    · have p8192_0 := h8192c.1
                                      have p8192_1 := h8192c.2.1
                                      have p8192_2 := h8192c.2.2.1
                                      have p8192_3 := h8192c.2.2.2
                                      linarith only [h8028, h8031, h8032, h8034, h8162, h8191, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8192_1]
                                    · have p8192_0 := h8192c.1
                                      have p8192_1 := h8192c.2.1
                                      have p8192_2 := h8192c.2.2.1
                                      have p8192_3 := h8192c.2.2.2
                                      linarith only [h8021, hlam, p8192_0]
                                    · have p8192_0 := h8192c.1
                                      have p8192_1 := h8192c.2.1
                                      have p8192_2 := h8192c.2.2.1
                                      have p8192_3 := h8192c.2.2.2
                                      linarith only [h8030, hlam, p8192_1]
                                    · have p8192_0 := h8192c.1
                                      have p8192_1 := h8192c.2.1
                                      have p8192_2 := h8192c.2.2.1
                                      have p8192_3 := h8192c.2.2.2
                                      linarith only [h8032, hlam, p8192_0]
                                    · have p8192_0 := h8192c.1
                                      have p8192_1 := h8192c.2.1
                                      have p8192_2 := h8192c.2.2.1
                                      have p8192_3 := h8192c.2.2.2
                                      linarith only [h8033, hlam, p8192_0]
                                    · have p8192_0 := h8192c.1
                                      have p8192_1 := h8192c.2.1
                                      have p8192_2 := h8192c.2.2.1
                                      have p8192_3 := h8192c.2.2.2
                                      linarith only [hlam, p8192_0]
                                  · linarith only [h0, h8021, h8033, h8034, h8191, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h0, h7252, h8022, h8025, h8027, h8033, hc01, hc12, hlam, hphi]
                        · linarith only [h6137, h8021, h8026, h8032, hlam]
                      · linarith only [h0, h6137, h8022, h8025, h8031, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h8024, h8030, hlam]
                  · linarith only [h0, h8023, h8029, hlam]
                · linarith only [h0, h8022, h8028, hlam]
              · linarith only [h7252, h8021, h8027, hlam]
            · linarith only [h6137, h8021, h8026, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h8227 | h8227
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8228 | h8228
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8229 | h8229
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8230 | h8230
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8231 | h8231
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8232 | h8232
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8233 | h8233
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8234 | h8234
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8235 | h8235
                            · linarith only [h8022, h8025, h8235, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8237 | h8237
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8238 | h8238
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8239 | h8239
                                  · rcases h1bigk with h8240c | h8240c | h8240c | h8240c | h8240c | h8240c | h8240c | h8240c | h8240c | h8240c | h8240c | h8240c | h8240c | h8240c | h8240c | h8240c | h8240c | h8240c | h8240c | h8240c | h8240c | h8240c | h8240c | h8240c | h8240c
                                    · have p8240_0 := h8240c.1
                                      have p8240_1 := h8240c.2.1
                                      have p8240_2 := h8240c.2.2.1
                                      have p8240_3 := h8240c.2.2.2
                                      linarith only [hlam, p8240_0]
                                    · have p8240_0 := h8240c.1
                                      have p8240_1 := h8240c.2.1
                                      have p8240_2 := h8240c.2.2.1
                                      have p8240_3 := h8240c.2.2.2
                                      linarith only [h0, hlam, p8240_0]
                                    · have p8240_0 := h8240c.1
                                      have p8240_1 := h8240c.2.1
                                      have p8240_2 := h8240c.2.2.1
                                      have p8240_3 := h8240c.2.2.2
                                      linarith only [h6137, hlam, p8240_0]
                                    · have p8240_0 := h8240c.1
                                      have p8240_1 := h8240c.2.1
                                      have p8240_2 := h8240c.2.2.1
                                      have p8240_3 := h8240c.2.2.2
                                      linarith only [h7252, hlam, p8240_0]
                                    · have p8240_0 := h8240c.1
                                      have p8240_1 := h8240c.2.1
                                      have p8240_2 := h8240c.2.2.1
                                      have p8240_3 := h8240c.2.2.2
                                      linarith only [h6137, h8025, h8229, h8231, h8232, h8237, h8239, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8240_1]
                                    · have p8240_0 := h8240c.1
                                      have p8240_1 := h8240c.2.1
                                      have p8240_2 := h8240c.2.2.1
                                      have p8240_3 := h8240c.2.2.2
                                      linarith only [hc01, hc12, hlam, hphi, p8240_1]
                                    · have p8240_0 := h8240c.1
                                      have p8240_1 := h8240c.2.1
                                      have p8240_2 := h8240c.2.2.1
                                      have p8240_3 := h8240c.2.2.2
                                      linarith only [hlam, p8240_0]
                                    · have p8240_0 := h8240c.1
                                      have p8240_1 := h8240c.2.1
                                      have p8240_2 := h8240c.2.2.1
                                      have p8240_3 := h8240c.2.2.2
                                      linarith only [h8025, h8232, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8240_1]
                                    · have p8240_0 := h8240c.1
                                      have p8240_1 := h8240c.2.1
                                      have p8240_2 := h8240c.2.2.1
                                      have p8240_3 := h8240c.2.2.2
                                      linarith only [h6137, h8021, h8025, h8231, h8232, h8237, h8239, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8240_1]
                                    · have p8240_0 := h8240c.1
                                      have p8240_1 := h8240c.2.1
                                      have p8240_2 := h8240c.2.2.1
                                      have p8240_3 := h8240c.2.2.2
                                      rcases p8240_3 (m.d 0 1) (by simp) with h8250 | h8250
                                      · linarith only [h0, h8250, hlam]
                                      · linarith only [h8021, h8250, hlam]
                                    · have p8240_0 := h8240c.1
                                      have p8240_1 := h8240c.2.1
                                      have p8240_2 := h8240c.2.2.1
                                      have p8240_3 := h8240c.2.2.2
                                      linarith only [h8021, h8231, h8237, h8239, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p8240_1]
                                    · have p8240_0 := h8240c.1
                                      have p8240_1 := h8240c.2.1
                                      have p8240_2 := h8240c.2.2.1
                                      have p8240_3 := h8240c.2.2.2
                                      linarith only [h8229, hlam, p8240_1]
                                    · have p8240_0 := h8240c.1
                                      have p8240_1 := h8240c.2.1
                                      have p8240_2 := h8240c.2.2.1
                                      have p8240_3 := h8240c.2.2.2
                                      linarith only [hlam, p8240_0]
                                    · have p8240_0 := h8240c.1
                                      have p8240_1 := h8240c.2.1
                                      have p8240_2 := h8240c.2.2.1
                                      have p8240_3 := h8240c.2.2.2
                                      linarith only [h6137, h8021, h8025, h8229, h8231, h8232, h8237, h8239, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8240_1]
                                    · have p8240_0 := h8240c.1
                                      have p8240_1 := h8240c.2.1
                                      have p8240_2 := h8240c.2.2.1
                                      have p8240_3 := h8240c.2.2.2
                                      rcases p8240_3 (m.d 0 1) (by simp) with h8257 | h8257
                                      · linarith only [h6137, h8257, hlam]
                                      · linarith only [h8021, h8257, hlam]
                                    · have p8240_0 := h8240c.1
                                      have p8240_1 := h8240c.2.1
                                      have p8240_2 := h8240c.2.2.1
                                      have p8240_3 := h8240c.2.2.2
                                      linarith only [h8021, h8231, h8237, h8239, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p8240_1]
                                    · have p8240_0 := h8240c.1
                                      have p8240_1 := h8240c.2.1
                                      have p8240_2 := h8240c.2.2.1
                                      have p8240_3 := h8240c.2.2.2
                                      linarith only [h8230, hlam, p8240_1]
                                    · have p8240_0 := h8240c.1
                                      have p8240_1 := h8240c.2.1
                                      have p8240_2 := h8240c.2.2.1
                                      have p8240_3 := h8240c.2.2.2
                                      linarith only [h8232, hlam, p8240_0]
                                    · have p8240_0 := h8240c.1
                                      have p8240_1 := h8240c.2.1
                                      have p8240_2 := h8240c.2.2.1
                                      have p8240_3 := h8240c.2.2.2
                                      linarith only [hlam, p8240_0]
                                    · have p8240_0 := h8240c.1
                                      have p8240_1 := h8240c.2.1
                                      have p8240_2 := h8240c.2.2.1
                                      have p8240_3 := h8240c.2.2.2
                                      rcases p8240_3 (m.d 0 1) (by simp) with h8264 | h8264
                                      · linarith only [h7252, h8264, hlam]
                                      · linarith only [h8021, h8264, hlam]
                                    · have p8240_0 := h8240c.1
                                      have p8240_1 := h8240c.2.1
                                      have p8240_2 := h8240c.2.2.1
                                      have p8240_3 := h8240c.2.2.2
                                      linarith only [h8021, hlam, p8240_0]
                                    · have p8240_0 := h8240c.1
                                      have p8240_1 := h8240c.2.1
                                      have p8240_2 := h8240c.2.2.1
                                      have p8240_3 := h8240c.2.2.2
                                      linarith only [h8231, hlam, p8240_1]
                                    · have p8240_0 := h8240c.1
                                      have p8240_1 := h8240c.2.1
                                      have p8240_2 := h8240c.2.2.1
                                      have p8240_3 := h8240c.2.2.2
                                      linarith only [h8233, hlam, p8240_0]
                                    · have p8240_0 := h8240c.1
                                      have p8240_1 := h8240c.2.1
                                      have p8240_2 := h8240c.2.2.1
                                      have p8240_3 := h8240c.2.2.2
                                      linarith only [h8234, hlam, p8240_0]
                                    · have p8240_0 := h8240c.1
                                      have p8240_1 := h8240c.2.1
                                      have p8240_2 := h8240c.2.2.1
                                      have p8240_3 := h8240c.2.2.2
                                      linarith only [hlam, p8240_0]
                                  · linarith only [h6137, h8021, h8025, h8228, h8231, h8237, h8239, hc04, hc35, hlam, hphi, ht0b, ht5b]
                                · linarith only [h6137, h8021, h8025, h8229, h8232, h8234, h8238, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h8025, h8227, h8229, h8232, h8237, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h7252, h8021, h8228, h8234, hc04, hc15, hlam, hphi, ht0b, ht5b]
                        · linarith only [h6137, h8021, h8025, h8231, h8232, h8233, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8277 | h8277
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8278 | h8278
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8279 | h8279
                            · linarith only [h6137, h8021, h8231, h8232, h8279, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8281 | h8281
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8282 | h8282
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8283 | h8283
                                  · rcases h1bigk with h8284c | h8284c | h8284c | h8284c | h8284c | h8284c | h8284c | h8284c | h8284c | h8284c | h8284c | h8284c | h8284c | h8284c | h8284c | h8284c | h8284c | h8284c | h8284c | h8284c | h8284c | h8284c | h8284c | h8284c | h8284c
                                    · have p8284_0 := h8284c.1
                                      have p8284_1 := h8284c.2.1
                                      have p8284_2 := h8284c.2.2.1
                                      have p8284_3 := h8284c.2.2.2
                                      linarith only [hlam, p8284_0]
                                    · have p8284_0 := h8284c.1
                                      have p8284_1 := h8284c.2.1
                                      have p8284_2 := h8284c.2.2.1
                                      have p8284_3 := h8284c.2.2.2
                                      linarith only [h0, hlam, p8284_0]
                                    · have p8284_0 := h8284c.1
                                      have p8284_1 := h8284c.2.1
                                      have p8284_2 := h8284c.2.2.1
                                      have p8284_3 := h8284c.2.2.2
                                      linarith only [h6137, hlam, p8284_0]
                                    · have p8284_0 := h8284c.1
                                      have p8284_1 := h8284c.2.1
                                      have p8284_2 := h8284c.2.2.1
                                      have p8284_3 := h8284c.2.2.2
                                      linarith only [h7252, hlam, p8284_0]
                                    · have p8284_0 := h8284c.1
                                      have p8284_1 := h8284c.2.1
                                      have p8284_2 := h8284c.2.2.1
                                      have p8284_3 := h8284c.2.2.2
                                      linarith only [h6137, h8231, h8232, h8281, h8283, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8284_1]
                                    · have p8284_0 := h8284c.1
                                      have p8284_1 := h8284c.2.1
                                      have p8284_2 := h8284c.2.2.1
                                      have p8284_3 := h8284c.2.2.2
                                      linarith only [hc01, hc12, hlam, hphi, p8284_1]
                                    · have p8284_0 := h8284c.1
                                      have p8284_1 := h8284c.2.1
                                      have p8284_2 := h8284c.2.2.1
                                      have p8284_3 := h8284c.2.2.2
                                      linarith only [hlam, p8284_0]
                                    · have p8284_0 := h8284c.1
                                      have p8284_1 := h8284c.2.1
                                      have p8284_2 := h8284c.2.2.1
                                      have p8284_3 := h8284c.2.2.2
                                      linarith only [h6137, h8021, h8231, h8281, h8283, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8284_1]
                                    · have p8284_0 := h8284c.1
                                      have p8284_1 := h8284c.2.1
                                      have p8284_2 := h8284c.2.2.1
                                      have p8284_3 := h8284c.2.2.2
                                      linarith only [h7252, h8021, h8231, h8281, h8283, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8284_1]
                                    · have p8284_0 := h8284c.1
                                      have p8284_1 := h8284c.2.1
                                      have p8284_2 := h8284c.2.2.1
                                      have p8284_3 := h8284c.2.2.2
                                      rcases p8284_3 (m.d 0 1) (by simp) with h8294 | h8294
                                      · linarith only [h0, h8294, hlam]
                                      · linarith only [h8021, h8294, hlam]
                                    · have p8284_0 := h8284c.1
                                      have p8284_1 := h8284c.2.1
                                      have p8284_2 := h8284c.2.2.1
                                      have p8284_3 := h8284c.2.2.2
                                      linarith only [h8021, h8231, h8281, h8283, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p8284_1]
                                    · have p8284_0 := h8284c.1
                                      have p8284_1 := h8284c.2.1
                                      have p8284_2 := h8284c.2.2.1
                                      have p8284_3 := h8284c.2.2.2
                                      linarith only [h8229, hlam, p8284_1]
                                    · have p8284_0 := h8284c.1
                                      have p8284_1 := h8284c.2.1
                                      have p8284_2 := h8284c.2.2.1
                                      have p8284_3 := h8284c.2.2.2
                                      linarith only [hlam, p8284_0]
                                    · have p8284_0 := h8284c.1
                                      have p8284_1 := h8284c.2.1
                                      have p8284_2 := h8284c.2.2.1
                                      have p8284_3 := h8284c.2.2.2
                                      linarith only [h8232, hlam, p8284_1]
                                    · have p8284_0 := h8284c.1
                                      have p8284_1 := h8284c.2.1
                                      have p8284_2 := h8284c.2.2.1
                                      have p8284_3 := h8284c.2.2.2
                                      linarith only [h8231, h8232, h8281, h8283, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8284_1]
                                    · have p8284_0 := h8284c.1
                                      have p8284_1 := h8284c.2.1
                                      have p8284_2 := h8284c.2.2.1
                                      have p8284_3 := h8284c.2.2.2
                                      linarith only [h8021, h8231, h8232, h8281, h8283, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8284_1]
                                    · have p8284_0 := h8284c.1
                                      have p8284_1 := h8284c.2.1
                                      have p8284_2 := h8284c.2.2.1
                                      have p8284_3 := h8284c.2.2.2
                                      linarith only [h8230, hlam, p8284_1]
                                    · have p8284_0 := h8284c.1
                                      have p8284_1 := h8284c.2.1
                                      have p8284_2 := h8284c.2.2.1
                                      have p8284_3 := h8284c.2.2.2
                                      linarith only [h8232, hc13, hc34, hlam, hphi, p8284_1]
                                    · have p8284_0 := h8284c.1
                                      have p8284_1 := h8284c.2.1
                                      have p8284_2 := h8284c.2.2.1
                                      have p8284_3 := h8284c.2.2.2
                                      linarith only [hlam, p8284_0]
                                    · have p8284_0 := h8284c.1
                                      have p8284_1 := h8284c.2.1
                                      have p8284_2 := h8284c.2.2.1
                                      have p8284_3 := h8284c.2.2.2
                                      rcases p8284_3 (m.d 0 1) (by simp) with h8306 | h8306
                                      · linarith only [h7252, h8306, hlam]
                                      · linarith only [h8021, h8306, hlam]
                                    · have p8284_0 := h8284c.1
                                      have p8284_1 := h8284c.2.1
                                      have p8284_2 := h8284c.2.2.1
                                      have p8284_3 := h8284c.2.2.2
                                      linarith only [h8021, hlam, p8284_0]
                                    · have p8284_0 := h8284c.1
                                      have p8284_1 := h8284c.2.1
                                      have p8284_2 := h8284c.2.2.1
                                      have p8284_3 := h8284c.2.2.2
                                      linarith only [h8231, hlam, p8284_1]
                                    · have p8284_0 := h8284c.1
                                      have p8284_1 := h8284c.2.1
                                      have p8284_2 := h8284c.2.2.1
                                      have p8284_3 := h8284c.2.2.2
                                      linarith only [h8277, hlam, p8284_0]
                                    · have p8284_0 := h8284c.1
                                      have p8284_1 := h8284c.2.1
                                      have p8284_2 := h8284c.2.2.1
                                      have p8284_3 := h8284c.2.2.2
                                      linarith only [h8278, hlam, p8284_0]
                                    · have p8284_0 := h8284c.1
                                      have p8284_1 := h8284c.2.1
                                      have p8284_2 := h8284c.2.2.1
                                      have p8284_3 := h8284c.2.2.2
                                      linarith only [hlam, p8284_0]
                                  · linarith only [h7252, h8228, h8232, h8283, hlam]
                                · linarith only [h6137, h8021, h8232, h8278, h8279, h8282, hc23, hc34, hlam, hphi]
                              · linarith only [h6137, h8227, h8232, h8281, hc23, hc34, hlam, hphi]
                          · linarith only [h7252, h8228, h8278, hlam]
                        · linarith only [h6137, h8227, h8277, hlam]
                    · linarith only [h0, h8024, h8231, hlam]
                  · linarith only [h0, h8023, h8230, hlam]
                · linarith only [h0, h8022, h8229, hlam]
              · linarith only [h6137, h8021, h8025, h8228, hlam]
            · linarith only [h6137, h8021, h8227, hlam]
        · linarith only [h0, h8021, h8024, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h8325 | h8325
        · rcases m.htr 0 3 4 (by decide) (by decide) with h8326 | h8326
          · linarith only [h8022, h8023, h8326, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h8328 | h8328
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8329 | h8329
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8330 | h8330
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8331 | h8331
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8332 | h8332
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8333 | h8333
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8334 | h8334
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8335 | h8335
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8336 | h8336
                            · linarith only [h6137, h8022, h8023, h8326, h8331, h8336, hc01, hc12, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8338 | h8338
                              · linarith only [h8022, h8023, h8330, h8333, h8336, h8338, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h8022, h8023, h8328, h8330, h8333, h8336, h8338, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h7252, h8021, h8329, h8332, h8335, hc04, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h8022, h8023, h8326, h8333, h8334, hc23, hc35, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8343 | h8343
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8344 | h8344
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8345 | h8345
                            · linarith only [h8022, h8023, h8331, h8333, h8345, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8347 | h8347
                              · linarith only [h8022, h8023, h8331, h8347, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h8022, h8023, h8328, h8331, h8347, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h7252, h8021, h8329, h8332, h8344, hc04, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h6137, h8021, h8022, h8023, h8328, h8331, h8332, h8343, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h8023, h8331, h8332, hc02, hc25, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8353 | h8353
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8354 | h8354
                      · linarith only [h6137, h8326, h8330, h8331, h8354, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8356 | h8356
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8357 | h8357
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8358 | h8358
                            · linarith only [h0, h8022, h8331, h8354, h8358, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8360 | h8360
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8361 | h8361
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8362 | h8362
                                  · rcases h1bigk with h8363c | h8363c | h8363c | h8363c | h8363c | h8363c | h8363c | h8363c | h8363c | h8363c | h8363c | h8363c | h8363c | h8363c | h8363c | h8363c | h8363c | h8363c | h8363c | h8363c | h8363c | h8363c | h8363c | h8363c | h8363c
                                    · have p8363_0 := h8363c.1
                                      have p8363_1 := h8363c.2.1
                                      have p8363_2 := h8363c.2.2.1
                                      have p8363_3 := h8363c.2.2.2
                                      linarith only [hlam, p8363_0]
                                    · have p8363_0 := h8363c.1
                                      have p8363_1 := h8363c.2.1
                                      have p8363_2 := h8363c.2.2.1
                                      have p8363_3 := h8363c.2.2.2
                                      linarith only [h0, hlam, p8363_0]
                                    · have p8363_0 := h8363c.1
                                      have p8363_1 := h8363c.2.1
                                      have p8363_2 := h8363c.2.2.1
                                      have p8363_3 := h8363c.2.2.2
                                      linarith only [h6137, hlam, p8363_0]
                                    · have p8363_0 := h8363c.1
                                      have p8363_1 := h8363c.2.1
                                      have p8363_2 := h8363c.2.2.1
                                      have p8363_3 := h8363c.2.2.2
                                      linarith only [h7252, hlam, p8363_0]
                                    · have p8363_0 := h8363c.1
                                      have p8363_1 := h8363c.2.1
                                      have p8363_2 := h8363c.2.2.1
                                      have p8363_3 := h8363c.2.2.2
                                      linarith only [h6137, h8353, h8360, h8362, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p8363_1]
                                    · have p8363_0 := h8363c.1
                                      have p8363_1 := h8363c.2.1
                                      have p8363_2 := h8363c.2.2.1
                                      have p8363_3 := h8363c.2.2.2
                                      linarith only [h8331, h8358, hc01, hc34, hlam, hphi, ht12, ht23, p8363_1]
                                    · have p8363_0 := h8363c.1
                                      have p8363_1 := h8363c.2.1
                                      have p8363_2 := h8363c.2.2.1
                                      have p8363_3 := h8363c.2.2.2
                                      linarith only [hlam, p8363_0]
                                    · have p8363_0 := h8363c.1
                                      have p8363_1 := h8363c.2.1
                                      have p8363_2 := h8363c.2.2.1
                                      have p8363_3 := h8363c.2.2.2
                                      linarith only [h8331, h8358, hc13, hc34, hlam, hphi, p8363_1]
                                    · have p8363_0 := h8363c.1
                                      have p8363_1 := h8363c.2.1
                                      have p8363_2 := h8363c.2.2.1
                                      have p8363_3 := h8363c.2.2.2
                                      linarith only [h8331, hlam, p8363_0]
                                    · have p8363_0 := h8363c.1
                                      have p8363_1 := h8363c.2.1
                                      have p8363_2 := h8363c.2.2.1
                                      have p8363_3 := h8363c.2.2.2
                                      linarith only [h8331, h8353, h8358, h8360, h8362, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8363_1]
                                    · have p8363_0 := h8363c.1
                                      have p8363_1 := h8363c.2.1
                                      have p8363_2 := h8363c.2.2.1
                                      have p8363_3 := h8363c.2.2.2
                                      linarith only [h8021, h8353, h8360, h8362, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p8363_1]
                                    · have p8363_0 := h8363c.1
                                      have p8363_1 := h8363c.2.1
                                      have p8363_2 := h8363c.2.2.1
                                      have p8363_3 := h8363c.2.2.2
                                      linarith only [h8330, hlam, p8363_1]
                                    · have p8363_0 := h8363c.1
                                      have p8363_1 := h8363c.2.1
                                      have p8363_2 := h8363c.2.2.1
                                      have p8363_3 := h8363c.2.2.2
                                      linarith only [hlam, p8363_0]
                                    · have p8363_0 := h8363c.1
                                      have p8363_1 := h8363c.2.1
                                      have p8363_2 := h8363c.2.2.1
                                      have p8363_3 := h8363c.2.2.2
                                      linarith only [h8354, hlam, p8363_1]
                                    · have p8363_0 := h8363c.1
                                      have p8363_1 := h8363c.2.1
                                      have p8363_2 := h8363c.2.2.1
                                      have p8363_3 := h8363c.2.2.2
                                      linarith only [h8330, h8331, h8353, h8358, h8360, h8362, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8363_1]
                                    · have p8363_0 := h8363c.1
                                      have p8363_1 := h8363c.2.1
                                      have p8363_2 := h8363c.2.2.1
                                      have p8363_3 := h8363c.2.2.2
                                      linarith only [h8021, h8331, h8353, h8358, h8360, h8362, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8363_1]
                                    · have p8363_0 := h8363c.1
                                      have p8363_1 := h8363c.2.1
                                      have p8363_2 := h8363c.2.2.1
                                      have p8363_3 := h8363c.2.2.2
                                      linarith only [h0, h8331, h8358, hc02, hc34, hlam, hphi, ht23, p8363_1]
                                    · have p8363_0 := h8363c.1
                                      have p8363_1 := h8363c.2.1
                                      have p8363_2 := h8363c.2.2.1
                                      have p8363_3 := h8363c.2.2.2
                                      linarith only [h6137, h8021, h8331, h8353, h8358, h8360, h8362, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8363_1]
                                    · have p8363_0 := h8363c.1
                                      have p8363_1 := h8363c.2.1
                                      have p8363_2 := h8363c.2.2.1
                                      have p8363_3 := h8363c.2.2.2
                                      linarith only [hlam, p8363_0]
                                    · have p8363_0 := h8363c.1
                                      have p8363_1 := h8363c.2.1
                                      have p8363_2 := h8363c.2.2.1
                                      have p8363_3 := h8363c.2.2.2
                                      rcases p8363_3 (m.d 0 1) (by simp) with h8383 | h8383
                                      · linarith only [h7252, h8383, hlam]
                                      · linarith only [h8021, h8383, hlam]
                                    · have p8363_0 := h8363c.1
                                      have p8363_1 := h8363c.2.1
                                      have p8363_2 := h8363c.2.2.1
                                      have p8363_3 := h8363c.2.2.2
                                      linarith only [h8021, hlam, p8363_0]
                                    · have p8363_0 := h8363c.1
                                      have p8363_1 := h8363c.2.1
                                      have p8363_2 := h8363c.2.2.1
                                      have p8363_3 := h8363c.2.2.2
                                      linarith only [h8353, hlam, p8363_1]
                                    · have p8363_0 := h8363c.1
                                      have p8363_1 := h8363c.2.1
                                      have p8363_2 := h8363c.2.2.1
                                      have p8363_3 := h8363c.2.2.2
                                      linarith only [h8356, hlam, p8363_0]
                                    · have p8363_0 := h8363c.1
                                      have p8363_1 := h8363c.2.1
                                      have p8363_2 := h8363c.2.2.1
                                      have p8363_3 := h8363c.2.2.2
                                      linarith only [h8357, hlam, p8363_0]
                                    · have p8363_0 := h8363c.1
                                      have p8363_1 := h8363c.2.1
                                      have p8363_2 := h8363c.2.2.1
                                      have p8363_3 := h8363c.2.2.2
                                      linarith only [hlam, p8363_0]
                                  · linarith only [h8022, h8023, h8358, h8360, h8362, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                · linarith only [h6137, h8021, h8330, h8331, h8357, h8361, hlam]
                              · linarith only [h6137, h8328, h8330, h8331, h8358, h8360, hc23, hc34, hlam, hphi]
                          · linarith only [h0, h8021, h8329, h8331, h8357, hc04, hc15, hlam, hphi, ht0b, ht5b]
                        · linarith only [h6137, h8021, h8022, h8328, h8353, h8356, hc02, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h8325, h8353, hlam]
                · linarith only [h0, h8022, h8330, hlam]
              · linarith only [h7252, h8021, h8329, hlam]
            · linarith only [h6137, h8021, h8328, hlam]
        · linarith only [h0, h8021, h8325, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h8401 | h8401
      · rcases m.htr 0 2 5 (by decide) (by decide) with h8402 | h8402
        · rcases m.htr 0 3 4 (by decide) (by decide) with h8403 | h8403
          · rcases m.htr 0 3 5 (by decide) (by decide) with h8404 | h8404
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8405 | h8405
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8406 | h8406
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8407 | h8407
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8408 | h8408
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8409 | h8409
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8410 | h8410
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8411 | h8411
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8412 | h8412
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8413 | h8413
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8414 | h8414
                                · linarith only [h8022, h8401, h8406, h8414, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h8022, h8401, h8405, h8406, h8414, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h7252, h8021, h8022, h8401, h8404, h8413, hc03, hc15, hlam, hphi, ht0b, ht5b]
                            · linarith only [h7252, h8021, h8022, h8401, h8403, h8412, hc03, hc15, hlam, hphi, ht0b, ht5b]
                          · linarith only [h7252, h8021, h8401, h8405, h8408, h8411, hc02, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h6137, h8404, h8410, hlam]
                      · linarith only [h8022, h8401, h8403, h8406, h8409, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h7252, h8022, h8401, h8406, h8408, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h7252, h8021, h8022, h8401, h8406, h8407, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8424 | h8424
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8425 | h8425
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8426 | h8426
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8427 | h8427
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8428 | h8428
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8429 | h8429
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8430 | h8430
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8431 | h8431
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8432 | h8432
                                  · rcases h1bigk with h8433c | h8433c | h8433c | h8433c | h8433c | h8433c | h8433c | h8433c | h8433c | h8433c | h8433c | h8433c | h8433c | h8433c | h8433c | h8433c | h8433c | h8433c | h8433c | h8433c | h8433c | h8433c | h8433c | h8433c | h8433c
                                    · have p8433_0 := h8433c.1
                                      have p8433_1 := h8433c.2.1
                                      have p8433_2 := h8433c.2.2.1
                                      have p8433_3 := h8433c.2.2.2
                                      linarith only [hlam, p8433_0]
                                    · have p8433_0 := h8433c.1
                                      have p8433_1 := h8433c.2.1
                                      have p8433_2 := h8433c.2.2.1
                                      have p8433_3 := h8433c.2.2.2
                                      linarith only [h0, hlam, p8433_0]
                                    · have p8433_0 := h8433c.1
                                      have p8433_1 := h8433c.2.1
                                      have p8433_2 := h8433c.2.2.1
                                      have p8433_3 := h8433c.2.2.2
                                      linarith only [h6137, hlam, p8433_0]
                                    · have p8433_0 := h8433c.1
                                      have p8433_1 := h8433c.2.1
                                      have p8433_2 := h8433c.2.2.1
                                      have p8433_3 := h8433c.2.2.2
                                      linarith only [h7252, hlam, p8433_0]
                                    · have p8433_0 := h8433c.1
                                      have p8433_1 := h8433c.2.1
                                      have p8433_2 := h8433c.2.2.1
                                      have p8433_3 := h8433c.2.2.2
                                      linarith only [h7252, h8424, h8425, h8430, h8432, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8433_1]
                                    · have p8433_0 := h8433c.1
                                      have p8433_1 := h8433c.2.1
                                      have p8433_2 := h8433c.2.2.1
                                      have p8433_3 := h8433c.2.2.2
                                      linarith only [h8406, hc01, hc23, hlam, hphi, ht12, p8433_1]
                                    · have p8433_0 := h8433c.1
                                      have p8433_1 := h8433c.2.1
                                      have p8433_2 := h8433c.2.2.1
                                      have p8433_3 := h8433c.2.2.2
                                      linarith only [hlam, p8433_0]
                                    · have p8433_0 := h8433c.1
                                      have p8433_1 := h8433c.2.1
                                      have p8433_2 := h8433c.2.2.1
                                      have p8433_3 := h8433c.2.2.2
                                      linarith only [h8406, hlam, p8433_0]
                                    · have p8433_0 := h8433c.1
                                      have p8433_1 := h8433c.2.1
                                      have p8433_2 := h8433c.2.2.1
                                      have p8433_3 := h8433c.2.2.2
                                      linarith only [h8406, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8433_1]
                                    · have p8433_0 := h8433c.1
                                      have p8433_1 := h8433c.2.1
                                      have p8433_2 := h8433c.2.2.1
                                      have p8433_3 := h8433c.2.2.2
                                      linarith only [h8406, h8425, h8430, h8432, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8433_1]
                                    · have p8433_0 := h8433c.1
                                      have p8433_1 := h8433c.2.1
                                      have p8433_2 := h8433c.2.2.1
                                      have p8433_3 := h8433c.2.2.2
                                      linarith only [h8021, h8406, h8425, h8430, h8432, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8433_1]
                                    · have p8433_0 := h8433c.1
                                      have p8433_1 := h8433c.2.1
                                      have p8433_2 := h8433c.2.2.1
                                      have p8433_3 := h8433c.2.2.2
                                      linarith only [h8406, hc12, hc23, hlam, hphi, p8433_1]
                                    · have p8433_0 := h8433c.1
                                      have p8433_1 := h8433c.2.1
                                      have p8433_2 := h8433c.2.2.1
                                      have p8433_3 := h8433c.2.2.2
                                      linarith only [hlam, p8433_0]
                                    · have p8433_0 := h8433c.1
                                      have p8433_1 := h8433c.2.1
                                      have p8433_2 := h8433c.2.2.1
                                      have p8433_3 := h8433c.2.2.2
                                      linarith only [h7252, h8021, h8406, h8425, h8430, h8432, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8433_1]
                                    · have p8433_0 := h8433c.1
                                      have p8433_1 := h8433c.2.1
                                      have p8433_2 := h8433c.2.2.1
                                      have p8433_3 := h8433c.2.2.2
                                      rcases p8433_3 (m.d 0 1) (by simp) with h8448 | h8448
                                      · linarith only [h6137, h8448, hlam]
                                      · linarith only [h8021, h8448, hlam]
                                    · have p8433_0 := h8433c.1
                                      have p8433_1 := h8433c.2.1
                                      have p8433_2 := h8433c.2.2.1
                                      have p8433_3 := h8433c.2.2.2
                                      linarith only [h8021, h8424, h8425, h8430, h8432, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8433_1]
                                    · have p8433_0 := h8433c.1
                                      have p8433_1 := h8433c.2.1
                                      have p8433_2 := h8433c.2.2.1
                                      have p8433_3 := h8433c.2.2.2
                                      linarith only [h8424, hlam, p8433_1]
                                    · have p8433_0 := h8433c.1
                                      have p8433_1 := h8433c.2.1
                                      have p8433_2 := h8433c.2.2.1
                                      have p8433_3 := h8433c.2.2.2
                                      linarith only [h8426, hlam, p8433_0]
                                    · have p8433_0 := h8433c.1
                                      have p8433_1 := h8433c.2.1
                                      have p8433_2 := h8433c.2.2.1
                                      have p8433_3 := h8433c.2.2.2
                                      linarith only [hlam, p8433_0]
                                    · have p8433_0 := h8433c.1
                                      have p8433_1 := h8433c.2.1
                                      have p8433_2 := h8433c.2.2.1
                                      have p8433_3 := h8433c.2.2.2
                                      linarith only [h8406, h8424, h8425, h8430, h8432, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8433_1]
                                    · have p8433_0 := h8433c.1
                                      have p8433_1 := h8433c.2.1
                                      have p8433_2 := h8433c.2.2.1
                                      have p8433_3 := h8433c.2.2.2
                                      linarith only [h8021, hlam, p8433_0]
                                    · have p8433_0 := h8433c.1
                                      have p8433_1 := h8433c.2.1
                                      have p8433_2 := h8433c.2.2.1
                                      have p8433_3 := h8433c.2.2.2
                                      linarith only [h8425, hlam, p8433_1]
                                    · have p8433_0 := h8433c.1
                                      have p8433_1 := h8433c.2.1
                                      have p8433_2 := h8433c.2.2.1
                                      have p8433_3 := h8433c.2.2.2
                                      linarith only [h8427, hlam, p8433_0]
                                    · have p8433_0 := h8433c.1
                                      have p8433_1 := h8433c.2.1
                                      have p8433_2 := h8433c.2.2.1
                                      have p8433_3 := h8433c.2.2.2
                                      linarith only [h8428, hlam, p8433_0]
                                    · have p8433_0 := h8433c.1
                                      have p8433_1 := h8433c.2.1
                                      have p8433_2 := h8433c.2.2.1
                                      have p8433_3 := h8433c.2.2.2
                                      linarith only [hlam, p8433_0]
                                  · linarith only [h0, h8021, h8406, h8428, h8432, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h7252, h8021, h8406, h8424, h8428, h8431, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h7252, h8406, h8424, h8430, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h7252, h8021, h8406, h8424, h8428, h8429, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h7252, h8021, h8405, h8428, hc04, hc15, hlam, hphi, ht0b, ht5b]
                        · linarith only [h6137, h8404, h8427, hlam]
                      · linarith only [h6137, h8022, h8401, h8403, h8426, hlam]
                    · linarith only [h0, h8402, h8425, hlam]
                  · linarith only [h0, h8401, h8424, hlam]
              · linarith only [h7252, h8021, h8405, hlam]
            · linarith only [h0, h8021, h8022, h8404, hlam]
          · linarith only [h8022, h8401, h8403, hlam]
        · linarith only [h7252, h8021, h8401, h8402, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h8474 | h8474
        · rcases m.htr 0 3 4 (by decide) (by decide) with h8475 | h8475
          · rcases m.htr 0 3 5 (by decide) (by decide) with h8476 | h8476
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8477 | h8477
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8478 | h8478
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8479 | h8479
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8480 | h8480
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8481 | h8481
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8482 | h8482
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8483 | h8483
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8484 | h8484
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8485 | h8485
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8486 | h8486
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8487 | h8487
                                  · rcases h1bigk with h8488c | h8488c | h8488c | h8488c | h8488c | h8488c | h8488c | h8488c | h8488c | h8488c | h8488c | h8488c | h8488c | h8488c | h8488c | h8488c | h8488c | h8488c | h8488c | h8488c | h8488c | h8488c | h8488c | h8488c | h8488c
                                    · have p8488_0 := h8488c.1
                                      have p8488_1 := h8488c.2.1
                                      have p8488_2 := h8488c.2.2.1
                                      have p8488_3 := h8488c.2.2.2
                                      linarith only [hlam, p8488_0]
                                    · have p8488_0 := h8488c.1
                                      have p8488_1 := h8488c.2.1
                                      have p8488_2 := h8488c.2.2.1
                                      have p8488_3 := h8488c.2.2.2
                                      linarith only [h0, hlam, p8488_0]
                                    · have p8488_0 := h8488c.1
                                      have p8488_1 := h8488c.2.1
                                      have p8488_2 := h8488c.2.2.1
                                      have p8488_3 := h8488c.2.2.2
                                      linarith only [h6137, hlam, p8488_0]
                                    · have p8488_0 := h8488c.1
                                      have p8488_1 := h8488c.2.1
                                      have p8488_2 := h8488c.2.2.1
                                      have p8488_3 := h8488c.2.2.2
                                      linarith only [h7252, hlam, p8488_0]
                                    · have p8488_0 := h8488c.1
                                      have p8488_1 := h8488c.2.1
                                      have p8488_2 := h8488c.2.2.1
                                      have p8488_3 := h8488c.2.2.2
                                      linarith only [h0, h8480, h8485, h8487, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8488_1]
                                    · have p8488_0 := h8488c.1
                                      have p8488_1 := h8488c.2.1
                                      have p8488_2 := h8488c.2.2.1
                                      have p8488_3 := h8488c.2.2.2
                                      linarith only [hc01, hc12, hlam, hphi, p8488_1]
                                    · have p8488_0 := h8488c.1
                                      have p8488_1 := h8488c.2.1
                                      have p8488_2 := h8488c.2.2.1
                                      have p8488_3 := h8488c.2.2.2
                                      linarith only [hlam, p8488_0]
                                    · have p8488_0 := h8488c.1
                                      have p8488_1 := h8488c.2.1
                                      have p8488_2 := h8488c.2.2.1
                                      have p8488_3 := h8488c.2.2.2
                                      linarith only [h6137, h8021, h8480, h8485, h8487, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8488_1]
                                    · have p8488_0 := h8488c.1
                                      have p8488_1 := h8488c.2.1
                                      have p8488_2 := h8488c.2.2.1
                                      have p8488_3 := h8488c.2.2.2
                                      linarith only [h7252, h8021, h8480, h8485, h8487, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8488_1]
                                    · have p8488_0 := h8488c.1
                                      have p8488_1 := h8488c.2.1
                                      have p8488_2 := h8488c.2.2.1
                                      have p8488_3 := h8488c.2.2.2
                                      rcases p8488_3 (m.d 0 1) (by simp) with h8498 | h8498
                                      · linarith only [h0, h8498, hlam]
                                      · linarith only [h8021, h8498, hlam]
                                    · have p8488_0 := h8488c.1
                                      have p8488_1 := h8488c.2.1
                                      have p8488_2 := h8488c.2.2.1
                                      have p8488_3 := h8488c.2.2.2
                                      linarith only [h8021, h8480, h8485, h8487, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p8488_1]
                                    · have p8488_0 := h8488c.1
                                      have p8488_1 := h8488c.2.1
                                      have p8488_2 := h8488c.2.2.1
                                      have p8488_3 := h8488c.2.2.2
                                      linarith only [h8478, hlam, p8488_1]
                                    · have p8488_0 := h8488c.1
                                      have p8488_1 := h8488c.2.1
                                      have p8488_2 := h8488c.2.2.1
                                      have p8488_3 := h8488c.2.2.2
                                      linarith only [hlam, p8488_0]
                                    · have p8488_0 := h8488c.1
                                      have p8488_1 := h8488c.2.1
                                      have p8488_2 := h8488c.2.2.1
                                      have p8488_3 := h8488c.2.2.2
                                      linarith only [h8401, h8478, h8479, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p8488_1]
                                    · have p8488_0 := h8488c.1
                                      have p8488_1 := h8488c.2.1
                                      have p8488_2 := h8488c.2.2.1
                                      have p8488_3 := h8488c.2.2.2
                                      rcases p8488_3 (m.d 0 1) (by simp) with h8505 | h8505
                                      · linarith only [h6137, h8505, hlam]
                                      · linarith only [h8021, h8505, hlam]
                                    · have p8488_0 := h8488c.1
                                      have p8488_1 := h8488c.2.1
                                      have p8488_2 := h8488c.2.2.1
                                      have p8488_3 := h8488c.2.2.2
                                      linarith only [h8021, h8480, h8485, h8487, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p8488_1]
                                    · have p8488_0 := h8488c.1
                                      have p8488_1 := h8488c.2.1
                                      have p8488_2 := h8488c.2.2.1
                                      have p8488_3 := h8488c.2.2.2
                                      linarith only [h8479, hlam, p8488_1]
                                    · have p8488_0 := h8488c.1
                                      have p8488_1 := h8488c.2.1
                                      have p8488_2 := h8488c.2.2.1
                                      have p8488_3 := h8488c.2.2.2
                                      linarith only [h8481, hlam, p8488_0]
                                    · have p8488_0 := h8488c.1
                                      have p8488_1 := h8488c.2.1
                                      have p8488_2 := h8488c.2.2.1
                                      have p8488_3 := h8488c.2.2.2
                                      linarith only [hlam, p8488_0]
                                    · have p8488_0 := h8488c.1
                                      have p8488_1 := h8488c.2.1
                                      have p8488_2 := h8488c.2.2.1
                                      have p8488_3 := h8488c.2.2.2
                                      rcases p8488_3 (m.d 0 1) (by simp) with h8512 | h8512
                                      · linarith only [h7252, h8512, hlam]
                                      · linarith only [h8021, h8512, hlam]
                                    · have p8488_0 := h8488c.1
                                      have p8488_1 := h8488c.2.1
                                      have p8488_2 := h8488c.2.2.1
                                      have p8488_3 := h8488c.2.2.2
                                      linarith only [h8021, hlam, p8488_0]
                                    · have p8488_0 := h8488c.1
                                      have p8488_1 := h8488c.2.1
                                      have p8488_2 := h8488c.2.2.1
                                      have p8488_3 := h8488c.2.2.2
                                      linarith only [h8480, hlam, p8488_1]
                                    · have p8488_0 := h8488c.1
                                      have p8488_1 := h8488c.2.1
                                      have p8488_2 := h8488c.2.2.1
                                      have p8488_3 := h8488c.2.2.2
                                      linarith only [h8482, hlam, p8488_0]
                                    · have p8488_0 := h8488c.1
                                      have p8488_1 := h8488c.2.1
                                      have p8488_2 := h8488c.2.2.1
                                      have p8488_3 := h8488c.2.2.2
                                      linarith only [h8483, hlam, p8488_0]
                                    · have p8488_0 := h8488c.1
                                      have p8488_1 := h8488c.2.1
                                      have p8488_2 := h8488c.2.2.1
                                      have p8488_3 := h8488c.2.2.2
                                      linarith only [hlam, p8488_0]
                                  · linarith only [h0, h8021, h8022, h8478, h8483, h8487, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h0, h8021, h8401, h8483, h8486, hlam]
                              · linarith only [h0, h8021, h8401, h8476, h8484, h8485, hc03, hc15, hlam, hphi, ht0b, ht5b]
                            · linarith only [h8022, h8475, h8484, hlam]
                          · linarith only [h7252, h8021, h8477, h8483, hc04, hc15, hlam, hphi, ht0b, ht5b]
                        · linarith only [h6137, h8476, h8482, hlam]
                      · linarith only [h8022, h8475, h8478, h8481, hlam]
                    · linarith only [h0, h8021, h8474, h8480, hc02, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h8022, h8478, h8479, hc02, hc24, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8529 | h8529
                  · linarith only [h0, h8021, h8401, h8478, h8529, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8531 | h8531
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8532 | h8532
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8533 | h8533
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8534 | h8534
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8535 | h8535
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8536 | h8536
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8537 | h8537
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8538 | h8538
                                  · rcases h1bigk with h8539c | h8539c | h8539c | h8539c | h8539c | h8539c | h8539c | h8539c | h8539c | h8539c | h8539c | h8539c | h8539c | h8539c | h8539c | h8539c | h8539c | h8539c | h8539c | h8539c | h8539c | h8539c | h8539c | h8539c | h8539c
                                    · have p8539_0 := h8539c.1
                                      have p8539_1 := h8539c.2.1
                                      have p8539_2 := h8539c.2.2.1
                                      have p8539_3 := h8539c.2.2.2
                                      linarith only [hlam, p8539_0]
                                    · have p8539_0 := h8539c.1
                                      have p8539_1 := h8539c.2.1
                                      have p8539_2 := h8539c.2.2.1
                                      have p8539_3 := h8539c.2.2.2
                                      linarith only [h0, hlam, p8539_0]
                                    · have p8539_0 := h8539c.1
                                      have p8539_1 := h8539c.2.1
                                      have p8539_2 := h8539c.2.2.1
                                      have p8539_3 := h8539c.2.2.2
                                      linarith only [h6137, hlam, p8539_0]
                                    · have p8539_0 := h8539c.1
                                      have p8539_1 := h8539c.2.1
                                      have p8539_2 := h8539c.2.2.1
                                      have p8539_3 := h8539c.2.2.2
                                      linarith only [h7252, hlam, p8539_0]
                                    · have p8539_0 := h8539c.1
                                      have p8539_1 := h8539c.2.1
                                      have p8539_2 := h8539c.2.2.1
                                      have p8539_3 := h8539c.2.2.2
                                      linarith only [h0, h8529, h8531, h8535, h8536, h8538, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8539_1]
                                    · have p8539_0 := h8539c.1
                                      have p8539_1 := h8539c.2.1
                                      have p8539_2 := h8539c.2.2.1
                                      have p8539_3 := h8539c.2.2.2
                                      linarith only [h8529, h8535, hc01, hc23, hlam, hphi, ht12, p8539_1]
                                    · have p8539_0 := h8539c.1
                                      have p8539_1 := h8539c.2.1
                                      have p8539_2 := h8539c.2.2.1
                                      have p8539_3 := h8539c.2.2.2
                                      linarith only [hlam, p8539_0]
                                    · have p8539_0 := h8539c.1
                                      have p8539_1 := h8539c.2.1
                                      have p8539_2 := h8539c.2.2.1
                                      have p8539_3 := h8539c.2.2.2
                                      linarith only [h8478, hlam, p8539_0]
                                    · have p8539_0 := h8539c.1
                                      have p8539_1 := h8539c.2.1
                                      have p8539_2 := h8539c.2.2.1
                                      have p8539_3 := h8539c.2.2.2
                                      linarith only [h8529, hlam, p8539_0]
                                    · have p8539_0 := h8539c.1
                                      have p8539_1 := h8539c.2.1
                                      have p8539_2 := h8539c.2.2.1
                                      have p8539_3 := h8539c.2.2.2
                                      linarith only [h8529, h8531, h8535, h8536, h8538, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8539_1]
                                    · have p8539_0 := h8539c.1
                                      have p8539_1 := h8539c.2.1
                                      have p8539_2 := h8539c.2.2.1
                                      have p8539_3 := h8539c.2.2.2
                                      linarith only [h8021, h8531, h8536, h8538, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p8539_1]
                                    · have p8539_0 := h8539c.1
                                      have p8539_1 := h8539c.2.1
                                      have p8539_2 := h8539c.2.2.1
                                      have p8539_3 := h8539c.2.2.2
                                      linarith only [h8478, hc12, hc23, hlam, hphi, p8539_1]
                                    · have p8539_0 := h8539c.1
                                      have p8539_1 := h8539c.2.1
                                      have p8539_2 := h8539c.2.2.1
                                      have p8539_3 := h8539c.2.2.2
                                      linarith only [hlam, p8539_0]
                                    · have p8539_0 := h8539c.1
                                      have p8539_1 := h8539c.2.1
                                      have p8539_2 := h8539c.2.2.1
                                      have p8539_3 := h8539c.2.2.2
                                      linarith only [h0, h8021, h8478, h8529, h8531, h8536, h8538, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8539_1]
                                    · have p8539_0 := h8539c.1
                                      have p8539_1 := h8539c.2.1
                                      have p8539_2 := h8539c.2.2.1
                                      have p8539_3 := h8539c.2.2.2
                                      rcases p8539_3 (m.d 0 1) (by simp) with h8554 | h8554
                                      · linarith only [h6137, h8554, hlam]
                                      · linarith only [h8021, h8554, hlam]
                                    · have p8539_0 := h8539c.1
                                      have p8539_1 := h8539c.2.1
                                      have p8539_2 := h8539c.2.2.1
                                      have p8539_3 := h8539c.2.2.2
                                      linarith only [h8021, h8531, h8536, h8538, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p8539_1]
                                    · have p8539_0 := h8539c.1
                                      have p8539_1 := h8539c.2.1
                                      have p8539_2 := h8539c.2.2.1
                                      have p8539_3 := h8539c.2.2.2
                                      linarith only [h0, h8021, h8529, h8531, h8535, h8536, h8538, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8539_1]
                                    · have p8539_0 := h8539c.1
                                      have p8539_1 := h8539c.2.1
                                      have p8539_2 := h8539c.2.2.1
                                      have p8539_3 := h8539c.2.2.2
                                      linarith only [h8532, hlam, p8539_0]
                                    · have p8539_0 := h8539c.1
                                      have p8539_1 := h8539c.2.1
                                      have p8539_2 := h8539c.2.2.1
                                      have p8539_3 := h8539c.2.2.2
                                      linarith only [hlam, p8539_0]
                                    · have p8539_0 := h8539c.1
                                      have p8539_1 := h8539c.2.1
                                      have p8539_2 := h8539c.2.2.1
                                      have p8539_3 := h8539c.2.2.2
                                      rcases p8539_3 (m.d 0 1) (by simp) with h8561 | h8561
                                      · linarith only [h7252, h8561, hlam]
                                      · linarith only [h8021, h8561, hlam]
                                    · have p8539_0 := h8539c.1
                                      have p8539_1 := h8539c.2.1
                                      have p8539_2 := h8539c.2.2.1
                                      have p8539_3 := h8539c.2.2.2
                                      linarith only [h8021, hlam, p8539_0]
                                    · have p8539_0 := h8539c.1
                                      have p8539_1 := h8539c.2.1
                                      have p8539_2 := h8539c.2.2.1
                                      have p8539_3 := h8539c.2.2.2
                                      linarith only [h8531, hlam, p8539_1]
                                    · have p8539_0 := h8539c.1
                                      have p8539_1 := h8539c.2.1
                                      have p8539_2 := h8539c.2.2.1
                                      have p8539_3 := h8539c.2.2.2
                                      linarith only [h8533, hlam, p8539_0]
                                    · have p8539_0 := h8539c.1
                                      have p8539_1 := h8539c.2.1
                                      have p8539_2 := h8539c.2.2.1
                                      have p8539_3 := h8539c.2.2.2
                                      linarith only [h8534, hlam, p8539_0]
                                    · have p8539_0 := h8539c.1
                                      have p8539_1 := h8539c.2.1
                                      have p8539_2 := h8539c.2.2.1
                                      have p8539_3 := h8539c.2.2.2
                                      linarith only [hlam, p8539_0]
                                  · linarith only [h0, h8021, h8478, h8534, h8538, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h0, h8021, h8529, h8534, h8537, hlam]
                              · linarith only [h0, h8529, h8535, h8536, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h6137, h8021, h8475, h8478, h8534, h8535, hc03, hc45, hlam, hphi, ht0b, ht5b]
                          · linarith only [h0, h8021, h8477, h8529, h8533, h8534, hc04, hc35, hlam, hphi, ht0b, ht5b]
                        · linarith only [h6137, h8476, h8533, hlam]
                      · linarith only [h6137, h8475, h8532, hlam]
                    · linarith only [h0, h8021, h8474, h8531, hc02, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h8021, h8401, h8477, hlam]
            · linarith only [h0, h8021, h8401, h8475, h8476, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h8579 | h8579
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8580 | h8580
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8581 | h8581
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8582 | h8582
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8583 | h8583
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8584 | h8584
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8585 | h8585
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8586 | h8586
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8587 | h8587
                            · linarith only [h0, h8022, h8475, h8581, h8587, hc01, hc12, hlam, hphi]
                            · linarith only [h0, h8021, h8022, h8584, h8585, h8587, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h7252, h8021, h8580, h8585, h8586, hc04, hc35, hlam, hphi, ht0b, ht5b]
                        · linarith only [h8475, h8584, h8585, hc03, hc35, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8592 | h8592
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8593 | h8593
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8594 | h8594
                            · linarith only [h8581, h8584, h8594, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8596 | h8596
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8597 | h8597
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8598 | h8598
                                  · rcases h1bigk with h8599c | h8599c | h8599c | h8599c | h8599c | h8599c | h8599c | h8599c | h8599c | h8599c | h8599c | h8599c | h8599c | h8599c | h8599c | h8599c | h8599c | h8599c | h8599c | h8599c | h8599c | h8599c | h8599c | h8599c | h8599c
                                    · have p8599_0 := h8599c.1
                                      have p8599_1 := h8599c.2.1
                                      have p8599_2 := h8599c.2.2.1
                                      have p8599_3 := h8599c.2.2.2
                                      linarith only [hlam, p8599_0]
                                    · have p8599_0 := h8599c.1
                                      have p8599_1 := h8599c.2.1
                                      have p8599_2 := h8599c.2.2.1
                                      have p8599_3 := h8599c.2.2.2
                                      linarith only [h0, hlam, p8599_0]
                                    · have p8599_0 := h8599c.1
                                      have p8599_1 := h8599c.2.1
                                      have p8599_2 := h8599c.2.2.1
                                      have p8599_3 := h8599c.2.2.2
                                      linarith only [h6137, hlam, p8599_0]
                                    · have p8599_0 := h8599c.1
                                      have p8599_1 := h8599c.2.1
                                      have p8599_2 := h8599c.2.2.1
                                      have p8599_3 := h8599c.2.2.2
                                      linarith only [h7252, hlam, p8599_0]
                                    · have p8599_0 := h8599c.1
                                      have p8599_1 := h8599c.2.1
                                      have p8599_2 := h8599c.2.2.1
                                      have p8599_3 := h8599c.2.2.2
                                      linarith only [h0, h8022, h8583, h8596, h8598, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8599_1]
                                    · have p8599_0 := h8599c.1
                                      have p8599_1 := h8599c.2.1
                                      have p8599_2 := h8599c.2.2.1
                                      have p8599_3 := h8599c.2.2.2
                                      linarith only [hc01, hc12, hlam, hphi, p8599_1]
                                    · have p8599_0 := h8599c.1
                                      have p8599_1 := h8599c.2.1
                                      have p8599_2 := h8599c.2.2.1
                                      have p8599_3 := h8599c.2.2.2
                                      linarith only [hlam, p8599_0]
                                    · have p8599_0 := h8599c.1
                                      have p8599_1 := h8599c.2.1
                                      have p8599_2 := h8599c.2.2.1
                                      have p8599_3 := h8599c.2.2.2
                                      linarith only [h6137, h8021, h8583, h8596, h8598, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8599_1]
                                    · have p8599_0 := h8599c.1
                                      have p8599_1 := h8599c.2.1
                                      have p8599_2 := h8599c.2.2.1
                                      have p8599_3 := h8599c.2.2.2
                                      linarith only [h0, h8021, h8022, h8581, h8583, h8584, h8596, h8598, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8599_1]
                                    · have p8599_0 := h8599c.1
                                      have p8599_1 := h8599c.2.1
                                      have p8599_2 := h8599c.2.2.1
                                      have p8599_3 := h8599c.2.2.2
                                      rcases p8599_3 (m.d 0 1) (by simp) with h8609 | h8609
                                      · linarith only [h0, h8609, hlam]
                                      · linarith only [h8021, h8609, hlam]
                                    · have p8599_0 := h8599c.1
                                      have p8599_1 := h8599c.2.1
                                      have p8599_2 := h8599c.2.2.1
                                      have p8599_3 := h8599c.2.2.2
                                      linarith only [h8021, h8583, h8596, h8598, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p8599_1]
                                    · have p8599_0 := h8599c.1
                                      have p8599_1 := h8599c.2.1
                                      have p8599_2 := h8599c.2.2.1
                                      have p8599_3 := h8599c.2.2.2
                                      linarith only [h8581, hlam, p8599_1]
                                    · have p8599_0 := h8599c.1
                                      have p8599_1 := h8599c.2.1
                                      have p8599_2 := h8599c.2.2.1
                                      have p8599_3 := h8599c.2.2.2
                                      linarith only [hlam, p8599_0]
                                    · have p8599_0 := h8599c.1
                                      have p8599_1 := h8599c.2.1
                                      have p8599_2 := h8599c.2.2.1
                                      have p8599_3 := h8599c.2.2.2
                                      linarith only [h8584, hlam, p8599_1]
                                    · have p8599_0 := h8599c.1
                                      have p8599_1 := h8599c.2.1
                                      have p8599_2 := h8599c.2.2.1
                                      have p8599_3 := h8599c.2.2.2
                                      linarith only [h8583, h8584, h8596, h8598, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8599_1]
                                    · have p8599_0 := h8599c.1
                                      have p8599_1 := h8599c.2.1
                                      have p8599_2 := h8599c.2.2.1
                                      have p8599_3 := h8599c.2.2.2
                                      linarith only [h8021, h8583, h8584, h8596, h8598, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8599_1]
                                    · have p8599_0 := h8599c.1
                                      have p8599_1 := h8599c.2.1
                                      have p8599_2 := h8599c.2.2.1
                                      have p8599_3 := h8599c.2.2.2
                                      linarith only [h8582, hlam, p8599_1]
                                    · have p8599_0 := h8599c.1
                                      have p8599_1 := h8599c.2.1
                                      have p8599_2 := h8599c.2.2.1
                                      have p8599_3 := h8599c.2.2.2
                                      linarith only [h8584, hc13, hc34, hlam, hphi, p8599_1]
                                    · have p8599_0 := h8599c.1
                                      have p8599_1 := h8599c.2.1
                                      have p8599_2 := h8599c.2.2.1
                                      have p8599_3 := h8599c.2.2.2
                                      linarith only [hlam, p8599_0]
                                    · have p8599_0 := h8599c.1
                                      have p8599_1 := h8599c.2.1
                                      have p8599_2 := h8599c.2.2.1
                                      have p8599_3 := h8599c.2.2.2
                                      rcases p8599_3 (m.d 0 1) (by simp) with h8621 | h8621
                                      · linarith only [h7252, h8621, hlam]
                                      · linarith only [h8021, h8621, hlam]
                                    · have p8599_0 := h8599c.1
                                      have p8599_1 := h8599c.2.1
                                      have p8599_2 := h8599c.2.2.1
                                      have p8599_3 := h8599c.2.2.2
                                      linarith only [h8021, hlam, p8599_0]
                                    · have p8599_0 := h8599c.1
                                      have p8599_1 := h8599c.2.1
                                      have p8599_2 := h8599c.2.2.1
                                      have p8599_3 := h8599c.2.2.2
                                      linarith only [h8583, hlam, p8599_1]
                                    · have p8599_0 := h8599c.1
                                      have p8599_1 := h8599c.2.1
                                      have p8599_2 := h8599c.2.2.1
                                      have p8599_3 := h8599c.2.2.2
                                      linarith only [h8592, hlam, p8599_0]
                                    · have p8599_0 := h8599c.1
                                      have p8599_1 := h8599c.2.1
                                      have p8599_2 := h8599c.2.2.1
                                      have p8599_3 := h8599c.2.2.2
                                      linarith only [h8593, hlam, p8599_0]
                                    · have p8599_0 := h8599c.1
                                      have p8599_1 := h8599c.2.1
                                      have p8599_2 := h8599c.2.2.1
                                      have p8599_3 := h8599c.2.2.2
                                      linarith only [hlam, p8599_0]
                                  · linarith only [h0, h8021, h8022, h8475, h8580, h8583, h8596, h8598, hc04, hc35, hlam, hphi, ht0b, ht5b]
                                · linarith only [h0, h8021, h8022, h8581, h8584, h8593, h8597, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h0, h8021, h8022, h8475, h8579, h8596, hc04, hc15, hlam, hphi, ht0b, ht5b]
                          · linarith only [h0, h8021, h8022, h8580, h8581, h8584, h8593, hc04, hc15, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h8021, h8022, h8579, h8581, h8592, hc03, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h8021, h8474, h8583, hc02, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h8022, h8581, h8582, hc02, hc24, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8636 | h8636
                  · linarith only [h0, h8021, h8401, h8581, h8636, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8638 | h8638
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8639 | h8639
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8640 | h8640
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8641 | h8641
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8642 | h8642
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8643 | h8643
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8644 | h8644
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8645 | h8645
                                  · rcases h1bigk with h8646c | h8646c | h8646c | h8646c | h8646c | h8646c | h8646c | h8646c | h8646c | h8646c | h8646c | h8646c | h8646c | h8646c | h8646c | h8646c | h8646c | h8646c | h8646c | h8646c | h8646c | h8646c | h8646c | h8646c | h8646c
                                    · have p8646_0 := h8646c.1
                                      have p8646_1 := h8646c.2.1
                                      have p8646_2 := h8646c.2.2.1
                                      have p8646_3 := h8646c.2.2.2
                                      linarith only [hlam, p8646_0]
                                    · have p8646_0 := h8646c.1
                                      have p8646_1 := h8646c.2.1
                                      have p8646_2 := h8646c.2.2.1
                                      have p8646_3 := h8646c.2.2.2
                                      linarith only [h0, hlam, p8646_0]
                                    · have p8646_0 := h8646c.1
                                      have p8646_1 := h8646c.2.1
                                      have p8646_2 := h8646c.2.2.1
                                      have p8646_3 := h8646c.2.2.2
                                      linarith only [h6137, hlam, p8646_0]
                                    · have p8646_0 := h8646c.1
                                      have p8646_1 := h8646c.2.1
                                      have p8646_2 := h8646c.2.2.1
                                      have p8646_3 := h8646c.2.2.2
                                      linarith only [h7252, hlam, p8646_0]
                                    · have p8646_0 := h8646c.1
                                      have p8646_1 := h8646c.2.1
                                      have p8646_2 := h8646c.2.2.1
                                      have p8646_3 := h8646c.2.2.2
                                      linarith only [h0, h8636, h8638, h8642, h8643, h8645, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8646_1]
                                    · have p8646_0 := h8646c.1
                                      have p8646_1 := h8646c.2.1
                                      have p8646_2 := h8646c.2.2.1
                                      have p8646_3 := h8646c.2.2.2
                                      linarith only [h8636, h8642, hc01, hc23, hlam, hphi, ht12, p8646_1]
                                    · have p8646_0 := h8646c.1
                                      have p8646_1 := h8646c.2.1
                                      have p8646_2 := h8646c.2.2.1
                                      have p8646_3 := h8646c.2.2.2
                                      linarith only [hlam, p8646_0]
                                    · have p8646_0 := h8646c.1
                                      have p8646_1 := h8646c.2.1
                                      have p8646_2 := h8646c.2.2.1
                                      have p8646_3 := h8646c.2.2.2
                                      linarith only [h8581, hlam, p8646_0]
                                    · have p8646_0 := h8646c.1
                                      have p8646_1 := h8646c.2.1
                                      have p8646_2 := h8646c.2.2.1
                                      have p8646_3 := h8646c.2.2.2
                                      linarith only [h8636, hlam, p8646_0]
                                    · have p8646_0 := h8646c.1
                                      have p8646_1 := h8646c.2.1
                                      have p8646_2 := h8646c.2.2.1
                                      have p8646_3 := h8646c.2.2.2
                                      linarith only [h8636, h8638, h8642, h8643, h8645, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8646_1]
                                    · have p8646_0 := h8646c.1
                                      have p8646_1 := h8646c.2.1
                                      have p8646_2 := h8646c.2.2.1
                                      have p8646_3 := h8646c.2.2.2
                                      linarith only [h8021, h8581, h8638, h8643, h8645, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8646_1]
                                    · have p8646_0 := h8646c.1
                                      have p8646_1 := h8646c.2.1
                                      have p8646_2 := h8646c.2.2.1
                                      have p8646_3 := h8646c.2.2.2
                                      linarith only [h8581, hc12, hc23, hlam, hphi, p8646_1]
                                    · have p8646_0 := h8646c.1
                                      have p8646_1 := h8646c.2.1
                                      have p8646_2 := h8646c.2.2.1
                                      have p8646_3 := h8646c.2.2.2
                                      linarith only [hlam, p8646_0]
                                    · have p8646_0 := h8646c.1
                                      have p8646_1 := h8646c.2.1
                                      have p8646_2 := h8646c.2.2.1
                                      have p8646_3 := h8646c.2.2.2
                                      linarith only [h0, h8021, h8581, h8636, h8638, h8643, h8645, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8646_1]
                                    · have p8646_0 := h8646c.1
                                      have p8646_1 := h8646c.2.1
                                      have p8646_2 := h8646c.2.2.1
                                      have p8646_3 := h8646c.2.2.2
                                      rcases p8646_3 (m.d 0 1) (by simp) with h8661 | h8661
                                      · linarith only [h6137, h8661, hlam]
                                      · linarith only [h8021, h8661, hlam]
                                    · have p8646_0 := h8646c.1
                                      have p8646_1 := h8646c.2.1
                                      have p8646_2 := h8646c.2.2.1
                                      have p8646_3 := h8646c.2.2.2
                                      linarith only [h8021, h8638, h8643, h8645, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p8646_1]
                                    · have p8646_0 := h8646c.1
                                      have p8646_1 := h8646c.2.1
                                      have p8646_2 := h8646c.2.2.1
                                      have p8646_3 := h8646c.2.2.2
                                      linarith only [h0, h8021, h8636, h8638, h8642, h8643, h8645, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8646_1]
                                    · have p8646_0 := h8646c.1
                                      have p8646_1 := h8646c.2.1
                                      have p8646_2 := h8646c.2.2.1
                                      have p8646_3 := h8646c.2.2.2
                                      linarith only [h8639, hlam, p8646_0]
                                    · have p8646_0 := h8646c.1
                                      have p8646_1 := h8646c.2.1
                                      have p8646_2 := h8646c.2.2.1
                                      have p8646_3 := h8646c.2.2.2
                                      linarith only [hlam, p8646_0]
                                    · have p8646_0 := h8646c.1
                                      have p8646_1 := h8646c.2.1
                                      have p8646_2 := h8646c.2.2.1
                                      have p8646_3 := h8646c.2.2.2
                                      rcases p8646_3 (m.d 0 1) (by simp) with h8668 | h8668
                                      · linarith only [h7252, h8668, hlam]
                                      · linarith only [h8021, h8668, hlam]
                                    · have p8646_0 := h8646c.1
                                      have p8646_1 := h8646c.2.1
                                      have p8646_2 := h8646c.2.2.1
                                      have p8646_3 := h8646c.2.2.2
                                      linarith only [h8021, hlam, p8646_0]
                                    · have p8646_0 := h8646c.1
                                      have p8646_1 := h8646c.2.1
                                      have p8646_2 := h8646c.2.2.1
                                      have p8646_3 := h8646c.2.2.2
                                      linarith only [h8638, hlam, p8646_1]
                                    · have p8646_0 := h8646c.1
                                      have p8646_1 := h8646c.2.1
                                      have p8646_2 := h8646c.2.2.1
                                      have p8646_3 := h8646c.2.2.2
                                      linarith only [h8640, hlam, p8646_0]
                                    · have p8646_0 := h8646c.1
                                      have p8646_1 := h8646c.2.1
                                      have p8646_2 := h8646c.2.2.1
                                      have p8646_3 := h8646c.2.2.2
                                      linarith only [h8641, hlam, p8646_0]
                                    · have p8646_0 := h8646c.1
                                      have p8646_1 := h8646c.2.1
                                      have p8646_2 := h8646c.2.2.1
                                      have p8646_3 := h8646c.2.2.2
                                      linarith only [hlam, p8646_0]
                                  · linarith only [h0, h8021, h8022, h8475, h8580, h8638, h8643, h8645, hc04, hc35, hlam, hphi, ht0b, ht5b]
                                · linarith only [h7252, h8021, h8636, h8641, h8644, hlam]
                              · linarith only [h0, h8022, h8475, h8581, h8639, h8643, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h8581, h8639, h8642, hlam]
                          · linarith only [h0, h8021, h8022, h8475, h8580, h8638, h8639, h8641, hc04, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h8021, h8022, h8475, h8638, h8639, h8640, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8682 | h8682
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8683 | h8683
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8684 | h8684
                            · linarith only [h6137, h8021, h8638, h8639, h8684, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h0, h8021, h8581, h8638, h8684, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h0, h8021, h8580, h8581, h8638, h8639, h8683, hc04, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h8021, h8579, h8581, h8638, h8682, hc03, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h8021, h8474, h8638, hc02, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h8021, h8022, h8475, h8580, hlam]
            · linarith only [h0, h8021, h8022, h8579, hlam]
        · linarith only [h0, h8021, h8474, hlam]
  · exact r1l7_21_15_H_I_L_I_s10 m hb1 hb5 h0 h6137 h7252 h8021

end R2N4
