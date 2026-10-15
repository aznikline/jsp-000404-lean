import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_15S15

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6624000 in
set_option maxHeartbeats 6624000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s9 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6253 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7338 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0 := hg0
  have h6253 := hg6253
  have h7338 := hg7338
  rcases m.htr 0 1 5 (by decide) (by decide) with h8081 | h8081
  · rcases m.htr 0 2 3 (by decide) (by decide) with h8082 | h8082
    · rcases m.htr 0 2 4 (by decide) (by decide) with h8083 | h8083
      · rcases m.htr 0 2 5 (by decide) (by decide) with h8084 | h8084
        · rcases m.htr 0 3 4 (by decide) (by decide) with h8085 | h8085
          · rcases m.htr 0 3 5 (by decide) (by decide) with h8086 | h8086
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8087 | h8087
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8088 | h8088
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8089 | h8089
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8090 | h8090
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8091 | h8091
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8092 | h8092
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8093 | h8093
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8094 | h8094
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8095 | h8095
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8096 | h8096
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8097 | h8097
                                  · rcases h0bigk with h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c | h8098c
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [hlam, p8098_0]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h0, hlam, p8098_1]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h6253, hlam, p8098_0]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h7338, hlam, p8098_1]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h7338, h8091, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p8098_1]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p8098_1]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [hlam, p8098_0]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h0, h8082, h8094, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8098_1]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h0, h7338, h8081, h8090, h8095, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p8098_1]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      rcases p8098_3 (m.d 0 1) (by simp) with h8108 | h8108
                                      · linarith only [h0, h8108, hlam]
                                      · linarith only [h8081, h8108, hlam]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h8081, h8090, h8095, h8097, hc03, hc45, hlam, hphi, ht0b, ht5b, p8098_1]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h8082, hlam, p8098_1]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [hlam, p8098_0]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h6253, h7338, h8081, h8088, h8090, h8095, h8097, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8098_1]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      rcases p8098_3 (m.d 0 1) (by simp) with h8115 | h8115
                                      · linarith only [h6253, h8115, hlam]
                                      · linarith only [h8081, h8115, hlam]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h8081, h8090, h8095, h8097, hc04, hc45, hlam, hphi, ht0b, ht5b, p8098_1]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h8083, hlam, p8098_0]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h8085, hlam, p8098_0]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [hlam, p8098_0]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      rcases p8098_3 (m.d 0 1) (by simp) with h8122 | h8122
                                      · linarith only [h7338, h8122, hlam]
                                      · linarith only [h8081, h8122, hlam]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h8081, hlam, p8098_0]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h8084, hlam, p8098_1]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h8086, hlam, p8098_0]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [h8087, hlam, p8098_1]
                                    · have p8098_0 := h8098c.1
                                      have p8098_1 := h8098c.2.1
                                      have p8098_2 := h8098c.2.2.1
                                      have p8098_3 := h8098c.2.2.2
                                      linarith only [hlam, p8098_0]
                                  · rcases h0bigk with h8130c | h8130c | h8130c | h8130c | h8130c | h8130c | h8130c | h8130c | h8130c | h8130c | h8130c | h8130c | h8130c | h8130c | h8130c | h8130c | h8130c | h8130c | h8130c | h8130c | h8130c | h8130c | h8130c | h8130c | h8130c
                                    · have p8130_0 := h8130c.1
                                      have p8130_1 := h8130c.2.1
                                      have p8130_2 := h8130c.2.2.1
                                      have p8130_3 := h8130c.2.2.2
                                      linarith only [hlam, p8130_0]
                                    · have p8130_0 := h8130c.1
                                      have p8130_1 := h8130c.2.1
                                      have p8130_2 := h8130c.2.2.1
                                      have p8130_3 := h8130c.2.2.2
                                      linarith only [h0, hlam, p8130_1]
                                    · have p8130_0 := h8130c.1
                                      have p8130_1 := h8130c.2.1
                                      have p8130_2 := h8130c.2.2.1
                                      have p8130_3 := h8130c.2.2.2
                                      linarith only [h6253, hlam, p8130_0]
                                    · have p8130_0 := h8130c.1
                                      have p8130_1 := h8130c.2.1
                                      have p8130_2 := h8130c.2.2.1
                                      have p8130_3 := h8130c.2.2.2
                                      linarith only [h7338, hlam, p8130_1]
                                    · have p8130_0 := h8130c.1
                                      have p8130_1 := h8130c.2.1
                                      have p8130_2 := h8130c.2.2.1
                                      have p8130_3 := h8130c.2.2.2
                                      linarith only [h7338, h8088, h8091, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p8130_1]
                                    · have p8130_0 := h8130c.1
                                      have p8130_1 := h8130c.2.1
                                      have p8130_2 := h8130c.2.2.1
                                      have p8130_3 := h8130c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p8130_1]
                                    · have p8130_0 := h8130c.1
                                      have p8130_1 := h8130c.2.1
                                      have p8130_2 := h8130c.2.2.1
                                      have p8130_3 := h8130c.2.2.2
                                      linarith only [hlam, p8130_0]
                                    · have p8130_0 := h8130c.1
                                      have p8130_1 := h8130c.2.1
                                      have p8130_2 := h8130c.2.2.1
                                      have p8130_3 := h8130c.2.2.2
                                      linarith only [h0, h6253, h8081, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p8130_1]
                                    · have p8130_0 := h8130c.1
                                      have p8130_1 := h8130c.2.1
                                      have p8130_2 := h8130c.2.2.1
                                      have p8130_3 := h8130c.2.2.2
                                      linarith only [h0, h7338, h8081, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p8130_1]
                                    · have p8130_0 := h8130c.1
                                      have p8130_1 := h8130c.2.1
                                      have p8130_2 := h8130c.2.2.1
                                      have p8130_3 := h8130c.2.2.2
                                      linarith only [h0, h8084, h8096, h8097, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8130_1]
                                    · have p8130_0 := h8130c.1
                                      have p8130_1 := h8130c.2.1
                                      have p8130_2 := h8130c.2.2.1
                                      have p8130_3 := h8130c.2.2.2
                                      linarith only [h8081, h8084, h8096, h8097, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p8130_1]
                                    · have p8130_0 := h8130c.1
                                      have p8130_1 := h8130c.2.1
                                      have p8130_2 := h8130c.2.2.1
                                      have p8130_3 := h8130c.2.2.2
                                      linarith only [h8082, hlam, p8130_1]
                                    · have p8130_0 := h8130c.1
                                      have p8130_1 := h8130c.2.1
                                      have p8130_2 := h8130c.2.2.1
                                      have p8130_3 := h8130c.2.2.2
                                      linarith only [hlam, p8130_0]
                                    · have p8130_0 := h8130c.1
                                      have p8130_1 := h8130c.2.1
                                      have p8130_2 := h8130c.2.2.1
                                      have p8130_3 := h8130c.2.2.2
                                      linarith only [h6253, h7338, h8081, h8084, h8088, h8096, h8097, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8130_1]
                                    · have p8130_0 := h8130c.1
                                      have p8130_1 := h8130c.2.1
                                      have p8130_2 := h8130c.2.2.1
                                      have p8130_3 := h8130c.2.2.2
                                      linarith only [h6253, h8084, h8088, h8096, h8097, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8130_1]
                                    · have p8130_0 := h8130c.1
                                      have p8130_1 := h8130c.2.1
                                      have p8130_2 := h8130c.2.2.1
                                      have p8130_3 := h8130c.2.2.2
                                      linarith only [h8081, h8084, h8096, h8097, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p8130_1]
                                    · have p8130_0 := h8130c.1
                                      have p8130_1 := h8130c.2.1
                                      have p8130_2 := h8130c.2.2.1
                                      have p8130_3 := h8130c.2.2.2
                                      linarith only [h8083, hlam, p8130_0]
                                    · have p8130_0 := h8130c.1
                                      have p8130_1 := h8130c.2.1
                                      have p8130_2 := h8130c.2.2.1
                                      have p8130_3 := h8130c.2.2.2
                                      linarith only [h8085, hlam, p8130_0]
                                    · have p8130_0 := h8130c.1
                                      have p8130_1 := h8130c.2.1
                                      have p8130_2 := h8130c.2.2.1
                                      have p8130_3 := h8130c.2.2.2
                                      linarith only [hlam, p8130_0]
                                    · have p8130_0 := h8130c.1
                                      have p8130_1 := h8130c.2.1
                                      have p8130_2 := h8130c.2.2.1
                                      have p8130_3 := h8130c.2.2.2
                                      linarith only [h7338, h8084, h8088, h8091, h8096, h8097, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8130_1]
                                    · have p8130_0 := h8130c.1
                                      have p8130_1 := h8130c.2.1
                                      have p8130_2 := h8130c.2.2.1
                                      have p8130_3 := h8130c.2.2.2
                                      linarith only [h8081, hlam, p8130_0]
                                    · have p8130_0 := h8130c.1
                                      have p8130_1 := h8130c.2.1
                                      have p8130_2 := h8130c.2.2.1
                                      have p8130_3 := h8130c.2.2.2
                                      linarith only [h8084, hlam, p8130_1]
                                    · have p8130_0 := h8130c.1
                                      have p8130_1 := h8130c.2.1
                                      have p8130_2 := h8130c.2.2.1
                                      have p8130_3 := h8130c.2.2.2
                                      linarith only [h8086, hlam, p8130_0]
                                    · have p8130_0 := h8130c.1
                                      have p8130_1 := h8130c.2.1
                                      have p8130_2 := h8130c.2.2.1
                                      have p8130_3 := h8130c.2.2.2
                                      linarith only [h8087, hlam, p8130_1]
                                    · have p8130_0 := h8130c.1
                                      have p8130_1 := h8130c.2.1
                                      have p8130_2 := h8130c.2.2.1
                                      have p8130_3 := h8130c.2.2.2
                                      linarith only [hlam, p8130_0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8156 | h8156
                                  · linarith only [h0, h8082, h8094, h8096, h8156, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · rcases h0bigk with h8158c | h8158c | h8158c | h8158c | h8158c | h8158c | h8158c | h8158c | h8158c | h8158c | h8158c | h8158c | h8158c | h8158c | h8158c | h8158c | h8158c | h8158c | h8158c | h8158c | h8158c | h8158c | h8158c | h8158c | h8158c
                                    · have p8158_0 := h8158c.1
                                      have p8158_1 := h8158c.2.1
                                      have p8158_2 := h8158c.2.2.1
                                      have p8158_3 := h8158c.2.2.2
                                      linarith only [hlam, p8158_0]
                                    · have p8158_0 := h8158c.1
                                      have p8158_1 := h8158c.2.1
                                      have p8158_2 := h8158c.2.2.1
                                      have p8158_3 := h8158c.2.2.2
                                      linarith only [h0, hlam, p8158_1]
                                    · have p8158_0 := h8158c.1
                                      have p8158_1 := h8158c.2.1
                                      have p8158_2 := h8158c.2.2.1
                                      have p8158_3 := h8158c.2.2.2
                                      linarith only [h6253, hlam, p8158_0]
                                    · have p8158_0 := h8158c.1
                                      have p8158_1 := h8158c.2.1
                                      have p8158_2 := h8158c.2.2.1
                                      have p8158_3 := h8158c.2.2.2
                                      linarith only [h7338, hlam, p8158_1]
                                    · have p8158_0 := h8158c.1
                                      have p8158_1 := h8158c.2.1
                                      have p8158_2 := h8158c.2.2.1
                                      have p8158_3 := h8158c.2.2.2
                                      linarith only [h7338, h8088, h8091, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p8158_1]
                                    · have p8158_0 := h8158c.1
                                      have p8158_1 := h8158c.2.1
                                      have p8158_2 := h8158c.2.2.1
                                      have p8158_3 := h8158c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p8158_1]
                                    · have p8158_0 := h8158c.1
                                      have p8158_1 := h8158c.2.1
                                      have p8158_2 := h8158c.2.2.1
                                      have p8158_3 := h8158c.2.2.2
                                      linarith only [hlam, p8158_0]
                                    · have p8158_0 := h8158c.1
                                      have p8158_1 := h8158c.2.1
                                      have p8158_2 := h8158c.2.2.1
                                      have p8158_3 := h8158c.2.2.2
                                      linarith only [h0, h6253, h8081, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p8158_1]
                                    · have p8158_0 := h8158c.1
                                      have p8158_1 := h8158c.2.1
                                      have p8158_2 := h8158c.2.2.1
                                      have p8158_3 := h8158c.2.2.2
                                      linarith only [h0, h7338, h8081, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p8158_1]
                                    · have p8158_0 := h8158c.1
                                      have p8158_1 := h8158c.2.1
                                      have p8158_2 := h8158c.2.2.1
                                      have p8158_3 := h8158c.2.2.2
                                      linarith only [h0, h8081, h8093, h8094, h8096, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8158_1]
                                    · have p8158_0 := h8158c.1
                                      have p8158_1 := h8158c.2.1
                                      have p8158_2 := h8158c.2.2.1
                                      have p8158_3 := h8158c.2.2.2
                                      linarith only [h8081, h8093, h8094, h8096, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p8158_1]
                                    · have p8158_0 := h8158c.1
                                      have p8158_1 := h8158c.2.1
                                      have p8158_2 := h8158c.2.2.1
                                      have p8158_3 := h8158c.2.2.2
                                      linarith only [h8082, hlam, p8158_1]
                                    · have p8158_0 := h8158c.1
                                      have p8158_1 := h8158c.2.1
                                      have p8158_2 := h8158c.2.2.1
                                      have p8158_3 := h8158c.2.2.2
                                      linarith only [hlam, p8158_0]
                                    · have p8158_0 := h8158c.1
                                      have p8158_1 := h8158c.2.1
                                      have p8158_2 := h8158c.2.2.1
                                      have p8158_3 := h8158c.2.2.2
                                      linarith only [h6253, h7338, h8081, h8088, h8093, h8094, h8096, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8158_1]
                                    · have p8158_0 := h8158c.1
                                      have p8158_1 := h8158c.2.1
                                      have p8158_2 := h8158c.2.2.1
                                      have p8158_3 := h8158c.2.2.2
                                      linarith only [h6253, h8081, h8088, h8093, h8094, h8096, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8158_1]
                                    · have p8158_0 := h8158c.1
                                      have p8158_1 := h8158c.2.1
                                      have p8158_2 := h8158c.2.2.1
                                      have p8158_3 := h8158c.2.2.2
                                      linarith only [h8081, h8093, h8094, h8096, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p8158_1]
                                    · have p8158_0 := h8158c.1
                                      have p8158_1 := h8158c.2.1
                                      have p8158_2 := h8158c.2.2.1
                                      have p8158_3 := h8158c.2.2.2
                                      linarith only [h8083, hlam, p8158_0]
                                    · have p8158_0 := h8158c.1
                                      have p8158_1 := h8158c.2.1
                                      have p8158_2 := h8158c.2.2.1
                                      have p8158_3 := h8158c.2.2.2
                                      linarith only [h8085, hlam, p8158_0]
                                    · have p8158_0 := h8158c.1
                                      have p8158_1 := h8158c.2.1
                                      have p8158_2 := h8158c.2.2.1
                                      have p8158_3 := h8158c.2.2.2
                                      linarith only [hlam, p8158_0]
                                    · have p8158_0 := h8158c.1
                                      have p8158_1 := h8158c.2.1
                                      have p8158_2 := h8158c.2.2.1
                                      have p8158_3 := h8158c.2.2.2
                                      linarith only [h7338, h8081, h8088, h8091, h8093, h8094, h8096, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8158_1]
                                    · have p8158_0 := h8158c.1
                                      have p8158_1 := h8158c.2.1
                                      have p8158_2 := h8158c.2.2.1
                                      have p8158_3 := h8158c.2.2.2
                                      linarith only [h8081, hlam, p8158_0]
                                    · have p8158_0 := h8158c.1
                                      have p8158_1 := h8158c.2.1
                                      have p8158_2 := h8158c.2.2.1
                                      have p8158_3 := h8158c.2.2.2
                                      linarith only [h8084, hlam, p8158_1]
                                    · have p8158_0 := h8158c.1
                                      have p8158_1 := h8158c.2.1
                                      have p8158_2 := h8158c.2.2.1
                                      have p8158_3 := h8158c.2.2.2
                                      linarith only [h8086, hlam, p8158_0]
                                    · have p8158_0 := h8158c.1
                                      have p8158_1 := h8158c.2.1
                                      have p8158_2 := h8158c.2.2.1
                                      have p8158_3 := h8158c.2.2.2
                                      linarith only [h8087, hlam, p8158_1]
                                    · have p8158_0 := h8158c.1
                                      have p8158_1 := h8158c.2.1
                                      have p8158_2 := h8158c.2.2.1
                                      have p8158_3 := h8158c.2.2.2
                                      linarith only [hlam, p8158_0]
                              · linarith only [h7338, h8081, h8088, h8091, h8092, h8094, h8095, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8185 | h8185
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8186 | h8186
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8187 | h8187
                                  · rcases h0bigk with h8188c | h8188c | h8188c | h8188c | h8188c | h8188c | h8188c | h8188c | h8188c | h8188c | h8188c | h8188c | h8188c | h8188c | h8188c | h8188c | h8188c | h8188c | h8188c | h8188c | h8188c | h8188c | h8188c | h8188c | h8188c
                                    · have p8188_0 := h8188c.1
                                      have p8188_1 := h8188c.2.1
                                      have p8188_2 := h8188c.2.2.1
                                      have p8188_3 := h8188c.2.2.2
                                      linarith only [hlam, p8188_0]
                                    · have p8188_0 := h8188c.1
                                      have p8188_1 := h8188c.2.1
                                      have p8188_2 := h8188c.2.2.1
                                      have p8188_3 := h8188c.2.2.2
                                      linarith only [h0, hlam, p8188_1]
                                    · have p8188_0 := h8188c.1
                                      have p8188_1 := h8188c.2.1
                                      have p8188_2 := h8188c.2.2.1
                                      have p8188_3 := h8188c.2.2.2
                                      linarith only [h6253, hlam, p8188_0]
                                    · have p8188_0 := h8188c.1
                                      have p8188_1 := h8188c.2.1
                                      have p8188_2 := h8188c.2.2.1
                                      have p8188_3 := h8188c.2.2.2
                                      linarith only [h7338, hlam, p8188_1]
                                    · have p8188_0 := h8188c.1
                                      have p8188_1 := h8188c.2.1
                                      have p8188_2 := h8188c.2.2.1
                                      have p8188_3 := h8188c.2.2.2
                                      linarith only [h7338, h8088, h8091, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p8188_1]
                                    · have p8188_0 := h8188c.1
                                      have p8188_1 := h8188c.2.1
                                      have p8188_2 := h8188c.2.2.1
                                      have p8188_3 := h8188c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p8188_1]
                                    · have p8188_0 := h8188c.1
                                      have p8188_1 := h8188c.2.1
                                      have p8188_2 := h8188c.2.2.1
                                      have p8188_3 := h8188c.2.2.2
                                      linarith only [hlam, p8188_0]
                                    · have p8188_0 := h8188c.1
                                      have p8188_1 := h8188c.2.1
                                      have p8188_2 := h8188c.2.2.1
                                      have p8188_3 := h8188c.2.2.2
                                      linarith only [h0, h6253, h8081, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p8188_1]
                                    · have p8188_0 := h8188c.1
                                      have p8188_1 := h8188c.2.1
                                      have p8188_2 := h8188c.2.2.1
                                      have p8188_3 := h8188c.2.2.2
                                      linarith only [h0, h7338, h8081, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p8188_1]
                                    · have p8188_0 := h8188c.1
                                      have p8188_1 := h8188c.2.1
                                      have p8188_2 := h8188c.2.2.1
                                      have p8188_3 := h8188c.2.2.2
                                      rcases p8188_3 (m.d 0 1) (by simp) with h8198 | h8198
                                      · linarith only [h0, h8198, hlam]
                                      · linarith only [h8081, h8198, hlam]
                                    · have p8188_0 := h8188c.1
                                      have p8188_1 := h8188c.2.1
                                      have p8188_2 := h8188c.2.2.1
                                      have p8188_3 := h8188c.2.2.2
                                      linarith only [h8081, h8090, h8185, h8187, hc03, hc45, hlam, hphi, ht0b, ht5b, p8188_1]
                                    · have p8188_0 := h8188c.1
                                      have p8188_1 := h8188c.2.1
                                      have p8188_2 := h8188c.2.2.1
                                      have p8188_3 := h8188c.2.2.2
                                      linarith only [h8082, hlam, p8188_1]
                                    · have p8188_0 := h8188c.1
                                      have p8188_1 := h8188c.2.1
                                      have p8188_2 := h8188c.2.2.1
                                      have p8188_3 := h8188c.2.2.2
                                      linarith only [hlam, p8188_0]
                                    · have p8188_0 := h8188c.1
                                      have p8188_1 := h8188c.2.1
                                      have p8188_2 := h8188c.2.2.1
                                      have p8188_3 := h8188c.2.2.2
                                      linarith only [h6253, h8085, h8088, h8094, h8185, h8187, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8188_1]
                                    · have p8188_0 := h8188c.1
                                      have p8188_1 := h8188c.2.1
                                      have p8188_2 := h8188c.2.2.1
                                      have p8188_3 := h8188c.2.2.2
                                      rcases p8188_3 (m.d 0 1) (by simp) with h8205 | h8205
                                      · linarith only [h6253, h8205, hlam]
                                      · linarith only [h8081, h8205, hlam]
                                    · have p8188_0 := h8188c.1
                                      have p8188_1 := h8188c.2.1
                                      have p8188_2 := h8188c.2.2.1
                                      have p8188_3 := h8188c.2.2.2
                                      linarith only [h8081, h8090, h8185, h8187, hc04, hc45, hlam, hphi, ht0b, ht5b, p8188_1]
                                    · have p8188_0 := h8188c.1
                                      have p8188_1 := h8188c.2.1
                                      have p8188_2 := h8188c.2.2.1
                                      have p8188_3 := h8188c.2.2.2
                                      linarith only [h8083, hlam, p8188_0]
                                    · have p8188_0 := h8188c.1
                                      have p8188_1 := h8188c.2.1
                                      have p8188_2 := h8188c.2.2.1
                                      have p8188_3 := h8188c.2.2.2
                                      linarith only [h8085, hlam, p8188_0]
                                    · have p8188_0 := h8188c.1
                                      have p8188_1 := h8188c.2.1
                                      have p8188_2 := h8188c.2.2.1
                                      have p8188_3 := h8188c.2.2.2
                                      linarith only [hlam, p8188_0]
                                    · have p8188_0 := h8188c.1
                                      have p8188_1 := h8188c.2.1
                                      have p8188_2 := h8188c.2.2.1
                                      have p8188_3 := h8188c.2.2.2
                                      rcases p8188_3 (m.d 0 1) (by simp) with h8212 | h8212
                                      · linarith only [h7338, h8212, hlam]
                                      · linarith only [h8081, h8212, hlam]
                                    · have p8188_0 := h8188c.1
                                      have p8188_1 := h8188c.2.1
                                      have p8188_2 := h8188c.2.2.1
                                      have p8188_3 := h8188c.2.2.2
                                      linarith only [h8081, hlam, p8188_0]
                                    · have p8188_0 := h8188c.1
                                      have p8188_1 := h8188c.2.1
                                      have p8188_2 := h8188c.2.2.1
                                      have p8188_3 := h8188c.2.2.2
                                      linarith only [h8084, hlam, p8188_1]
                                    · have p8188_0 := h8188c.1
                                      have p8188_1 := h8188c.2.1
                                      have p8188_2 := h8188c.2.2.1
                                      have p8188_3 := h8188c.2.2.2
                                      linarith only [h8086, hlam, p8188_0]
                                    · have p8188_0 := h8188c.1
                                      have p8188_1 := h8188c.2.1
                                      have p8188_2 := h8188c.2.2.1
                                      have p8188_3 := h8188c.2.2.2
                                      linarith only [h8087, hlam, p8188_1]
                                    · have p8188_0 := h8188c.1
                                      have p8188_1 := h8188c.2.1
                                      have p8188_2 := h8188c.2.2.1
                                      have p8188_3 := h8188c.2.2.2
                                      linarith only [hlam, p8188_0]
                                  · linarith only [h7338, h8087, h8088, h8091, h8094, h8185, h8187, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h7338, h8081, h8088, h8091, h8093, h8094, h8185, h8186, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8222 | h8222
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8223 | h8223
                                  · rcases h0bigk with h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c | h8224c
                                    · have p8224_0 := h8224c.1
                                      have p8224_1 := h8224c.2.1
                                      have p8224_2 := h8224c.2.2.1
                                      have p8224_3 := h8224c.2.2.2
                                      linarith only [hlam, p8224_0]
                                    · have p8224_0 := h8224c.1
                                      have p8224_1 := h8224c.2.1
                                      have p8224_2 := h8224c.2.2.1
                                      have p8224_3 := h8224c.2.2.2
                                      linarith only [h0, hlam, p8224_1]
                                    · have p8224_0 := h8224c.1
                                      have p8224_1 := h8224c.2.1
                                      have p8224_2 := h8224c.2.2.1
                                      have p8224_3 := h8224c.2.2.2
                                      linarith only [h6253, hlam, p8224_0]
                                    · have p8224_0 := h8224c.1
                                      have p8224_1 := h8224c.2.1
                                      have p8224_2 := h8224c.2.2.1
                                      have p8224_3 := h8224c.2.2.2
                                      linarith only [h7338, hlam, p8224_1]
                                    · have p8224_0 := h8224c.1
                                      have p8224_1 := h8224c.2.1
                                      have p8224_2 := h8224c.2.2.1
                                      have p8224_3 := h8224c.2.2.2
                                      linarith only [h7338, h8088, h8091, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p8224_1]
                                    · have p8224_0 := h8224c.1
                                      have p8224_1 := h8224c.2.1
                                      have p8224_2 := h8224c.2.2.1
                                      have p8224_3 := h8224c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p8224_1]
                                    · have p8224_0 := h8224c.1
                                      have p8224_1 := h8224c.2.1
                                      have p8224_2 := h8224c.2.2.1
                                      have p8224_3 := h8224c.2.2.2
                                      linarith only [hlam, p8224_0]
                                    · have p8224_0 := h8224c.1
                                      have p8224_1 := h8224c.2.1
                                      have p8224_2 := h8224c.2.2.1
                                      have p8224_3 := h8224c.2.2.2
                                      linarith only [h0, h6253, h8081, h8092, h8185, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8224_1]
                                    · have p8224_0 := h8224c.1
                                      have p8224_1 := h8224c.2.1
                                      have p8224_2 := h8224c.2.2.1
                                      have p8224_3 := h8224c.2.2.2
                                      linarith only [h0, h7338, h8081, h8092, h8185, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8224_1]
                                    · have p8224_0 := h8224c.1
                                      have p8224_1 := h8224c.2.1
                                      have p8224_2 := h8224c.2.2.1
                                      have p8224_3 := h8224c.2.2.2
                                      linarith only [h0, h8081, h8092, h8185, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8224_1]
                                    · have p8224_0 := h8224c.1
                                      have p8224_1 := h8224c.2.1
                                      have p8224_2 := h8224c.2.2.1
                                      have p8224_3 := h8224c.2.2.2
                                      linarith only [h8081, h8092, h8185, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8224_1]
                                    · have p8224_0 := h8224c.1
                                      have p8224_1 := h8224c.2.1
                                      have p8224_2 := h8224c.2.2.1
                                      have p8224_3 := h8224c.2.2.2
                                      linarith only [h8082, hlam, p8224_1]
                                    · have p8224_0 := h8224c.1
                                      have p8224_1 := h8224c.2.1
                                      have p8224_2 := h8224c.2.2.1
                                      have p8224_3 := h8224c.2.2.2
                                      linarith only [hlam, p8224_0]
                                    · have p8224_0 := h8224c.1
                                      have p8224_1 := h8224c.2.1
                                      have p8224_2 := h8224c.2.2.1
                                      have p8224_3 := h8224c.2.2.2
                                      linarith only [h6253, h7338, h8081, h8088, h8092, h8185, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8224_1]
                                    · have p8224_0 := h8224c.1
                                      have p8224_1 := h8224c.2.1
                                      have p8224_2 := h8224c.2.2.1
                                      have p8224_3 := h8224c.2.2.2
                                      linarith only [h6253, h8081, h8088, h8092, h8185, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8224_1]
                                    · have p8224_0 := h8224c.1
                                      have p8224_1 := h8224c.2.1
                                      have p8224_2 := h8224c.2.2.1
                                      have p8224_3 := h8224c.2.2.2
                                      linarith only [h8081, h8092, h8185, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8224_1]
                                    · have p8224_0 := h8224c.1
                                      have p8224_1 := h8224c.2.1
                                      have p8224_2 := h8224c.2.2.1
                                      have p8224_3 := h8224c.2.2.2
                                      linarith only [h8083, hlam, p8224_0]
                                    · have p8224_0 := h8224c.1
                                      have p8224_1 := h8224c.2.1
                                      have p8224_2 := h8224c.2.2.1
                                      have p8224_3 := h8224c.2.2.2
                                      linarith only [h8085, hlam, p8224_0]
                                    · have p8224_0 := h8224c.1
                                      have p8224_1 := h8224c.2.1
                                      have p8224_2 := h8224c.2.2.1
                                      have p8224_3 := h8224c.2.2.2
                                      linarith only [hlam, p8224_0]
                                    · have p8224_0 := h8224c.1
                                      have p8224_1 := h8224c.2.1
                                      have p8224_2 := h8224c.2.2.1
                                      have p8224_3 := h8224c.2.2.2
                                      linarith only [h7338, h8081, h8088, h8091, h8092, h8185, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8224_1]
                                    · have p8224_0 := h8224c.1
                                      have p8224_1 := h8224c.2.1
                                      have p8224_2 := h8224c.2.2.1
                                      have p8224_3 := h8224c.2.2.2
                                      linarith only [h8081, hlam, p8224_0]
                                    · have p8224_0 := h8224c.1
                                      have p8224_1 := h8224c.2.1
                                      have p8224_2 := h8224c.2.2.1
                                      have p8224_3 := h8224c.2.2.2
                                      linarith only [h8084, hlam, p8224_1]
                                    · have p8224_0 := h8224c.1
                                      have p8224_1 := h8224c.2.1
                                      have p8224_2 := h8224c.2.2.1
                                      have p8224_3 := h8224c.2.2.2
                                      linarith only [h8086, hlam, p8224_0]
                                    · have p8224_0 := h8224c.1
                                      have p8224_1 := h8224c.2.1
                                      have p8224_2 := h8224c.2.2.1
                                      have p8224_3 := h8224c.2.2.2
                                      linarith only [h8087, hlam, p8224_1]
                                    · have p8224_0 := h8224c.1
                                      have p8224_1 := h8224c.2.1
                                      have p8224_2 := h8224c.2.2.1
                                      have p8224_3 := h8224c.2.2.2
                                      linarith only [hlam, p8224_0]
                                  · linarith only [h0, h8083, h8094, h8222, h8223, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8251 | h8251
                                  · rcases h0bigk with h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c | h8252c
                                    · have p8252_0 := h8252c.1
                                      have p8252_1 := h8252c.2.1
                                      have p8252_2 := h8252c.2.2.1
                                      have p8252_3 := h8252c.2.2.2
                                      linarith only [hlam, p8252_0]
                                    · have p8252_0 := h8252c.1
                                      have p8252_1 := h8252c.2.1
                                      have p8252_2 := h8252c.2.2.1
                                      have p8252_3 := h8252c.2.2.2
                                      linarith only [h0, hlam, p8252_1]
                                    · have p8252_0 := h8252c.1
                                      have p8252_1 := h8252c.2.1
                                      have p8252_2 := h8252c.2.2.1
                                      have p8252_3 := h8252c.2.2.2
                                      linarith only [h6253, hlam, p8252_0]
                                    · have p8252_0 := h8252c.1
                                      have p8252_1 := h8252c.2.1
                                      have p8252_2 := h8252c.2.2.1
                                      have p8252_3 := h8252c.2.2.2
                                      linarith only [h7338, hlam, p8252_1]
                                    · have p8252_0 := h8252c.1
                                      have p8252_1 := h8252c.2.1
                                      have p8252_2 := h8252c.2.2.1
                                      have p8252_3 := h8252c.2.2.2
                                      linarith only [h8081, h8092, h8094, h8222, h8251, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8252_1]
                                    · have p8252_0 := h8252c.1
                                      have p8252_1 := h8252c.2.1
                                      have p8252_2 := h8252c.2.2.1
                                      have p8252_3 := h8252c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p8252_1]
                                    · have p8252_0 := h8252c.1
                                      have p8252_1 := h8252c.2.1
                                      have p8252_2 := h8252c.2.2.1
                                      have p8252_3 := h8252c.2.2.2
                                      linarith only [hlam, p8252_0]
                                    · have p8252_0 := h8252c.1
                                      have p8252_1 := h8252c.2.1
                                      have p8252_2 := h8252c.2.2.1
                                      have p8252_3 := h8252c.2.2.2
                                      linarith only [h0, h8085, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8252_1]
                                    · have p8252_0 := h8252c.1
                                      have p8252_1 := h8252c.2.1
                                      have p8252_2 := h8252c.2.2.1
                                      have p8252_3 := h8252c.2.2.2
                                      linarith only [h0, h7338, h8081, h8092, h8094, h8222, h8251, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8252_1]
                                    · have p8252_0 := h8252c.1
                                      have p8252_1 := h8252c.2.1
                                      have p8252_2 := h8252c.2.2.1
                                      have p8252_3 := h8252c.2.2.2
                                      linarith only [h0, h8081, h8092, h8094, h8222, h8251, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8252_1]
                                    · have p8252_0 := h8252c.1
                                      have p8252_1 := h8252c.2.1
                                      have p8252_2 := h8252c.2.2.1
                                      have p8252_3 := h8252c.2.2.2
                                      linarith only [h8081, h8092, h8094, h8222, h8251, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8252_1]
                                    · have p8252_0 := h8252c.1
                                      have p8252_1 := h8252c.2.1
                                      have p8252_2 := h8252c.2.2.1
                                      have p8252_3 := h8252c.2.2.2
                                      linarith only [h8082, hlam, p8252_1]
                                    · have p8252_0 := h8252c.1
                                      have p8252_1 := h8252c.2.1
                                      have p8252_2 := h8252c.2.2.1
                                      have p8252_3 := h8252c.2.2.2
                                      linarith only [hlam, p8252_0]
                                    · have p8252_0 := h8252c.1
                                      have p8252_1 := h8252c.2.1
                                      have p8252_2 := h8252c.2.2.1
                                      have p8252_3 := h8252c.2.2.2
                                      linarith only [h6253, h7338, h8081, h8088, h8092, h8094, h8222, h8251, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8252_1]
                                    · have p8252_0 := h8252c.1
                                      have p8252_1 := h8252c.2.1
                                      have p8252_2 := h8252c.2.2.1
                                      have p8252_3 := h8252c.2.2.2
                                      linarith only [h6253, h8081, h8088, h8092, h8094, h8222, h8251, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8252_1]
                                    · have p8252_0 := h8252c.1
                                      have p8252_1 := h8252c.2.1
                                      have p8252_2 := h8252c.2.2.1
                                      have p8252_3 := h8252c.2.2.2
                                      linarith only [h8081, h8092, h8094, h8222, h8251, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8252_1]
                                    · have p8252_0 := h8252c.1
                                      have p8252_1 := h8252c.2.1
                                      have p8252_2 := h8252c.2.2.1
                                      have p8252_3 := h8252c.2.2.2
                                      linarith only [h8083, hlam, p8252_0]
                                    · have p8252_0 := h8252c.1
                                      have p8252_1 := h8252c.2.1
                                      have p8252_2 := h8252c.2.2.1
                                      have p8252_3 := h8252c.2.2.2
                                      linarith only [h8085, hlam, p8252_0]
                                    · have p8252_0 := h8252c.1
                                      have p8252_1 := h8252c.2.1
                                      have p8252_2 := h8252c.2.2.1
                                      have p8252_3 := h8252c.2.2.2
                                      linarith only [hlam, p8252_0]
                                    · have p8252_0 := h8252c.1
                                      have p8252_1 := h8252c.2.1
                                      have p8252_2 := h8252c.2.2.1
                                      have p8252_3 := h8252c.2.2.2
                                      linarith only [h7338, h8081, h8088, h8091, h8092, h8094, h8222, h8251, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8252_1]
                                    · have p8252_0 := h8252c.1
                                      have p8252_1 := h8252c.2.1
                                      have p8252_2 := h8252c.2.2.1
                                      have p8252_3 := h8252c.2.2.2
                                      linarith only [h8081, hlam, p8252_0]
                                    · have p8252_0 := h8252c.1
                                      have p8252_1 := h8252c.2.1
                                      have p8252_2 := h8252c.2.2.1
                                      have p8252_3 := h8252c.2.2.2
                                      linarith only [h8084, hlam, p8252_1]
                                    · have p8252_0 := h8252c.1
                                      have p8252_1 := h8252c.2.1
                                      have p8252_2 := h8252c.2.2.1
                                      have p8252_3 := h8252c.2.2.2
                                      linarith only [h8086, hlam, p8252_0]
                                    · have p8252_0 := h8252c.1
                                      have p8252_1 := h8252c.2.1
                                      have p8252_2 := h8252c.2.2.1
                                      have p8252_3 := h8252c.2.2.2
                                      linarith only [h8087, hlam, p8252_1]
                                    · have p8252_0 := h8252c.1
                                      have p8252_1 := h8252c.2.1
                                      have p8252_2 := h8252c.2.2.1
                                      have p8252_3 := h8252c.2.2.2
                                      linarith only [hlam, p8252_0]
                                  · linarith only [h0, h8081, h8093, h8094, h8251, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h7338, h8087, h8093, hlam]
                        · linarith only [h6253, h8086, h8092, hlam]
                      · linarith only [h6253, h8085, h8091, hlam]
                    · linarith only [h0, h8084, h8090, hlam]
                  · linarith only [h0, h8083, h8089, hlam]
                · linarith only [h0, h8082, h8088, hlam]
              · linarith only [h7338, h8081, h8087, hlam]
            · linarith only [h6253, h8081, h8086, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h8287 | h8287
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8288 | h8288
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8289 | h8289
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8290 | h8290
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8291 | h8291
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8292 | h8292
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8293 | h8293
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8294 | h8294
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8295 | h8295
                            · linarith only [h6253, h8081, h8082, h8085, h8295, hc02, hc15, hlam, hphi, ht0b, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8297 | h8297
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8298 | h8298
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8299 | h8299
                                  · rcases h0bigk with h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c | h8300c
                                    · have p8300_0 := h8300c.1
                                      have p8300_1 := h8300c.2.1
                                      have p8300_2 := h8300c.2.2.1
                                      have p8300_3 := h8300c.2.2.2
                                      linarith only [hlam, p8300_0]
                                    · have p8300_0 := h8300c.1
                                      have p8300_1 := h8300c.2.1
                                      have p8300_2 := h8300c.2.2.1
                                      have p8300_3 := h8300c.2.2.2
                                      linarith only [h0, hlam, p8300_1]
                                    · have p8300_0 := h8300c.1
                                      have p8300_1 := h8300c.2.1
                                      have p8300_2 := h8300c.2.2.1
                                      have p8300_3 := h8300c.2.2.2
                                      linarith only [h6253, hlam, p8300_0]
                                    · have p8300_0 := h8300c.1
                                      have p8300_1 := h8300c.2.1
                                      have p8300_2 := h8300c.2.2.1
                                      have p8300_3 := h8300c.2.2.2
                                      linarith only [h7338, hlam, p8300_1]
                                    · have p8300_0 := h8300c.1
                                      have p8300_1 := h8300c.2.1
                                      have p8300_2 := h8300c.2.2.1
                                      have p8300_3 := h8300c.2.2.2
                                      linarith only [h6253, h8085, h8292, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p8300_1]
                                    · have p8300_0 := h8300c.1
                                      have p8300_1 := h8300c.2.1
                                      have p8300_2 := h8300c.2.2.1
                                      have p8300_3 := h8300c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p8300_1]
                                    · have p8300_0 := h8300c.1
                                      have p8300_1 := h8300c.2.1
                                      have p8300_2 := h8300c.2.2.1
                                      have p8300_3 := h8300c.2.2.2
                                      linarith only [hlam, p8300_0]
                                    · have p8300_0 := h8300c.1
                                      have p8300_1 := h8300c.2.1
                                      have p8300_2 := h8300c.2.2.1
                                      have p8300_3 := h8300c.2.2.2
                                      linarith only [h0, h6253, h8081, h8291, h8297, h8299, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8300_1]
                                    · have p8300_0 := h8300c.1
                                      have p8300_1 := h8300c.2.1
                                      have p8300_2 := h8300c.2.2.1
                                      have p8300_3 := h8300c.2.2.2
                                      linarith only [h0, h6253, h8081, h8085, h8291, h8297, h8299, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8300_1]
                                    · have p8300_0 := h8300c.1
                                      have p8300_1 := h8300c.2.1
                                      have p8300_2 := h8300c.2.2.1
                                      have p8300_3 := h8300c.2.2.2
                                      rcases p8300_3 (m.d 0 1) (by simp) with h8310 | h8310
                                      · linarith only [h0, h8310, hlam]
                                      · linarith only [h8081, h8310, hlam]
                                    · have p8300_0 := h8300c.1
                                      have p8300_1 := h8300c.2.1
                                      have p8300_2 := h8300c.2.2.1
                                      have p8300_3 := h8300c.2.2.2
                                      linarith only [h8081, h8291, h8297, h8299, hc03, hc45, hlam, hphi, ht0b, ht5b, p8300_1]
                                    · have p8300_0 := h8300c.1
                                      have p8300_1 := h8300c.2.1
                                      have p8300_2 := h8300c.2.2.1
                                      have p8300_3 := h8300c.2.2.2
                                      linarith only [h8082, hlam, p8300_1]
                                    · have p8300_0 := h8300c.1
                                      have p8300_1 := h8300c.2.1
                                      have p8300_2 := h8300c.2.2.1
                                      have p8300_3 := h8300c.2.2.2
                                      linarith only [hlam, p8300_0]
                                    · have p8300_0 := h8300c.1
                                      have p8300_1 := h8300c.2.1
                                      have p8300_2 := h8300c.2.2.1
                                      have p8300_3 := h8300c.2.2.2
                                      linarith only [h8085, hlam, p8300_1]
                                    · have p8300_0 := h8300c.1
                                      have p8300_1 := h8300c.2.1
                                      have p8300_2 := h8300c.2.2.1
                                      have p8300_3 := h8300c.2.2.2
                                      linarith only [h8081, h8085, h8289, h8291, h8292, h8297, h8299, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8300_1]
                                    · have p8300_0 := h8300c.1
                                      have p8300_1 := h8300c.2.1
                                      have p8300_2 := h8300c.2.2.1
                                      have p8300_3 := h8300c.2.2.2
                                      linarith only [h8081, h8085, h8289, h8291, h8292, h8297, h8299, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8300_1]
                                    · have p8300_0 := h8300c.1
                                      have p8300_1 := h8300c.2.1
                                      have p8300_2 := h8300c.2.2.1
                                      have p8300_3 := h8300c.2.2.2
                                      linarith only [h8083, hlam, p8300_0]
                                    · have p8300_0 := h8300c.1
                                      have p8300_1 := h8300c.2.1
                                      have p8300_2 := h8300c.2.2.1
                                      have p8300_3 := h8300c.2.2.2
                                      linarith only [h8085, h8289, h8292, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p8300_1]
                                    · have p8300_0 := h8300c.1
                                      have p8300_1 := h8300c.2.1
                                      have p8300_2 := h8300c.2.2.1
                                      have p8300_3 := h8300c.2.2.2
                                      linarith only [hlam, p8300_0]
                                    · have p8300_0 := h8300c.1
                                      have p8300_1 := h8300c.2.1
                                      have p8300_2 := h8300c.2.2.1
                                      have p8300_3 := h8300c.2.2.2
                                      linarith only [h8081, h8085, h8289, h8291, h8292, h8297, h8299, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8300_1]
                                    · have p8300_0 := h8300c.1
                                      have p8300_1 := h8300c.2.1
                                      have p8300_2 := h8300c.2.2.1
                                      have p8300_3 := h8300c.2.2.2
                                      linarith only [h8081, hlam, p8300_0]
                                    · have p8300_0 := h8300c.1
                                      have p8300_1 := h8300c.2.1
                                      have p8300_2 := h8300c.2.2.1
                                      have p8300_3 := h8300c.2.2.2
                                      linarith only [h8084, hlam, p8300_1]
                                    · have p8300_0 := h8300c.1
                                      have p8300_1 := h8300c.2.1
                                      have p8300_2 := h8300c.2.2.1
                                      have p8300_3 := h8300c.2.2.2
                                      linarith only [h8287, hlam, p8300_0]
                                    · have p8300_0 := h8300c.1
                                      have p8300_1 := h8300c.2.1
                                      have p8300_2 := h8300c.2.2.1
                                      have p8300_3 := h8300c.2.2.2
                                      linarith only [h8288, hlam, p8300_1]
                                    · have p8300_0 := h8300c.1
                                      have p8300_1 := h8300c.2.1
                                      have p8300_2 := h8300c.2.2.1
                                      have p8300_3 := h8300c.2.2.2
                                      linarith only [hlam, p8300_0]
                                  · linarith only [h6253, h8081, h8085, h8288, h8291, h8297, h8299, hc04, hc35, hlam, hphi, ht0b, ht5b]
                                · linarith only [h6253, h8081, h8085, h8289, h8292, h8294, h8298, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h8085, h8287, h8289, h8292, h8297, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h7338, h8288, h8294, hlam]
                        · linarith only [h6253, h8085, h8292, h8293, hc01, hc35, hlam, hphi, ht12, ht23]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8333 | h8333
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8334 | h8334
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8335 | h8335
                            · linarith only [h6253, h8081, h8291, h8292, h8335, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8337 | h8337
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8338 | h8338
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8339 | h8339
                                  · rcases h0bigk with h8340c | h8340c | h8340c | h8340c | h8340c | h8340c | h8340c | h8340c | h8340c | h8340c | h8340c | h8340c | h8340c | h8340c | h8340c | h8340c | h8340c | h8340c | h8340c | h8340c | h8340c | h8340c | h8340c | h8340c | h8340c
                                    · have p8340_0 := h8340c.1
                                      have p8340_1 := h8340c.2.1
                                      have p8340_2 := h8340c.2.2.1
                                      have p8340_3 := h8340c.2.2.2
                                      linarith only [hlam, p8340_0]
                                    · have p8340_0 := h8340c.1
                                      have p8340_1 := h8340c.2.1
                                      have p8340_2 := h8340c.2.2.1
                                      have p8340_3 := h8340c.2.2.2
                                      linarith only [h0, hlam, p8340_1]
                                    · have p8340_0 := h8340c.1
                                      have p8340_1 := h8340c.2.1
                                      have p8340_2 := h8340c.2.2.1
                                      have p8340_3 := h8340c.2.2.2
                                      linarith only [h6253, hlam, p8340_0]
                                    · have p8340_0 := h8340c.1
                                      have p8340_1 := h8340c.2.1
                                      have p8340_2 := h8340c.2.2.1
                                      have p8340_3 := h8340c.2.2.2
                                      linarith only [h7338, hlam, p8340_1]
                                    · have p8340_0 := h8340c.1
                                      have p8340_1 := h8340c.2.1
                                      have p8340_2 := h8340c.2.2.1
                                      have p8340_3 := h8340c.2.2.2
                                      linarith only [h6253, h8081, h8291, h8337, h8339, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p8340_1]
                                    · have p8340_0 := h8340c.1
                                      have p8340_1 := h8340c.2.1
                                      have p8340_2 := h8340c.2.2.1
                                      have p8340_3 := h8340c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p8340_1]
                                    · have p8340_0 := h8340c.1
                                      have p8340_1 := h8340c.2.1
                                      have p8340_2 := h8340c.2.2.1
                                      have p8340_3 := h8340c.2.2.2
                                      linarith only [hlam, p8340_0]
                                    · have p8340_0 := h8340c.1
                                      have p8340_1 := h8340c.2.1
                                      have p8340_2 := h8340c.2.2.1
                                      have p8340_3 := h8340c.2.2.2
                                      linarith only [h0, h6253, h8081, h8291, h8337, h8339, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8340_1]
                                    · have p8340_0 := h8340c.1
                                      have p8340_1 := h8340c.2.1
                                      have p8340_2 := h8340c.2.2.1
                                      have p8340_3 := h8340c.2.2.2
                                      linarith only [h0, h7338, h8081, h8291, h8337, h8339, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8340_1]
                                    · have p8340_0 := h8340c.1
                                      have p8340_1 := h8340c.2.1
                                      have p8340_2 := h8340c.2.2.1
                                      have p8340_3 := h8340c.2.2.2
                                      rcases p8340_3 (m.d 0 1) (by simp) with h8350 | h8350
                                      · linarith only [h0, h8350, hlam]
                                      · linarith only [h8081, h8350, hlam]
                                    · have p8340_0 := h8340c.1
                                      have p8340_1 := h8340c.2.1
                                      have p8340_2 := h8340c.2.2.1
                                      have p8340_3 := h8340c.2.2.2
                                      linarith only [h8081, h8291, h8337, h8339, hc03, hc45, hlam, hphi, ht0b, ht5b, p8340_1]
                                    · have p8340_0 := h8340c.1
                                      have p8340_1 := h8340c.2.1
                                      have p8340_2 := h8340c.2.2.1
                                      have p8340_3 := h8340c.2.2.2
                                      linarith only [h8082, hlam, p8340_1]
                                    · have p8340_0 := h8340c.1
                                      have p8340_1 := h8340c.2.1
                                      have p8340_2 := h8340c.2.2.1
                                      have p8340_3 := h8340c.2.2.2
                                      linarith only [hlam, p8340_0]
                                    · have p8340_0 := h8340c.1
                                      have p8340_1 := h8340c.2.1
                                      have p8340_2 := h8340c.2.2.1
                                      have p8340_3 := h8340c.2.2.2
                                      linarith only [h8085, hlam, p8340_1]
                                    · have p8340_0 := h8340c.1
                                      have p8340_1 := h8340c.2.1
                                      have p8340_2 := h8340c.2.2.1
                                      have p8340_3 := h8340c.2.2.2
                                      linarith only [h6253, h8081, h8291, h8292, h8337, h8339, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8340_1]
                                    · have p8340_0 := h8340c.1
                                      have p8340_1 := h8340c.2.1
                                      have p8340_2 := h8340c.2.2.1
                                      have p8340_3 := h8340c.2.2.2
                                      linarith only [h7338, h8081, h8291, h8292, h8337, h8339, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8340_1]
                                    · have p8340_0 := h8340c.1
                                      have p8340_1 := h8340c.2.1
                                      have p8340_2 := h8340c.2.2.1
                                      have p8340_3 := h8340c.2.2.2
                                      linarith only [h8083, hlam, p8340_0]
                                    · have p8340_0 := h8340c.1
                                      have p8340_1 := h8340c.2.1
                                      have p8340_2 := h8340c.2.2.1
                                      have p8340_3 := h8340c.2.2.2
                                      linarith only [h7338, h8292, hc03, hc34, hlam, hphi, p8340_1]
                                    · have p8340_0 := h8340c.1
                                      have p8340_1 := h8340c.2.1
                                      have p8340_2 := h8340c.2.2.1
                                      have p8340_3 := h8340c.2.2.2
                                      linarith only [hlam, p8340_0]
                                    · have p8340_0 := h8340c.1
                                      have p8340_1 := h8340c.2.1
                                      have p8340_2 := h8340c.2.2.1
                                      have p8340_3 := h8340c.2.2.2
                                      rcases p8340_3 (m.d 0 1) (by simp) with h8362 | h8362
                                      · linarith only [h7338, h8362, hlam]
                                      · linarith only [h8081, h8362, hlam]
                                    · have p8340_0 := h8340c.1
                                      have p8340_1 := h8340c.2.1
                                      have p8340_2 := h8340c.2.2.1
                                      have p8340_3 := h8340c.2.2.2
                                      linarith only [h8081, hlam, p8340_0]
                                    · have p8340_0 := h8340c.1
                                      have p8340_1 := h8340c.2.1
                                      have p8340_2 := h8340c.2.2.1
                                      have p8340_3 := h8340c.2.2.2
                                      linarith only [h8084, hlam, p8340_1]
                                    · have p8340_0 := h8340c.1
                                      have p8340_1 := h8340c.2.1
                                      have p8340_2 := h8340c.2.2.1
                                      have p8340_3 := h8340c.2.2.2
                                      linarith only [h8287, hlam, p8340_0]
                                    · have p8340_0 := h8340c.1
                                      have p8340_1 := h8340c.2.1
                                      have p8340_2 := h8340c.2.2.1
                                      have p8340_3 := h8340c.2.2.2
                                      linarith only [h8288, hlam, p8340_1]
                                    · have p8340_0 := h8340c.1
                                      have p8340_1 := h8340c.2.1
                                      have p8340_2 := h8340c.2.2.1
                                      have p8340_3 := h8340c.2.2.2
                                      linarith only [hlam, p8340_0]
                                  · linarith only [h6253, h8292, h8339, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                · linarith only [h6253, h8081, h8334, h8335, h8337, h8338, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h6253, h8287, h8292, h8337, hc23, hc34, hlam, hphi]
                          · linarith only [h7338, h8288, h8334, hlam]
                        · linarith only [h6253, h8287, h8333, hlam]
                    · linarith only [h0, h8084, h8291, hlam]
                  · linarith only [h0, h8083, h8290, hlam]
                · linarith only [h0, h8082, h8289, hlam]
              · linarith only [h6253, h8081, h8085, h8288, hlam]
            · linarith only [h6253, h8081, h8287, hlam]
        · linarith only [h0, h8081, h8084, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h8381 | h8381
        · rcases m.htr 0 3 4 (by decide) (by decide) with h8382 | h8382
          · linarith only [h8082, h8083, h8382, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h8384 | h8384
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8385 | h8385
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8386 | h8386
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8387 | h8387
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8388 | h8388
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8389 | h8389
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8390 | h8390
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8391 | h8391
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8392 | h8392
                            · linarith only [h6253, h8082, h8083, h8382, h8387, h8392, hc01, hc12, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8394 | h8394
                              · linarith only [h8082, h8083, h8386, h8389, h8392, h8394, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h8082, h8083, h8384, h8386, h8389, h8392, h8394, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h7338, h8081, h8385, h8388, h8391, hc04, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h8082, h8083, h8382, h8389, h8390, hc23, hc35, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8399 | h8399
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8400 | h8400
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8401 | h8401
                            · linarith only [h8082, h8083, h8387, h8389, h8401, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8403 | h8403
                              · linarith only [h8082, h8083, h8387, h8403, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h8082, h8083, h8384, h8387, h8403, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h7338, h8081, h8385, h8388, h8400, hc04, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h6253, h8081, h8082, h8083, h8384, h8387, h8388, h8399, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h8083, h8387, h8388, hc02, hc25, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8409 | h8409
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8410 | h8410
                      · linarith only [h6253, h8081, h8382, h8386, h8387, h8409, h8410, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8412 | h8412
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8413 | h8413
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8414 | h8414
                            · linarith only [h6253, h8081, h8409, h8410, h8414, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8416 | h8416
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8417 | h8417
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8418 | h8418
                                  · rcases h0bigk with h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c | h8419c
                                    · have p8419_0 := h8419c.1
                                      have p8419_1 := h8419c.2.1
                                      have p8419_2 := h8419c.2.2.1
                                      have p8419_3 := h8419c.2.2.2
                                      linarith only [hlam, p8419_0]
                                    · have p8419_0 := h8419c.1
                                      have p8419_1 := h8419c.2.1
                                      have p8419_2 := h8419c.2.2.1
                                      have p8419_3 := h8419c.2.2.2
                                      linarith only [h0, hlam, p8419_1]
                                    · have p8419_0 := h8419c.1
                                      have p8419_1 := h8419c.2.1
                                      have p8419_2 := h8419c.2.2.1
                                      have p8419_3 := h8419c.2.2.2
                                      linarith only [h6253, hlam, p8419_0]
                                    · have p8419_0 := h8419c.1
                                      have p8419_1 := h8419c.2.1
                                      have p8419_2 := h8419c.2.2.1
                                      have p8419_3 := h8419c.2.2.2
                                      linarith only [h7338, hlam, p8419_1]
                                    · have p8419_0 := h8419c.1
                                      have p8419_1 := h8419c.2.1
                                      have p8419_2 := h8419c.2.2.1
                                      have p8419_3 := h8419c.2.2.2
                                      linarith only [h6253, h8386, h8387, h8414, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8419_1]
                                    · have p8419_0 := h8419c.1
                                      have p8419_1 := h8419c.2.1
                                      have p8419_2 := h8419c.2.2.1
                                      have p8419_3 := h8419c.2.2.2
                                      linarith only [h8081, hc02, hc15, hlam, hphi, ht0b, ht5b, p8419_1]
                                    · have p8419_0 := h8419c.1
                                      have p8419_1 := h8419c.2.1
                                      have p8419_2 := h8419c.2.2.1
                                      have p8419_3 := h8419c.2.2.2
                                      linarith only [hlam, p8419_0]
                                    · have p8419_0 := h8419c.1
                                      have p8419_1 := h8419c.2.1
                                      have p8419_2 := h8419c.2.2.1
                                      have p8419_3 := h8419c.2.2.2
                                      linarith only [h0, h6253, h8081, h8387, h8409, h8414, h8416, h8418, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8419_1]
                                    · have p8419_0 := h8419c.1
                                      have p8419_1 := h8419c.2.1
                                      have p8419_2 := h8419c.2.2.1
                                      have p8419_3 := h8419c.2.2.2
                                      linarith only [h8083, hlam, p8419_1]
                                    · have p8419_0 := h8419c.1
                                      have p8419_1 := h8419c.2.1
                                      have p8419_2 := h8419c.2.2.1
                                      have p8419_3 := h8419c.2.2.2
                                      linarith only [h0, h8081, h8387, h8409, h8414, h8416, h8418, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8419_1]
                                    · have p8419_0 := h8419c.1
                                      have p8419_1 := h8419c.2.1
                                      have p8419_2 := h8419c.2.2.1
                                      have p8419_3 := h8419c.2.2.2
                                      linarith only [h8081, h8409, h8416, h8418, hc03, hc45, hlam, hphi, ht0b, ht5b, p8419_1]
                                    · have p8419_0 := h8419c.1
                                      have p8419_1 := h8419c.2.1
                                      have p8419_2 := h8419c.2.2.1
                                      have p8419_3 := h8419c.2.2.2
                                      linarith only [h8082, hlam, p8419_1]
                                    · have p8419_0 := h8419c.1
                                      have p8419_1 := h8419c.2.1
                                      have p8419_2 := h8419c.2.2.1
                                      have p8419_3 := h8419c.2.2.2
                                      linarith only [hlam, p8419_0]
                                    · have p8419_0 := h8419c.1
                                      have p8419_1 := h8419c.2.1
                                      have p8419_2 := h8419c.2.2.1
                                      have p8419_3 := h8419c.2.2.2
                                      linarith only [h8382, hlam, p8419_1]
                                    · have p8419_0 := h8419c.1
                                      have p8419_1 := h8419c.2.1
                                      have p8419_2 := h8419c.2.2.1
                                      have p8419_3 := h8419c.2.2.2
                                      linarith only [h0, h8081, h8082, h8387, h8409, h8414, h8416, h8418, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8419_1]
                                    · have p8419_0 := h8419c.1
                                      have p8419_1 := h8419c.2.1
                                      have p8419_2 := h8419c.2.2.1
                                      have p8419_3 := h8419c.2.2.2
                                      linarith only [h7338, h8081, h8387, h8409, h8414, h8416, h8418, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8419_1]
                                    · have p8419_0 := h8419c.1
                                      have p8419_1 := h8419c.2.1
                                      have p8419_2 := h8419c.2.2.1
                                      have p8419_3 := h8419c.2.2.2
                                      linarith only [h7338, h8387, h8414, hc02, hc34, hlam, hphi, ht23, p8419_1]
                                    · have p8419_0 := h8419c.1
                                      have p8419_1 := h8419c.2.1
                                      have p8419_2 := h8419c.2.2.1
                                      have p8419_3 := h8419c.2.2.2
                                      linarith only [h6253, h7338, h8081, h8387, h8409, h8414, h8416, h8418, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8419_1]
                                    · have p8419_0 := h8419c.1
                                      have p8419_1 := h8419c.2.1
                                      have p8419_2 := h8419c.2.2.1
                                      have p8419_3 := h8419c.2.2.2
                                      linarith only [hlam, p8419_0]
                                    · have p8419_0 := h8419c.1
                                      have p8419_1 := h8419c.2.1
                                      have p8419_2 := h8419c.2.2.1
                                      have p8419_3 := h8419c.2.2.2
                                      rcases p8419_3 (m.d 0 1) (by simp) with h8439 | h8439
                                      · linarith only [h7338, h8439, hlam]
                                      · linarith only [h8081, h8439, hlam]
                                    · have p8419_0 := h8419c.1
                                      have p8419_1 := h8419c.2.1
                                      have p8419_2 := h8419c.2.2.1
                                      have p8419_3 := h8419c.2.2.2
                                      linarith only [h8081, hlam, p8419_0]
                                    · have p8419_0 := h8419c.1
                                      have p8419_1 := h8419c.2.1
                                      have p8419_2 := h8419c.2.2.1
                                      have p8419_3 := h8419c.2.2.2
                                      linarith only [h8381, hlam, p8419_1]
                                    · have p8419_0 := h8419c.1
                                      have p8419_1 := h8419c.2.1
                                      have p8419_2 := h8419c.2.2.1
                                      have p8419_3 := h8419c.2.2.2
                                      linarith only [h8384, hlam, p8419_0]
                                    · have p8419_0 := h8419c.1
                                      have p8419_1 := h8419c.2.1
                                      have p8419_2 := h8419c.2.2.1
                                      have p8419_3 := h8419c.2.2.2
                                      linarith only [h8385, hlam, p8419_1]
                                    · have p8419_0 := h8419c.1
                                      have p8419_1 := h8419c.2.1
                                      have p8419_2 := h8419c.2.2.1
                                      have p8419_3 := h8419c.2.2.2
                                      linarith only [hlam, p8419_0]
                                  · linarith only [h0, h8081, h8387, h8409, h8414, h8418, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                · linarith only [h6253, h8081, h8386, h8387, h8413, h8417, hlam]
                              · linarith only [h6253, h8384, h8386, h8387, h8414, h8416, hc23, hc34, hlam, hphi]
                          · linarith only [h7338, h8385, h8413, hlam]
                        · linarith only [h6253, h8384, h8412, hlam]
                    · linarith only [h0, h8381, h8409, hlam]
                · linarith only [h0, h8082, h8386, hlam]
              · linarith only [h7338, h8081, h8385, hlam]
            · linarith only [h6253, h8081, h8384, hlam]
        · linarith only [h0, h8081, h8381, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h8457 | h8457
      · rcases m.htr 0 2 5 (by decide) (by decide) with h8458 | h8458
        · rcases m.htr 0 3 4 (by decide) (by decide) with h8459 | h8459
          · rcases m.htr 0 3 5 (by decide) (by decide) with h8460 | h8460
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8461 | h8461
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8462 | h8462
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8463 | h8463
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8464 | h8464
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8465 | h8465
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8466 | h8466
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8467 | h8467
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8468 | h8468
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8469 | h8469
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8470 | h8470
                                · linarith only [h8082, h8457, h8462, h8470, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h8082, h8457, h8461, h8462, h8470, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h7338, h8081, h8082, h8457, h8460, h8469, hc03, hc15, hlam, hphi, ht0b, ht5b]
                            · linarith only [h7338, h8081, h8082, h8457, h8459, h8468, hc03, hc15, hlam, hphi, ht0b, ht5b]
                          · linarith only [h7338, h8081, h8457, h8461, h8464, h8467, hc02, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h6253, h8460, h8466, hlam]
                      · linarith only [h8082, h8457, h8459, h8462, h8465, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h7338, h8081, h8082, h8457, h8462, h8464, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h8082, h8457, h8462, h8463, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8480 | h8480
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8481 | h8481
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8482 | h8482
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8483 | h8483
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8484 | h8484
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8485 | h8485
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8486 | h8486
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8487 | h8487
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8488 | h8488
                                  · rcases h0bigk with h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c | h8489c
                                    · have p8489_0 := h8489c.1
                                      have p8489_1 := h8489c.2.1
                                      have p8489_2 := h8489c.2.2.1
                                      have p8489_3 := h8489c.2.2.2
                                      linarith only [hlam, p8489_0]
                                    · have p8489_0 := h8489c.1
                                      have p8489_1 := h8489c.2.1
                                      have p8489_2 := h8489c.2.2.1
                                      have p8489_3 := h8489c.2.2.2
                                      linarith only [h0, hlam, p8489_1]
                                    · have p8489_0 := h8489c.1
                                      have p8489_1 := h8489c.2.1
                                      have p8489_2 := h8489c.2.2.1
                                      have p8489_3 := h8489c.2.2.2
                                      linarith only [h6253, hlam, p8489_0]
                                    · have p8489_0 := h8489c.1
                                      have p8489_1 := h8489c.2.1
                                      have p8489_2 := h8489c.2.2.1
                                      have p8489_3 := h8489c.2.2.2
                                      linarith only [h7338, hlam, p8489_1]
                                    · have p8489_0 := h8489c.1
                                      have p8489_1 := h8489c.2.1
                                      have p8489_2 := h8489c.2.2.1
                                      have p8489_3 := h8489c.2.2.2
                                      linarith only [h7338, h8462, h8480, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p8489_1]
                                    · have p8489_0 := h8489c.1
                                      have p8489_1 := h8489c.2.1
                                      have p8489_2 := h8489c.2.2.1
                                      have p8489_3 := h8489c.2.2.2
                                      linarith only [h8081, hc02, hc15, hlam, hphi, ht0b, ht5b, p8489_1]
                                    · have p8489_0 := h8489c.1
                                      have p8489_1 := h8489c.2.1
                                      have p8489_2 := h8489c.2.2.1
                                      have p8489_3 := h8489c.2.2.2
                                      linarith only [hlam, p8489_0]
                                    · have p8489_0 := h8489c.1
                                      have p8489_1 := h8489c.2.1
                                      have p8489_2 := h8489c.2.2.1
                                      have p8489_3 := h8489c.2.2.2
                                      linarith only [h8082, hlam, p8489_0]
                                    · have p8489_0 := h8489c.1
                                      have p8489_1 := h8489c.2.1
                                      have p8489_2 := h8489c.2.2.1
                                      have p8489_3 := h8489c.2.2.2
                                      linarith only [h0, h8462, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8489_1]
                                    · have p8489_0 := h8489c.1
                                      have p8489_1 := h8489c.2.1
                                      have p8489_2 := h8489c.2.2.1
                                      have p8489_3 := h8489c.2.2.2
                                      linarith only [h0, h8081, h8462, h8481, h8486, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p8489_1]
                                    · have p8489_0 := h8489c.1
                                      have p8489_1 := h8489c.2.1
                                      have p8489_2 := h8489c.2.2.1
                                      have p8489_3 := h8489c.2.2.2
                                      linarith only [h6253, h8081, h8462, h8481, h8486, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p8489_1]
                                    · have p8489_0 := h8489c.1
                                      have p8489_1 := h8489c.2.1
                                      have p8489_2 := h8489c.2.2.1
                                      have p8489_3 := h8489c.2.2.2
                                      linarith only [h6253, h8462, hc02, hc23, hlam, hphi, p8489_1]
                                    · have p8489_0 := h8489c.1
                                      have p8489_1 := h8489c.2.1
                                      have p8489_2 := h8489c.2.2.1
                                      have p8489_3 := h8489c.2.2.2
                                      linarith only [hlam, p8489_0]
                                    · have p8489_0 := h8489c.1
                                      have p8489_1 := h8489c.2.1
                                      have p8489_2 := h8489c.2.2.1
                                      have p8489_3 := h8489c.2.2.2
                                      linarith only [h6253, h7338, h8081, h8462, h8481, h8486, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p8489_1]
                                    · have p8489_0 := h8489c.1
                                      have p8489_1 := h8489c.2.1
                                      have p8489_2 := h8489c.2.2.1
                                      have p8489_3 := h8489c.2.2.2
                                      rcases p8489_3 (m.d 0 1) (by simp) with h8504 | h8504
                                      · linarith only [h6253, h8504, hlam]
                                      · linarith only [h8081, h8504, hlam]
                                    · have p8489_0 := h8489c.1
                                      have p8489_1 := h8489c.2.1
                                      have p8489_2 := h8489c.2.2.1
                                      have p8489_3 := h8489c.2.2.2
                                      linarith only [h8081, h8481, h8486, h8488, hc04, hc45, hlam, hphi, ht0b, ht5b, p8489_1]
                                    · have p8489_0 := h8489c.1
                                      have p8489_1 := h8489c.2.1
                                      have p8489_2 := h8489c.2.2.1
                                      have p8489_3 := h8489c.2.2.2
                                      linarith only [h8457, hlam, p8489_0]
                                    · have p8489_0 := h8489c.1
                                      have p8489_1 := h8489c.2.1
                                      have p8489_2 := h8489c.2.2.1
                                      have p8489_3 := h8489c.2.2.2
                                      linarith only [h8459, hlam, p8489_0]
                                    · have p8489_0 := h8489c.1
                                      have p8489_1 := h8489c.2.1
                                      have p8489_2 := h8489c.2.2.1
                                      have p8489_3 := h8489c.2.2.2
                                      linarith only [hlam, p8489_0]
                                    · have p8489_0 := h8489c.1
                                      have p8489_1 := h8489c.2.1
                                      have p8489_2 := h8489c.2.2.1
                                      have p8489_3 := h8489c.2.2.2
                                      linarith only [h0, h8081, h8457, h8462, h8481, h8486, h8488, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8489_1]
                                    · have p8489_0 := h8489c.1
                                      have p8489_1 := h8489c.2.1
                                      have p8489_2 := h8489c.2.2.1
                                      have p8489_3 := h8489c.2.2.2
                                      linarith only [h8081, hlam, p8489_0]
                                    · have p8489_0 := h8489c.1
                                      have p8489_1 := h8489c.2.1
                                      have p8489_2 := h8489c.2.2.1
                                      have p8489_3 := h8489c.2.2.2
                                      linarith only [h8458, hlam, p8489_1]
                                    · have p8489_0 := h8489c.1
                                      have p8489_1 := h8489c.2.1
                                      have p8489_2 := h8489c.2.2.1
                                      have p8489_3 := h8489c.2.2.2
                                      linarith only [h8460, hlam, p8489_0]
                                    · have p8489_0 := h8489c.1
                                      have p8489_1 := h8489c.2.1
                                      have p8489_2 := h8489c.2.2.1
                                      have p8489_3 := h8489c.2.2.2
                                      linarith only [h8461, hlam, p8489_1]
                                    · have p8489_0 := h8489c.1
                                      have p8489_1 := h8489c.2.1
                                      have p8489_2 := h8489c.2.2.1
                                      have p8489_3 := h8489c.2.2.2
                                      linarith only [hlam, p8489_0]
                                  · linarith only [h0, h8081, h8462, h8484, h8488, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h7338, h8081, h8462, h8480, h8484, h8487, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h7338, h8462, h8480, h8486, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h7338, h8081, h8462, h8480, h8484, h8485, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h7338, h8461, h8484, hlam]
                        · linarith only [h6253, h8460, h8483, hlam]
                      · linarith only [h0, h8081, h8459, h8462, h8481, h8482, hc03, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h8458, h8481, hlam]
                  · linarith only [h0, h8457, h8480, hlam]
              · linarith only [h7338, h8081, h8461, hlam]
            · linarith only [h6253, h8081, h8460, hlam]
          · linarith only [h8082, h8457, h8459, hlam]
        · linarith only [h7338, h8081, h8457, h8458, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h8530 | h8530
        · rcases m.htr 0 3 4 (by decide) (by decide) with h8531 | h8531
          · rcases m.htr 0 3 5 (by decide) (by decide) with h8532 | h8532
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8533 | h8533
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8534 | h8534
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8535 | h8535
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8536 | h8536
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8537 | h8537
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8538 | h8538
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8539 | h8539
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8540 | h8540
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8541 | h8541
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8542 | h8542
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8543 | h8543
                                  · rcases h0bigk with h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c | h8544c
                                    · have p8544_0 := h8544c.1
                                      have p8544_1 := h8544c.2.1
                                      have p8544_2 := h8544c.2.2.1
                                      have p8544_3 := h8544c.2.2.2
                                      linarith only [hlam, p8544_0]
                                    · have p8544_0 := h8544c.1
                                      have p8544_1 := h8544c.2.1
                                      have p8544_2 := h8544c.2.2.1
                                      have p8544_3 := h8544c.2.2.2
                                      linarith only [h0, hlam, p8544_1]
                                    · have p8544_0 := h8544c.1
                                      have p8544_1 := h8544c.2.1
                                      have p8544_2 := h8544c.2.2.1
                                      have p8544_3 := h8544c.2.2.2
                                      linarith only [h6253, hlam, p8544_0]
                                    · have p8544_0 := h8544c.1
                                      have p8544_1 := h8544c.2.1
                                      have p8544_2 := h8544c.2.2.1
                                      have p8544_3 := h8544c.2.2.2
                                      linarith only [h7338, hlam, p8544_1]
                                    · have p8544_0 := h8544c.1
                                      have p8544_1 := h8544c.2.1
                                      have p8544_2 := h8544c.2.2.1
                                      have p8544_3 := h8544c.2.2.2
                                      linarith only [h0, h8457, h8534, h8540, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p8544_1]
                                    · have p8544_0 := h8544c.1
                                      have p8544_1 := h8544c.2.1
                                      have p8544_2 := h8544c.2.2.1
                                      have p8544_3 := h8544c.2.2.2
                                      linarith only [h8457, h8534, h8540, hc01, hc12, hlam, hphi, p8544_1]
                                    · have p8544_0 := h8544c.1
                                      have p8544_1 := h8544c.2.1
                                      have p8544_2 := h8544c.2.2.1
                                      have p8544_3 := h8544c.2.2.2
                                      linarith only [hlam, p8544_0]
                                    · have p8544_0 := h8544c.1
                                      have p8544_1 := h8544c.2.1
                                      have p8544_2 := h8544c.2.2.1
                                      have p8544_3 := h8544c.2.2.2
                                      linarith only [h8082, hlam, p8544_0]
                                    · have p8544_0 := h8544c.1
                                      have p8544_1 := h8544c.2.1
                                      have p8544_2 := h8544c.2.2.1
                                      have p8544_3 := h8544c.2.2.2
                                      linarith only [h8457, hlam, p8544_1]
                                    · have p8544_0 := h8544c.1
                                      have p8544_1 := h8544c.2.1
                                      have p8544_2 := h8544c.2.2.1
                                      have p8544_3 := h8544c.2.2.2
                                      linarith only [h8081, h8457, h8534, h8536, h8540, h8541, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p8544_1]
                                    · have p8544_0 := h8544c.1
                                      have p8544_1 := h8544c.2.1
                                      have p8544_2 := h8544c.2.2.1
                                      have p8544_3 := h8544c.2.2.2
                                      linarith only [h8081, h8536, h8541, hc03, hc35, hlam, hphi, ht0b, ht5b, p8544_1]
                                    · have p8544_0 := h8544c.1
                                      have p8544_1 := h8544c.2.1
                                      have p8544_2 := h8544c.2.2.1
                                      have p8544_3 := h8544c.2.2.2
                                      linarith only [h8082, h8534, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p8544_1]
                                    · have p8544_0 := h8544c.1
                                      have p8544_1 := h8544c.2.1
                                      have p8544_2 := h8544c.2.2.1
                                      have p8544_3 := h8544c.2.2.2
                                      linarith only [hlam, p8544_0]
                                    · have p8544_0 := h8544c.1
                                      have p8544_1 := h8544c.2.1
                                      have p8544_2 := h8544c.2.2.1
                                      have p8544_3 := h8544c.2.2.2
                                      linarith only [h0, h8081, h8082, h8457, h8534, h8536, h8541, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p8544_1]
                                    · have p8544_0 := h8544c.1
                                      have p8544_1 := h8544c.2.1
                                      have p8544_2 := h8544c.2.2.1
                                      have p8544_3 := h8544c.2.2.2
                                      linarith only [h8081, h8082, h8534, h8536, h8541, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p8544_1]
                                    · have p8544_0 := h8544c.1
                                      have p8544_1 := h8544c.2.1
                                      have p8544_2 := h8544c.2.2.1
                                      have p8544_3 := h8544c.2.2.2
                                      linarith only [h8081, h8536, h8541, hc04, hc35, hlam, hphi, ht0b, ht5b, p8544_1]
                                    · have p8544_0 := h8544c.1
                                      have p8544_1 := h8544c.2.1
                                      have p8544_2 := h8544c.2.2.1
                                      have p8544_3 := h8544c.2.2.2
                                      linarith only [h0, h8081, h8457, h8534, h8536, h8540, h8541, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p8544_1]
                                    · have p8544_0 := h8544c.1
                                      have p8544_1 := h8544c.2.1
                                      have p8544_2 := h8544c.2.2.1
                                      have p8544_3 := h8544c.2.2.2
                                      linarith only [h8531, hlam, p8544_0]
                                    · have p8544_0 := h8544c.1
                                      have p8544_1 := h8544c.2.1
                                      have p8544_2 := h8544c.2.2.1
                                      have p8544_3 := h8544c.2.2.2
                                      linarith only [hlam, p8544_0]
                                    · have p8544_0 := h8544c.1
                                      have p8544_1 := h8544c.2.1
                                      have p8544_2 := h8544c.2.2.1
                                      have p8544_3 := h8544c.2.2.2
                                      linarith only [h8081, h8457, h8534, h8536, h8540, h8541, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p8544_1]
                                    · have p8544_0 := h8544c.1
                                      have p8544_1 := h8544c.2.1
                                      have p8544_2 := h8544c.2.2.1
                                      have p8544_3 := h8544c.2.2.2
                                      linarith only [h8081, hlam, p8544_0]
                                    · have p8544_0 := h8544c.1
                                      have p8544_1 := h8544c.2.1
                                      have p8544_2 := h8544c.2.2.1
                                      have p8544_3 := h8544c.2.2.2
                                      linarith only [h8530, hlam, p8544_1]
                                    · have p8544_0 := h8544c.1
                                      have p8544_1 := h8544c.2.1
                                      have p8544_2 := h8544c.2.2.1
                                      have p8544_3 := h8544c.2.2.2
                                      linarith only [h8532, hlam, p8544_0]
                                    · have p8544_0 := h8544c.1
                                      have p8544_1 := h8544c.2.1
                                      have p8544_2 := h8544c.2.2.1
                                      have p8544_3 := h8544c.2.2.2
                                      linarith only [h8533, hlam, p8544_1]
                                    · have p8544_0 := h8544c.1
                                      have p8544_1 := h8544c.2.1
                                      have p8544_2 := h8544c.2.2.1
                                      have p8544_3 := h8544c.2.2.2
                                      linarith only [hlam, p8544_0]
                                  · linarith only [h0, h8081, h8457, h8534, h8539, h8540, h8543, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h0, h8081, h8457, h8539, h8542, hlam]
                              · linarith only [h8082, h8532, h8541, hlam]
                            · linarith only [h8082, h8531, h8540, hlam]
                          · linarith only [h0, h8081, h8457, h8531, h8533, h8535, h8539, hc03, hc15, hlam, hphi, ht0b, ht5b]
                        · linarith only [h6253, h8532, h8538, hlam]
                      · linarith only [h8082, h8531, h8534, h8537, hlam]
                    · linarith only [h8082, h8530, h8536, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h8082, h8534, h8535, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8579 | h8579
                  · linarith only [h0, h8081, h8457, h8534, h8579, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8581 | h8581
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8582 | h8582
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8583 | h8583
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8584 | h8584
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8585 | h8585
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8586 | h8586
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8587 | h8587
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8588 | h8588
                                  · rcases h0bigk with h8589c | h8589c | h8589c | h8589c | h8589c | h8589c | h8589c | h8589c | h8589c | h8589c | h8589c | h8589c | h8589c | h8589c | h8589c | h8589c | h8589c | h8589c | h8589c | h8589c | h8589c | h8589c | h8589c | h8589c | h8589c
                                    · have p8589_0 := h8589c.1
                                      have p8589_1 := h8589c.2.1
                                      have p8589_2 := h8589c.2.2.1
                                      have p8589_3 := h8589c.2.2.2
                                      linarith only [hlam, p8589_0]
                                    · have p8589_0 := h8589c.1
                                      have p8589_1 := h8589c.2.1
                                      have p8589_2 := h8589c.2.2.1
                                      have p8589_3 := h8589c.2.2.2
                                      linarith only [h0, hlam, p8589_1]
                                    · have p8589_0 := h8589c.1
                                      have p8589_1 := h8589c.2.1
                                      have p8589_2 := h8589c.2.2.1
                                      have p8589_3 := h8589c.2.2.2
                                      linarith only [h6253, hlam, p8589_0]
                                    · have p8589_0 := h8589c.1
                                      have p8589_1 := h8589c.2.1
                                      have p8589_2 := h8589c.2.2.1
                                      have p8589_3 := h8589c.2.2.2
                                      linarith only [h7338, hlam, p8589_1]
                                    · have p8589_0 := h8589c.1
                                      have p8589_1 := h8589c.2.1
                                      have p8589_2 := h8589c.2.2.1
                                      have p8589_3 := h8589c.2.2.2
                                      linarith only [h0, h8579, h8585, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p8589_1]
                                    · have p8589_0 := h8589c.1
                                      have p8589_1 := h8589c.2.1
                                      have p8589_2 := h8589c.2.2.1
                                      have p8589_3 := h8589c.2.2.2
                                      linarith only [h0, h8579, h8585, hc01, hc23, hlam, hphi, ht12, p8589_1]
                                    · have p8589_0 := h8589c.1
                                      have p8589_1 := h8589c.2.1
                                      have p8589_2 := h8589c.2.2.1
                                      have p8589_3 := h8589c.2.2.2
                                      linarith only [hlam, p8589_0]
                                    · have p8589_0 := h8589c.1
                                      have p8589_1 := h8589c.2.1
                                      have p8589_2 := h8589c.2.2.1
                                      have p8589_3 := h8589c.2.2.2
                                      linarith only [h8082, hlam, p8589_0]
                                    · have p8589_0 := h8589c.1
                                      have p8589_1 := h8589c.2.1
                                      have p8589_2 := h8589c.2.2.1
                                      have p8589_3 := h8589c.2.2.2
                                      linarith only [h8457, hlam, p8589_1]
                                    · have p8589_0 := h8589c.1
                                      have p8589_1 := h8589c.2.1
                                      have p8589_2 := h8589c.2.2.1
                                      have p8589_3 := h8589c.2.2.2
                                      linarith only [h0, h8081, h8579, h8581, h8585, h8586, h8588, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8589_1]
                                    · have p8589_0 := h8589c.1
                                      have p8589_1 := h8589c.2.1
                                      have p8589_2 := h8589c.2.2.1
                                      have p8589_3 := h8589c.2.2.2
                                      linarith only [h8081, h8581, h8586, h8588, hc03, hc45, hlam, hphi, ht0b, ht5b, p8589_1]
                                    · have p8589_0 := h8589c.1
                                      have p8589_1 := h8589c.2.1
                                      have p8589_2 := h8589c.2.2.1
                                      have p8589_3 := h8589c.2.2.2
                                      linarith only [h8082, hc02, hc23, hlam, hphi, p8589_1]
                                    · have p8589_0 := h8589c.1
                                      have p8589_1 := h8589c.2.1
                                      have p8589_2 := h8589c.2.2.1
                                      have p8589_3 := h8589c.2.2.2
                                      linarith only [hlam, p8589_0]
                                    · have p8589_0 := h8589c.1
                                      have p8589_1 := h8589c.2.1
                                      have p8589_2 := h8589c.2.2.1
                                      have p8589_3 := h8589c.2.2.2
                                      linarith only [h7338, h8081, h8082, h8581, h8586, h8588, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8589_1]
                                    · have p8589_0 := h8589c.1
                                      have p8589_1 := h8589c.2.1
                                      have p8589_2 := h8589c.2.2.1
                                      have p8589_3 := h8589c.2.2.2
                                      rcases p8589_3 (m.d 0 1) (by simp) with h8604 | h8604
                                      · linarith only [h6253, h8604, hlam]
                                      · linarith only [h8081, h8604, hlam]
                                    · have p8589_0 := h8589c.1
                                      have p8589_1 := h8589c.2.1
                                      have p8589_2 := h8589c.2.2.1
                                      have p8589_3 := h8589c.2.2.2
                                      linarith only [h8081, h8581, h8586, h8588, hc04, hc45, hlam, hphi, ht0b, ht5b, p8589_1]
                                    · have p8589_0 := h8589c.1
                                      have p8589_1 := h8589c.2.1
                                      have p8589_2 := h8589c.2.2.1
                                      have p8589_3 := h8589c.2.2.2
                                      linarith only [h0, h7338, h8081, h8579, h8581, h8585, h8586, h8588, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8589_1]
                                    · have p8589_0 := h8589c.1
                                      have p8589_1 := h8589c.2.1
                                      have p8589_2 := h8589c.2.2.1
                                      have p8589_3 := h8589c.2.2.2
                                      linarith only [h8531, hlam, p8589_0]
                                    · have p8589_0 := h8589c.1
                                      have p8589_1 := h8589c.2.1
                                      have p8589_2 := h8589c.2.2.1
                                      have p8589_3 := h8589c.2.2.2
                                      linarith only [hlam, p8589_0]
                                    · have p8589_0 := h8589c.1
                                      have p8589_1 := h8589c.2.1
                                      have p8589_2 := h8589c.2.2.1
                                      have p8589_3 := h8589c.2.2.2
                                      rcases p8589_3 (m.d 0 1) (by simp) with h8611 | h8611
                                      · linarith only [h7338, h8611, hlam]
                                      · linarith only [h8081, h8611, hlam]
                                    · have p8589_0 := h8589c.1
                                      have p8589_1 := h8589c.2.1
                                      have p8589_2 := h8589c.2.2.1
                                      have p8589_3 := h8589c.2.2.2
                                      linarith only [h8081, hlam, p8589_0]
                                    · have p8589_0 := h8589c.1
                                      have p8589_1 := h8589c.2.1
                                      have p8589_2 := h8589c.2.2.1
                                      have p8589_3 := h8589c.2.2.2
                                      linarith only [h8530, hlam, p8589_1]
                                    · have p8589_0 := h8589c.1
                                      have p8589_1 := h8589c.2.1
                                      have p8589_2 := h8589c.2.2.1
                                      have p8589_3 := h8589c.2.2.2
                                      linarith only [h8532, hlam, p8589_0]
                                    · have p8589_0 := h8589c.1
                                      have p8589_1 := h8589c.2.1
                                      have p8589_2 := h8589c.2.2.1
                                      have p8589_3 := h8589c.2.2.2
                                      linarith only [h8533, hlam, p8589_1]
                                    · have p8589_0 := h8589c.1
                                      have p8589_1 := h8589c.2.1
                                      have p8589_2 := h8589c.2.2.1
                                      have p8589_3 := h8589c.2.2.2
                                      linarith only [hlam, p8589_0]
                                  · linarith only [h0, h8081, h8579, h8584, h8585, h8588, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h0, h8081, h8579, h8584, h8587, hlam]
                              · linarith only [h0, h8579, h8585, h8586, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h6253, h8531, h8534, h8585, hlam]
                          · linarith only [h7338, h8533, h8584, hlam]
                        · linarith only [h6253, h8081, h8532, h8583, hc03, hc15, hlam, hphi, ht0b, ht5b]
                      · linarith only [h6253, h8531, h8582, hlam]
                    · linarith only [h0, h8081, h8457, h8530, h8581, hc04, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h8081, h8457, h8533, hlam]
            · linarith only [h0, h8081, h8457, h8531, h8532, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h8629 | h8629
            · rcases m.htr 0 4 5 (by decide) (by decide) with h8630 | h8630
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8631 | h8631
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8632 | h8632
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8633 | h8633
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8634 | h8634
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8635 | h8635
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8636 | h8636
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8637 | h8637
                            · linarith only [h0, h8082, h8531, h8631, h8637, hc01, hc12, hlam, hphi]
                            · linarith only [h0, h8081, h8082, h8633, h8634, h8637, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h7338, h8081, h8630, h8633, h8636, hc04, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h8081, h8082, h8531, h8633, h8634, h8635, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8642 | h8642
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8643 | h8643
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8644 | h8644
                            · linarith only [h8631, h8634, h8644, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8646 | h8646
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8647 | h8647
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8648 | h8648
                                  · rcases h0bigk with h8649c | h8649c | h8649c | h8649c | h8649c | h8649c | h8649c | h8649c | h8649c | h8649c | h8649c | h8649c | h8649c | h8649c | h8649c | h8649c | h8649c | h8649c | h8649c | h8649c | h8649c | h8649c | h8649c | h8649c | h8649c
                                    · have p8649_0 := h8649c.1
                                      have p8649_1 := h8649c.2.1
                                      have p8649_2 := h8649c.2.2.1
                                      have p8649_3 := h8649c.2.2.2
                                      linarith only [hlam, p8649_0]
                                    · have p8649_0 := h8649c.1
                                      have p8649_1 := h8649c.2.1
                                      have p8649_2 := h8649c.2.2.1
                                      have p8649_3 := h8649c.2.2.2
                                      linarith only [h0, hlam, p8649_1]
                                    · have p8649_0 := h8649c.1
                                      have p8649_1 := h8649c.2.1
                                      have p8649_2 := h8649c.2.2.1
                                      have p8649_3 := h8649c.2.2.2
                                      linarith only [h6253, hlam, p8649_0]
                                    · have p8649_0 := h8649c.1
                                      have p8649_1 := h8649c.2.1
                                      have p8649_2 := h8649c.2.2.1
                                      have p8649_3 := h8649c.2.2.2
                                      linarith only [h7338, hlam, p8649_1]
                                    · have p8649_0 := h8649c.1
                                      have p8649_1 := h8649c.2.1
                                      have p8649_2 := h8649c.2.2.1
                                      have p8649_3 := h8649c.2.2.2
                                      linarith only [h0, h8082, h8631, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p8649_1]
                                    · have p8649_0 := h8649c.1
                                      have p8649_1 := h8649c.2.1
                                      have p8649_2 := h8649c.2.2.1
                                      have p8649_3 := h8649c.2.2.2
                                      linarith only [h8082, h8631, hc01, hc13, hlam, hphi, p8649_1]
                                    · have p8649_0 := h8649c.1
                                      have p8649_1 := h8649c.2.1
                                      have p8649_2 := h8649c.2.2.1
                                      have p8649_3 := h8649c.2.2.2
                                      linarith only [hlam, p8649_0]
                                    · have p8649_0 := h8649c.1
                                      have p8649_1 := h8649c.2.1
                                      have p8649_2 := h8649c.2.2.1
                                      have p8649_3 := h8649c.2.2.2
                                      linarith only [h8082, hlam, p8649_0]
                                    · have p8649_0 := h8649c.1
                                      have p8649_1 := h8649c.2.1
                                      have p8649_2 := h8649c.2.2.1
                                      have p8649_3 := h8649c.2.2.2
                                      linarith only [h8457, hlam, p8649_1]
                                    · have p8649_0 := h8649c.1
                                      have p8649_1 := h8649c.2.1
                                      have p8649_2 := h8649c.2.2.1
                                      have p8649_3 := h8649c.2.2.2
                                      linarith only [h8081, h8457, h8632, h8633, h8646, h8648, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p8649_1]
                                    · have p8649_0 := h8649c.1
                                      have p8649_1 := h8649c.2.1
                                      have p8649_2 := h8649c.2.2.1
                                      have p8649_3 := h8649c.2.2.2
                                      linarith only [h6253, h8081, h8633, h8634, h8646, h8648, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8649_1]
                                    · have p8649_0 := h8649c.1
                                      have p8649_1 := h8649c.2.1
                                      have p8649_2 := h8649c.2.2.1
                                      have p8649_3 := h8649c.2.2.2
                                      linarith only [h6253, h8634, hc02, hc34, hlam, hphi, ht23, p8649_1]
                                    · have p8649_0 := h8649c.1
                                      have p8649_1 := h8649c.2.1
                                      have p8649_2 := h8649c.2.2.1
                                      have p8649_3 := h8649c.2.2.2
                                      linarith only [hlam, p8649_0]
                                    · have p8649_0 := h8649c.1
                                      have p8649_1 := h8649c.2.1
                                      have p8649_2 := h8649c.2.2.1
                                      have p8649_3 := h8649c.2.2.2
                                      linarith only [h8531, hlam, p8649_1]
                                    · have p8649_0 := h8649c.1
                                      have p8649_1 := h8649c.2.1
                                      have p8649_2 := h8649c.2.2.1
                                      have p8649_3 := h8649c.2.2.2
                                      linarith only [h8081, h8082, h8631, h8633, h8634, h8646, h8648, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8649_1]
                                    · have p8649_0 := h8649c.1
                                      have p8649_1 := h8649c.2.1
                                      have p8649_2 := h8649c.2.2.1
                                      have p8649_3 := h8649c.2.2.2
                                      linarith only [h8081, h8531, h8633, h8646, h8648, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8649_1]
                                    · have p8649_0 := h8649c.1
                                      have p8649_1 := h8649c.2.1
                                      have p8649_2 := h8649c.2.2.1
                                      have p8649_3 := h8649c.2.2.2
                                      linarith only [h0, h8081, h8531, h8633, h8646, h8648, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8649_1]
                                    · have p8649_0 := h8649c.1
                                      have p8649_1 := h8649c.2.1
                                      have p8649_2 := h8649c.2.2.1
                                      have p8649_3 := h8649c.2.2.2
                                      linarith only [h8531, hc03, hc34, hlam, hphi, p8649_1]
                                    · have p8649_0 := h8649c.1
                                      have p8649_1 := h8649c.2.1
                                      have p8649_2 := h8649c.2.2.1
                                      have p8649_3 := h8649c.2.2.2
                                      linarith only [hlam, p8649_0]
                                    · have p8649_0 := h8649c.1
                                      have p8649_1 := h8649c.2.1
                                      have p8649_2 := h8649c.2.2.1
                                      have p8649_3 := h8649c.2.2.2
                                      linarith only [h8081, h8457, h8632, h8633, h8646, h8648, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8649_1]
                                    · have p8649_0 := h8649c.1
                                      have p8649_1 := h8649c.2.1
                                      have p8649_2 := h8649c.2.2.1
                                      have p8649_3 := h8649c.2.2.2
                                      linarith only [h8081, hlam, p8649_0]
                                    · have p8649_0 := h8649c.1
                                      have p8649_1 := h8649c.2.1
                                      have p8649_2 := h8649c.2.2.1
                                      have p8649_3 := h8649c.2.2.2
                                      linarith only [h8530, hlam, p8649_1]
                                    · have p8649_0 := h8649c.1
                                      have p8649_1 := h8649c.2.1
                                      have p8649_2 := h8649c.2.2.1
                                      have p8649_3 := h8649c.2.2.2
                                      linarith only [h8629, hlam, p8649_0]
                                    · have p8649_0 := h8649c.1
                                      have p8649_1 := h8649c.2.1
                                      have p8649_2 := h8649c.2.2.1
                                      have p8649_3 := h8649c.2.2.2
                                      linarith only [h8630, hlam, p8649_1]
                                    · have p8649_0 := h8649c.1
                                      have p8649_1 := h8649c.2.1
                                      have p8649_2 := h8649c.2.2.1
                                      have p8649_3 := h8649c.2.2.2
                                      linarith only [hlam, p8649_0]
                                  · linarith only [h6253, h8634, h8648, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                · linarith only [h0, h8081, h8082, h8643, h8644, h8647, hlam]
                              · linarith only [h0, h8081, h8082, h8629, h8633, h8646, hc03, hc25, hlam, hphi, ht0b, ht5b]
                          · linarith only [h7338, h8081, h8630, h8633, h8643, hc04, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h8081, h8082, h8629, h8631, h8633, h8642, hc03, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h8082, h8631, h8633, hc02, hc25, hlam, hphi]
                  · linarith only [h0, h8081, h8082, h8631, h8632, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8682 | h8682
                  · linarith only [h0, h8081, h8457, h8631, h8682, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h8684 | h8684
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h8685 | h8685
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8686 | h8686
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8687 | h8687
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8688 | h8688
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h8689 | h8689
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h8690 | h8690
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h8691 | h8691
                                  · rcases h0bigk with h8692c | h8692c | h8692c | h8692c | h8692c | h8692c | h8692c | h8692c | h8692c | h8692c | h8692c | h8692c | h8692c | h8692c | h8692c | h8692c | h8692c | h8692c | h8692c | h8692c | h8692c | h8692c | h8692c | h8692c | h8692c
                                    · have p8692_0 := h8692c.1
                                      have p8692_1 := h8692c.2.1
                                      have p8692_2 := h8692c.2.2.1
                                      have p8692_3 := h8692c.2.2.2
                                      linarith only [hlam, p8692_0]
                                    · have p8692_0 := h8692c.1
                                      have p8692_1 := h8692c.2.1
                                      have p8692_2 := h8692c.2.2.1
                                      have p8692_3 := h8692c.2.2.2
                                      linarith only [h0, hlam, p8692_1]
                                    · have p8692_0 := h8692c.1
                                      have p8692_1 := h8692c.2.1
                                      have p8692_2 := h8692c.2.2.1
                                      have p8692_3 := h8692c.2.2.2
                                      linarith only [h6253, hlam, p8692_0]
                                    · have p8692_0 := h8692c.1
                                      have p8692_1 := h8692c.2.1
                                      have p8692_2 := h8692c.2.2.1
                                      have p8692_3 := h8692c.2.2.2
                                      linarith only [h7338, hlam, p8692_1]
                                    · have p8692_0 := h8692c.1
                                      have p8692_1 := h8692c.2.1
                                      have p8692_2 := h8692c.2.2.1
                                      have p8692_3 := h8692c.2.2.2
                                      linarith only [h0, h8081, h8682, h8684, h8688, h8689, h8691, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8692_1]
                                    · have p8692_0 := h8692c.1
                                      have p8692_1 := h8692c.2.1
                                      have p8692_2 := h8692c.2.2.1
                                      have p8692_3 := h8692c.2.2.2
                                      linarith only [h0, h8682, h8688, hc01, hc23, hlam, hphi, ht12, p8692_1]
                                    · have p8692_0 := h8692c.1
                                      have p8692_1 := h8692c.2.1
                                      have p8692_2 := h8692c.2.2.1
                                      have p8692_3 := h8692c.2.2.2
                                      linarith only [hlam, p8692_0]
                                    · have p8692_0 := h8692c.1
                                      have p8692_1 := h8692c.2.1
                                      have p8692_2 := h8692c.2.2.1
                                      have p8692_3 := h8692c.2.2.2
                                      linarith only [h8082, hlam, p8692_0]
                                    · have p8692_0 := h8692c.1
                                      have p8692_1 := h8692c.2.1
                                      have p8692_2 := h8692c.2.2.1
                                      have p8692_3 := h8692c.2.2.2
                                      linarith only [h8457, hlam, p8692_1]
                                    · have p8692_0 := h8692c.1
                                      have p8692_1 := h8692c.2.1
                                      have p8692_2 := h8692c.2.2.1
                                      have p8692_3 := h8692c.2.2.2
                                      linarith only [h0, h8081, h8682, h8684, h8688, h8689, h8691, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8692_1]
                                    · have p8692_0 := h8692c.1
                                      have p8692_1 := h8692c.2.1
                                      have p8692_2 := h8692c.2.2.1
                                      have p8692_3 := h8692c.2.2.2
                                      linarith only [h8081, h8684, h8689, h8691, hc03, hc45, hlam, hphi, ht0b, ht5b, p8692_1]
                                    · have p8692_0 := h8692c.1
                                      have p8692_1 := h8692c.2.1
                                      have p8692_2 := h8692c.2.2.1
                                      have p8692_3 := h8692c.2.2.2
                                      linarith only [h6253, h8631, hc02, hc23, hlam, hphi, p8692_1]
                                    · have p8692_0 := h8692c.1
                                      have p8692_1 := h8692c.2.1
                                      have p8692_2 := h8692c.2.2.1
                                      have p8692_3 := h8692c.2.2.2
                                      linarith only [hlam, p8692_0]
                                    · have p8692_0 := h8692c.1
                                      have p8692_1 := h8692c.2.1
                                      have p8692_2 := h8692c.2.2.1
                                      have p8692_3 := h8692c.2.2.2
                                      linarith only [h8531, hlam, p8692_1]
                                    · have p8692_0 := h8692c.1
                                      have p8692_1 := h8692c.2.1
                                      have p8692_2 := h8692c.2.2.1
                                      have p8692_3 := h8692c.2.2.2
                                      linarith only [h8081, h8531, h8631, h8684, h8685, h8689, h8691, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8692_1]
                                    · have p8692_0 := h8692c.1
                                      have p8692_1 := h8692c.2.1
                                      have p8692_2 := h8692c.2.2.1
                                      have p8692_3 := h8692c.2.2.2
                                      linarith only [h8081, h8531, h8631, h8684, h8685, h8689, h8691, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8692_1]
                                    · have p8692_0 := h8692c.1
                                      have p8692_1 := h8692c.2.1
                                      have p8692_2 := h8692c.2.2.1
                                      have p8692_3 := h8692c.2.2.2
                                      linarith only [h0, h8081, h8531, h8631, h8684, h8685, h8689, h8691, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8692_1]
                                    · have p8692_0 := h8692c.1
                                      have p8692_1 := h8692c.2.1
                                      have p8692_2 := h8692c.2.2.1
                                      have p8692_3 := h8692c.2.2.2
                                      linarith only [h8531, h8631, h8685, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p8692_1]
                                    · have p8692_0 := h8692c.1
                                      have p8692_1 := h8692c.2.1
                                      have p8692_2 := h8692c.2.2.1
                                      have p8692_3 := h8692c.2.2.2
                                      linarith only [hlam, p8692_0]
                                    · have p8692_0 := h8692c.1
                                      have p8692_1 := h8692c.2.1
                                      have p8692_2 := h8692c.2.2.1
                                      have p8692_3 := h8692c.2.2.2
                                      linarith only [h8081, h8531, h8631, h8684, h8685, h8689, h8691, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8692_1]
                                    · have p8692_0 := h8692c.1
                                      have p8692_1 := h8692c.2.1
                                      have p8692_2 := h8692c.2.2.1
                                      have p8692_3 := h8692c.2.2.2
                                      linarith only [h8081, hlam, p8692_0]
                                    · have p8692_0 := h8692c.1
                                      have p8692_1 := h8692c.2.1
                                      have p8692_2 := h8692c.2.2.1
                                      have p8692_3 := h8692c.2.2.2
                                      linarith only [h8530, hlam, p8692_1]
                                    · have p8692_0 := h8692c.1
                                      have p8692_1 := h8692c.2.1
                                      have p8692_2 := h8692c.2.2.1
                                      have p8692_3 := h8692c.2.2.2
                                      linarith only [h8629, hlam, p8692_0]
                                    · have p8692_0 := h8692c.1
                                      have p8692_1 := h8692c.2.1
                                      have p8692_2 := h8692c.2.2.1
                                      have p8692_3 := h8692c.2.2.2
                                      linarith only [h8630, hlam, p8692_1]
                                    · have p8692_0 := h8692c.1
                                      have p8692_1 := h8692c.2.1
                                      have p8692_2 := h8692c.2.2.1
                                      have p8692_3 := h8692c.2.2.2
                                      linarith only [hlam, p8692_0]
                                  · linarith only [h0, h8081, h8082, h8531, h8630, h8691, hc04, hc15, hlam, hphi, ht0b, ht5b]
                                · linarith only [h0, h8081, h8682, h8687, h8690, hlam]
                              · linarith only [h0, h8081, h8082, h8531, h8631, h8684, h8685, h8689, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h8631, h8685, h8688, hlam]
                          · linarith only [h7338, h8081, h8630, h8684, h8687, hc04, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h8081, h8082, h8531, h8684, h8685, h8686, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h8724 | h8724
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h8725 | h8725
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h8726 | h8726
                            · linarith only [h6253, h8081, h8684, h8685, h8726, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h0, h8081, h8631, h8684, h8726, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h0, h8081, h8630, h8631, h8684, h8685, h8725, hc04, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h8081, h8629, h8631, h8684, h8724, hc03, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h8081, h8530, h8684, hc02, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h8081, h8082, h8531, h8630, hlam]
            · linarith only [h0, h8081, h8082, h8629, hlam]
        · linarith only [h0, h8081, h8530, hlam]
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s10 m hb0 hb1 hb3 hb4 h0 h6253 h7338 h8081

end R2N4
