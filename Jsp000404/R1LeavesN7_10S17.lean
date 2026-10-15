import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_10S16

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x1_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h10681 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10682 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10683 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h10684 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h10685 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  rcases m.htr 1 4 5 (by decide) (by decide) with h11041 | h11041
  · rcases m.htr 2 3 4 (by decide) (by decide) with h11042 | h11042
    · linarith only [h0, h10685, h11042, h6874, h8886, hc01, hc12, hlam, hphi]
    · rcases m.htr 2 3 5 (by decide) (by decide) with h11044 | h11044
      · rcases m.htr 2 4 5 (by decide) (by decide) with h11045 | h11045
        · rcases m.htr 3 4 5 (by decide) (by decide) with h11046 | h11046
          · rcases h2bigk with h11047c | h11047c | h11047c | h11047c | h11047c | h11047c | h11047c | h11047c | h11047c | h11047c | h11047c | h11047c | h11047c | h11047c | h11047c | h11047c | h11047c | h11047c | h11047c | h11047c | h11047c | h11047c | h11047c | h11047c | h11047c
            · have p11047_0 := h11047c.1
              have p11047_1 := h11047c.2.1
              have p11047_2 := h11047c.2.2.1
              have p11047_3 := h11047c.2.2.2
              linarith only [hlam, p11047_0]
            · have p11047_0 := h11047c.1
              have p11047_1 := h11047c.2.1
              have p11047_2 := h11047c.2.2.1
              have p11047_3 := h11047c.2.2.2
              linarith only [h0, hlam, p11047_0]
            · have p11047_0 := h11047c.1
              have p11047_1 := h11047c.2.1
              have p11047_2 := h11047c.2.2.1
              have p11047_3 := h11047c.2.2.2
              rcases p11047_3 (m.d 0 2) (by simp) with h11050 | h11050
              · rcases p11047_3 (m.d 1 2) (by simp) with h11051 | h11051
                · rcases p11047_3 (m.d 2 3) (by simp) with h11052 | h11052
                  · linarith only [h11052, hlam, p11047_0]
                  · rcases p11047_3 (m.d 2 4) (by simp) with h11054 | h11054
                    · linarith only [h11054, h8887, hlam]
                    · linarith only [h11042, h11054, hlam]
                · linarith only [h10682, h11051, hlam]
              · linarith only [h11050, hlam, p11047_0]
            · have p11047_0 := h11047c.1
              have p11047_1 := h11047c.2.1
              have p11047_2 := h11047c.2.2.1
              have p11047_3 := h11047c.2.2.2
              rcases p11047_3 (m.d 0 2) (by simp) with h11059 | h11059
              · rcases p11047_3 (m.d 1 2) (by simp) with h11060 | h11060
                · rcases p11047_3 (m.d 2 3) (by simp) with h11061 | h11061
                  · linarith only [h11061, h8886, hlam]
                  · rcases p11047_3 (m.d 2 4) (by simp) with h11063 | h11063
                    · linarith only [h11063, hlam, p11047_0]
                    · rcases p11047_3 (m.d 2 5) (by simp) with h11065 | h11065
                      · linarith only [h11065, h8888, hlam]
                      · rcases h4bigk with h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c | h11067c
                        · have p11067_0 := h11067c.1
                          have p11067_1 := h11067c.2.1
                          have p11067_2 := h11067c.2.2.1
                          have p11067_3 := h11067c.2.2.2
                          linarith only [hlam, p11067_0]
                        · have p11067_0 := h11067c.1
                          have p11067_1 := h11067c.2.1
                          have p11067_2 := h11067c.2.2.1
                          have p11067_3 := h11067c.2.2.2
                          linarith only [h6874, hlam, p11067_1]
                        · have p11067_0 := h11067c.1
                          have p11067_1 := h11067c.2.1
                          have p11067_2 := h11067c.2.2.1
                          have p11067_3 := h11067c.2.2.2
                          linarith only [h11042, h11044, h11046, hc04, hc45, hlam, hphi, ht0b, ht5b, p11067_1]
                        · have p11067_0 := h11067c.1
                          have p11067_1 := h11067c.2.1
                          have p11067_2 := h11067c.2.2.1
                          have p11067_3 := h11067c.2.2.2
                          linarith only [h8889, hlam, p11067_1]
                        · have p11067_0 := h11067c.1
                          have p11067_1 := h11067c.2.1
                          have p11067_2 := h11067c.2.2.1
                          have p11067_3 := h11067c.2.2.2
                          rcases p11067_3 (m.d 0 4) (by simp) with h11072 | h11072
                          · rcases p11067_3 (m.d 1 4) (by simp) with h11073 | h11073
                            · rcases p11067_3 (m.d 2 4) (by simp) with h11074 | h11074
                              · linarith only [h11074, h8887, hlam]
                              · linarith only [h11045, h11074, hlam]
                            · linarith only [h11041, h11073, hlam]
                          · linarith only [h11072, hlam, p11067_0]
                        · have p11067_0 := h11067c.1
                          have p11067_1 := h11067c.2.1
                          have p11067_2 := h11067c.2.2.1
                          have p11067_3 := h11067c.2.2.2
                          linarith only [h10685, h6874, hc01, hc34, hlam, hphi, ht12, ht23, p11067_1]
                        · have p11067_0 := h11067c.1
                          have p11067_1 := h11067c.2.1
                          have p11067_2 := h11067c.2.2.1
                          have p11067_3 := h11067c.2.2.2
                          linarith only [hlam, p11067_0]
                        · have p11067_0 := h11067c.1
                          have p11067_1 := h11067c.2.1
                          have p11067_2 := h11067c.2.2.1
                          have p11067_3 := h11067c.2.2.2
                          linarith only [h10685, h11042, h11044, h11046, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p11067_1]
                        · have p11067_0 := h11067c.1
                          have p11067_1 := h11067c.2.1
                          have p11067_2 := h11067c.2.2.1
                          have p11067_3 := h11067c.2.2.2
                          linarith only [h10685, hlam, p11067_1]
                        · have p11067_0 := h11067c.1
                          have p11067_1 := h11067c.2.1
                          have p11067_2 := h11067c.2.2.1
                          have p11067_3 := h11067c.2.2.2
                          rcases p11067_3 (m.d 0 4) (by simp) with h11083 | h11083
                          · linarith only [h11083, h6874, hlam]
                          · linarith only [h10681, h11083, hlam]
                        · have p11067_0 := h11067c.1
                          have p11067_1 := h11067c.2.1
                          have p11067_2 := h11067c.2.2.1
                          have p11067_3 := h11067c.2.2.2
                          linarith only [h8887, hlam, p11067_0]
                        · have p11067_0 := h11067c.1
                          have p11067_1 := h11067c.2.1
                          have p11067_2 := h11067c.2.2.1
                          have p11067_3 := h11067c.2.2.2
                          linarith only [h10683, hlam, p11067_0]
                        · have p11067_0 := h11067c.1
                          have p11067_1 := h11067c.2.1
                          have p11067_2 := h11067c.2.2.1
                          have p11067_3 := h11067c.2.2.2
                          linarith only [hlam, p11067_0]
                        · have p11067_0 := h11067c.1
                          have p11067_1 := h11067c.2.1
                          have p11067_2 := h11067c.2.2.1
                          have p11067_3 := h11067c.2.2.2
                          linarith only [h11042, hlam, p11067_1]
                        · have p11067_0 := h11067c.1
                          have p11067_1 := h11067c.2.1
                          have p11067_2 := h11067c.2.2.1
                          have p11067_3 := h11067c.2.2.2
                          linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11047_1, p11067_1]
                        · have p11067_0 := h11067c.1
                          have p11067_1 := h11067c.2.1
                          have p11067_2 := h11067c.2.2.1
                          have p11067_3 := h11067c.2.2.2
                          linarith only [h6874, hc01, hc34, hlam, hphi, ht12, ht23, p11067_1]
                        · have p11067_0 := h11067c.1
                          have p11067_1 := h11067c.2.1
                          have p11067_2 := h11067c.2.2.1
                          have p11067_3 := h11067c.2.2.2
                          linarith only [h6874, hc01, hc34, hlam, hphi, ht12, ht23, p11067_1]
                        · have p11067_0 := h11067c.1
                          have p11067_1 := h11067c.2.1
                          have p11067_2 := h11067c.2.2.1
                          have p11067_3 := h11067c.2.2.2
                          linarith only [h11042, h11044, h11046, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p11067_1]
                        · have p11067_0 := h11067c.1
                          have p11067_1 := h11067c.2.1
                          have p11067_2 := h11067c.2.2.1
                          have p11067_3 := h11067c.2.2.2
                          linarith only [hlam, p11067_0]
                        · have p11067_0 := h11067c.1
                          have p11067_1 := h11067c.2.1
                          have p11067_2 := h11067c.2.2.1
                          have p11067_3 := h11067c.2.2.2
                          rcases p11067_3 (m.d 0 4) (by simp) with h11095 | h11095
                          · linarith only [h11095, h8889, hlam]
                          · linarith only [h10681, h11095, hlam]
                        · have p11067_0 := h11067c.1
                          have p11067_1 := h11067c.2.1
                          have p11067_2 := h11067c.2.2.1
                          have p11067_3 := h11067c.2.2.2
                          linarith only [h10681, hlam, p11067_0]
                        · have p11067_0 := h11067c.1
                          have p11067_1 := h11067c.2.1
                          have p11067_2 := h11067c.2.2.1
                          have p11067_3 := h11067c.2.2.2
                          linarith only [h11041, hlam, p11067_0]
                        · have p11067_0 := h11067c.1
                          have p11067_1 := h11067c.2.1
                          have p11067_2 := h11067c.2.2.1
                          have p11067_3 := h11067c.2.2.2
                          linarith only [h11045, hlam, p11067_0]
                        · have p11067_0 := h11067c.1
                          have p11067_1 := h11067c.2.1
                          have p11067_2 := h11067c.2.2.1
                          have p11067_3 := h11067c.2.2.2
                          linarith only [h11046, hlam, p11067_0]
                        · have p11067_0 := h11067c.1
                          have p11067_1 := h11067c.2.1
                          have p11067_2 := h11067c.2.2.1
                          have p11067_3 := h11067c.2.2.2
                          linarith only [hlam, p11067_0]
                · linarith only [h10683, h11060, hlam]
              · linarith only [h11059, hlam, p11047_0]
            · have p11047_0 := h11047c.1
              have p11047_1 := h11047c.2.1
              have p11047_2 := h11047c.2.2.1
              have p11047_3 := h11047c.2.2.2
              rcases p11047_3 (m.d 0 2) (by simp) with h11105 | h11105
              · rcases p11047_3 (m.d 1 2) (by simp) with h11106 | h11106
                · rcases p11047_3 (m.d 2 3) (by simp) with h11107 | h11107
                  · linarith only [h11107, h8886, hlam]
                  · linarith only [h11044, h11107, hlam]
                · linarith only [h10684, h11106, hlam]
              · linarith only [h11105, hlam, p11047_0]
            · have p11047_0 := h11047c.1
              have p11047_1 := h11047c.2.1
              have p11047_2 := h11047c.2.2.1
              have p11047_3 := h11047c.2.2.2
              linarith only [h11044, h11046, h8886, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11047_1]
            · have p11047_0 := h11047c.1
              have p11047_1 := h11047c.2.1
              have p11047_2 := h11047c.2.2.1
              have p11047_3 := h11047c.2.2.2
              linarith only [hlam, p11047_0]
            · have p11047_0 := h11047c.1
              have p11047_1 := h11047c.2.1
              have p11047_2 := h11047c.2.2.1
              have p11047_3 := h11047c.2.2.2
              rcases p11047_3 (m.d 0 2) (by simp) with h11114 | h11114
              · linarith only [h0, h11114, hlam]
              · linarith only [h11114, h8886, hlam]
            · have p11047_0 := h11047c.1
              have p11047_1 := h11047c.2.1
              have p11047_2 := h11047c.2.2.1
              have p11047_3 := h11047c.2.2.2
              rcases p11047_3 (m.d 0 2) (by simp) with h11117 | h11117
              · linarith only [h0, h11117, hlam]
              · linarith only [h11117, h8887, hlam]
            · have p11047_0 := h11047c.1
              have p11047_1 := h11047c.2.1
              have p11047_2 := h11047c.2.2.1
              have p11047_3 := h11047c.2.2.2
              rcases p11047_3 (m.d 0 2) (by simp) with h11120 | h11120
              · linarith only [h0, h11120, hlam]
              · linarith only [h11120, h8888, hlam]
            · have p11047_0 := h11047c.1
              have p11047_1 := h11047c.2.1
              have p11047_2 := h11047c.2.2.1
              have p11047_3 := h11047c.2.2.2
              linarith only [h8886, hlam, p11047_0]
            · have p11047_0 := h11047c.1
              have p11047_1 := h11047c.2.1
              have p11047_2 := h11047c.2.2.1
              have p11047_3 := h11047c.2.2.2
              linarith only [h10682, hlam, p11047_0]
            · have p11047_0 := h11047c.1
              have p11047_1 := h11047c.2.1
              have p11047_2 := h11047c.2.2.1
              have p11047_3 := h11047c.2.2.2
              linarith only [hlam, p11047_0]
            · have p11047_0 := h11047c.1
              have p11047_1 := h11047c.2.1
              have p11047_2 := h11047c.2.2.1
              have p11047_3 := h11047c.2.2.2
              linarith only [h11042, hlam, p11047_1]
            · have p11047_0 := h11047c.1
              have p11047_1 := h11047c.2.1
              have p11047_2 := h11047c.2.2.1
              have p11047_3 := h11047c.2.2.2
              rcases p11047_3 (m.d 0 2) (by simp) with h11127 | h11127
              · rcases p11047_3 (m.d 1 2) (by simp) with h11128 | h11128
                · rcases p11047_3 (m.d 2 3) (by simp) with h11129 | h11129
                  · rcases p11047_3 (m.d 2 4) (by simp) with h11130 | h11130
                    · rcases p11047_3 (m.d 2 5) (by simp) with h11131 | h11131
                      · linarith only [h11044, h11131, hlam]
                      · rcases h4bigk with h11133c | h11133c | h11133c | h11133c | h11133c | h11133c | h11133c | h11133c | h11133c | h11133c | h11133c | h11133c | h11133c | h11133c | h11133c | h11133c | h11133c | h11133c | h11133c | h11133c | h11133c | h11133c | h11133c | h11133c | h11133c
                        · have p11133_0 := h11133c.1
                          have p11133_1 := h11133c.2.1
                          have p11133_2 := h11133c.2.2.1
                          have p11133_3 := h11133c.2.2.2
                          linarith only [hlam, p11133_0]
                        · have p11133_0 := h11133c.1
                          have p11133_1 := h11133c.2.1
                          have p11133_2 := h11133c.2.2.1
                          have p11133_3 := h11133c.2.2.2
                          linarith only [h6874, hlam, p11133_1]
                        · have p11133_0 := h11133c.1
                          have p11133_1 := h11133c.2.1
                          have p11133_2 := h11133c.2.2.1
                          have p11133_3 := h11133c.2.2.2
                          linarith only [h11042, h11044, h11046, hc04, hc45, hlam, hphi, ht0b, ht5b, p11047_1, p11133_1]
                        · have p11133_0 := h11133c.1
                          have p11133_1 := h11133c.2.1
                          have p11133_2 := h11133c.2.2.1
                          have p11133_3 := h11133c.2.2.2
                          linarith only [h8889, hlam, p11133_1]
                        · have p11133_0 := h11133c.1
                          have p11133_1 := h11133c.2.1
                          have p11133_2 := h11133c.2.2.1
                          have p11133_3 := h11133c.2.2.2
                          rcases p11133_3 (m.d 0 4) (by simp) with h11138 | h11138
                          · rcases p11133_3 (m.d 1 4) (by simp) with h11139 | h11139
                            · rcases p11133_3 (m.d 2 4) (by simp) with h11140 | h11140
                              · linarith only [h11140, h8887, hlam]
                              · linarith only [h11045, h11140, hlam]
                            · linarith only [h11041, h11139, hlam]
                          · linarith only [h11138, hlam, p11133_0]
                        · have p11133_0 := h11133c.1
                          have p11133_1 := h11133c.2.1
                          have p11133_2 := h11133c.2.2.1
                          have p11133_3 := h11133c.2.2.2
                          linarith only [h10683, h6874, hc01, hc12, hlam, hphi, p11133_1]
                        · have p11133_0 := h11133c.1
                          have p11133_1 := h11133c.2.1
                          have p11133_2 := h11133c.2.2.1
                          have p11133_3 := h11133c.2.2.2
                          linarith only [hlam, p11133_0]
                        · have p11133_0 := h11133c.1
                          have p11133_1 := h11133c.2.1
                          have p11133_2 := h11133c.2.2.1
                          have p11133_3 := h11133c.2.2.2
                          linarith only [h10683, h11042, h11044, h11046, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11047_1, p11133_1]
                        · have p11133_0 := h11133c.1
                          have p11133_1 := h11133c.2.1
                          have p11133_2 := h11133c.2.2.1
                          have p11133_3 := h11133c.2.2.2
                          linarith only [h10685, hlam, p11133_1]
                        · have p11133_0 := h11133c.1
                          have p11133_1 := h11133c.2.1
                          have p11133_2 := h11133c.2.2.1
                          have p11133_3 := h11133c.2.2.2
                          rcases p11133_3 (m.d 0 4) (by simp) with h11149 | h11149
                          · linarith only [h11149, h6874, hlam]
                          · linarith only [h10681, h11149, hlam]
                        · have p11133_0 := h11133c.1
                          have p11133_1 := h11133c.2.1
                          have p11133_2 := h11133c.2.2.1
                          have p11133_3 := h11133c.2.2.2
                          linarith only [h8887, hlam, p11133_0]
                        · have p11133_0 := h11133c.1
                          have p11133_1 := h11133c.2.1
                          have p11133_2 := h11133c.2.2.1
                          have p11133_3 := h11133c.2.2.2
                          linarith only [h10683, hlam, p11133_0]
                        · have p11133_0 := h11133c.1
                          have p11133_1 := h11133c.2.1
                          have p11133_2 := h11133c.2.2.1
                          have p11133_3 := h11133c.2.2.2
                          linarith only [hlam, p11133_0]
                        · have p11133_0 := h11133c.1
                          have p11133_1 := h11133c.2.1
                          have p11133_2 := h11133c.2.2.1
                          have p11133_3 := h11133c.2.2.2
                          linarith only [h11042, hlam, p11133_1]
                        · have p11133_0 := h11133c.1
                          have p11133_1 := h11133c.2.1
                          have p11133_2 := h11133c.2.2.1
                          have p11133_3 := h11133c.2.2.2
                          linarith only [h8887, hc02, hc45, hlam, hphi, ht0b, ht5b, p11133_1]
                        · have p11133_0 := h11133c.1
                          have p11133_1 := h11133c.2.1
                          have p11133_2 := h11133c.2.2.1
                          have p11133_3 := h11133c.2.2.2
                          linarith only [h6874, hc01, hc34, hlam, hphi, ht12, ht23, p11133_1]
                        · have p11133_0 := h11133c.1
                          have p11133_1 := h11133c.2.1
                          have p11133_2 := h11133c.2.2.1
                          have p11133_3 := h11133c.2.2.2
                          linarith only [h6874, hc01, hc34, hlam, hphi, ht12, ht23, p11133_1]
                        · have p11133_0 := h11133c.1
                          have p11133_1 := h11133c.2.1
                          have p11133_2 := h11133c.2.2.1
                          have p11133_3 := h11133c.2.2.2
                          linarith only [h11042, h11044, h11046, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p11047_1, p11133_1]
                        · have p11133_0 := h11133c.1
                          have p11133_1 := h11133c.2.1
                          have p11133_2 := h11133c.2.2.1
                          have p11133_3 := h11133c.2.2.2
                          linarith only [hlam, p11133_0]
                        · have p11133_0 := h11133c.1
                          have p11133_1 := h11133c.2.1
                          have p11133_2 := h11133c.2.2.1
                          have p11133_3 := h11133c.2.2.2
                          rcases p11133_3 (m.d 0 4) (by simp) with h11161 | h11161
                          · linarith only [h11161, h8889, hlam]
                          · linarith only [h10681, h11161, hlam]
                        · have p11133_0 := h11133c.1
                          have p11133_1 := h11133c.2.1
                          have p11133_2 := h11133c.2.2.1
                          have p11133_3 := h11133c.2.2.2
                          linarith only [h10681, hlam, p11133_0]
                        · have p11133_0 := h11133c.1
                          have p11133_1 := h11133c.2.1
                          have p11133_2 := h11133c.2.2.1
                          have p11133_3 := h11133c.2.2.2
                          linarith only [h11041, hlam, p11133_0]
                        · have p11133_0 := h11133c.1
                          have p11133_1 := h11133c.2.1
                          have p11133_2 := h11133c.2.2.1
                          have p11133_3 := h11133c.2.2.2
                          linarith only [h11045, hlam, p11133_0]
                        · have p11133_0 := h11133c.1
                          have p11133_1 := h11133c.2.1
                          have p11133_2 := h11133c.2.2.1
                          have p11133_3 := h11133c.2.2.2
                          linarith only [h11046, hlam, p11133_0]
                        · have p11133_0 := h11133c.1
                          have p11133_1 := h11133c.2.1
                          have p11133_2 := h11133c.2.2.1
                          have p11133_3 := h11133c.2.2.2
                          linarith only [hlam, p11133_0]
                    · linarith only [h11045, h11130, hlam]
                  · linarith only [h11044, h11129, hlam]
                · linarith only [h10684, h11128, hlam]
              · linarith only [h11127, h8888, hlam]
            · have p11047_0 := h11047c.1
              have p11047_1 := h11047c.2.1
              have p11047_2 := h11047c.2.2.1
              have p11047_3 := h11047c.2.2.2
              linarith only [h8887, hlam, p11047_0]
            · have p11047_0 := h11047c.1
              have p11047_1 := h11047c.2.1
              have p11047_2 := h11047c.2.2.1
              have p11047_3 := h11047c.2.2.2
              linarith only [h10683, hlam, p11047_0]
            · have p11047_0 := h11047c.1
              have p11047_1 := h11047c.2.1
              have p11047_2 := h11047c.2.2.1
              have p11047_3 := h11047c.2.2.2
              linarith only [h0, h11044, h11046, h8887, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11047_1]
            · have p11047_0 := h11047c.1
              have p11047_1 := h11047c.2.1
              have p11047_2 := h11047c.2.2.1
              have p11047_3 := h11047c.2.2.2
              linarith only [hlam, p11047_0]
            · have p11047_0 := h11047c.1
              have p11047_1 := h11047c.2.1
              have p11047_2 := h11047c.2.2.1
              have p11047_3 := h11047c.2.2.2
              rcases p11047_3 (m.d 0 2) (by simp) with h11177 | h11177
              · rcases p11047_3 (m.d 1 2) (by simp) with h11178 | h11178
                · rcases p11047_3 (m.d 2 3) (by simp) with h11179 | h11179
                  · linarith only [h11042, h11179, hlam]
                  · linarith only [h11044, h11179, hlam]
                · linarith only [h10684, h11178, hlam]
              · linarith only [h11177, h8888, hlam]
            · have p11047_0 := h11047c.1
              have p11047_1 := h11047c.2.1
              have p11047_2 := h11047c.2.2.1
              have p11047_3 := h11047c.2.2.2
              linarith only [h8888, hlam, p11047_0]
            · have p11047_0 := h11047c.1
              have p11047_1 := h11047c.2.1
              have p11047_2 := h11047c.2.2.1
              have p11047_3 := h11047c.2.2.2
              linarith only [h10684, hlam, p11047_0]
            · have p11047_0 := h11047c.1
              have p11047_1 := h11047c.2.1
              have p11047_2 := h11047c.2.2.1
              have p11047_3 := h11047c.2.2.2
              linarith only [h11044, hlam, p11047_0]
            · have p11047_0 := h11047c.1
              have p11047_1 := h11047c.2.1
              have p11047_2 := h11047c.2.2.1
              have p11047_3 := h11047c.2.2.2
              linarith only [h11045, hlam, p11047_1]
            · have p11047_0 := h11047c.1
              have p11047_1 := h11047c.2.1
              have p11047_2 := h11047c.2.2.1
              have p11047_3 := h11047c.2.2.2
              linarith only [hlam, p11047_0]
          · linarith only [h10681, h11046, h8889, hlam]
        · linarith only [h11042, h11044, h11045, hlam]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h11191 | h11191
        · rcases m.htr 3 4 5 (by decide) (by decide) with h11192 | h11192
          · rcases h2bigk with h11193c | h11193c | h11193c | h11193c | h11193c | h11193c | h11193c | h11193c | h11193c | h11193c | h11193c | h11193c | h11193c | h11193c | h11193c | h11193c | h11193c | h11193c | h11193c | h11193c | h11193c | h11193c | h11193c | h11193c | h11193c
            · have p11193_0 := h11193c.1
              have p11193_1 := h11193c.2.1
              have p11193_2 := h11193c.2.2.1
              have p11193_3 := h11193c.2.2.2
              linarith only [hlam, p11193_0]
            · have p11193_0 := h11193c.1
              have p11193_1 := h11193c.2.1
              have p11193_2 := h11193c.2.2.1
              have p11193_3 := h11193c.2.2.2
              linarith only [h0, hlam, p11193_0]
            · have p11193_0 := h11193c.1
              have p11193_1 := h11193c.2.1
              have p11193_2 := h11193c.2.2.1
              have p11193_3 := h11193c.2.2.2
              rcases p11193_3 (m.d 0 2) (by simp) with h11196 | h11196
              · rcases p11193_3 (m.d 1 2) (by simp) with h11197 | h11197
                · rcases p11193_3 (m.d 2 3) (by simp) with h11198 | h11198
                  · linarith only [h11198, hlam, p11193_0]
                  · rcases p11193_3 (m.d 2 4) (by simp) with h11200 | h11200
                    · linarith only [h11200, h8887, hlam]
                    · linarith only [h11042, h11200, hlam]
                · linarith only [h10682, h11197, hlam]
              · linarith only [h11196, hlam, p11193_0]
            · have p11193_0 := h11193c.1
              have p11193_1 := h11193c.2.1
              have p11193_2 := h11193c.2.2.1
              have p11193_3 := h11193c.2.2.2
              rcases p11193_3 (m.d 0 2) (by simp) with h11205 | h11205
              · rcases p11193_3 (m.d 1 2) (by simp) with h11206 | h11206
                · rcases p11193_3 (m.d 2 3) (by simp) with h11207 | h11207
                  · linarith only [h11207, h8886, hlam]
                  · rcases p11193_3 (m.d 2 4) (by simp) with h11209 | h11209
                    · linarith only [h11209, hlam, p11193_0]
                    · rcases p11193_3 (m.d 2 5) (by simp) with h11211 | h11211
                      · linarith only [h11211, h8888, hlam]
                      · rcases h4bigk with h11213c | h11213c | h11213c | h11213c | h11213c | h11213c | h11213c | h11213c | h11213c | h11213c | h11213c | h11213c | h11213c | h11213c | h11213c | h11213c | h11213c | h11213c | h11213c | h11213c | h11213c | h11213c | h11213c | h11213c | h11213c
                        · have p11213_0 := h11213c.1
                          have p11213_1 := h11213c.2.1
                          have p11213_2 := h11213c.2.2.1
                          have p11213_3 := h11213c.2.2.2
                          linarith only [hlam, p11213_0]
                        · have p11213_0 := h11213c.1
                          have p11213_1 := h11213c.2.1
                          have p11213_2 := h11213c.2.2.1
                          have p11213_3 := h11213c.2.2.2
                          linarith only [h6874, hlam, p11213_1]
                        · have p11213_0 := h11213c.1
                          have p11213_1 := h11213c.2.1
                          have p11213_2 := h11213c.2.2.1
                          have p11213_3 := h11213c.2.2.2
                          linarith only [h10685, h11044, h11191, h6874, hc23, hc34, hlam, hphi, p11213_1]
                        · have p11213_0 := h11213c.1
                          have p11213_1 := h11213c.2.1
                          have p11213_2 := h11213c.2.2.1
                          have p11213_3 := h11213c.2.2.2
                          linarith only [h8889, hlam, p11213_1]
                        · have p11213_0 := h11213c.1
                          have p11213_1 := h11213c.2.1
                          have p11213_2 := h11213c.2.2.1
                          have p11213_3 := h11213c.2.2.2
                          rcases p11213_3 (m.d 0 4) (by simp) with h11218 | h11218
                          · rcases p11213_3 (m.d 1 4) (by simp) with h11219 | h11219
                            · rcases p11213_3 (m.d 2 4) (by simp) with h11220 | h11220
                              · linarith only [h11220, h8887, hlam]
                              · linarith only [h11191, h11220, hlam]
                            · linarith only [h11041, h11219, hlam]
                          · linarith only [h11218, hlam, p11213_0]
                        · have p11213_0 := h11213c.1
                          have p11213_1 := h11213c.2.1
                          have p11213_2 := h11213c.2.2.1
                          have p11213_3 := h11213c.2.2.2
                          linarith only [h10685, h6874, hc01, hc34, hlam, hphi, ht12, ht23, p11213_1]
                        · have p11213_0 := h11213c.1
                          have p11213_1 := h11213c.2.1
                          have p11213_2 := h11213c.2.2.1
                          have p11213_3 := h11213c.2.2.2
                          linarith only [hlam, p11213_0]
                        · have p11213_0 := h11213c.1
                          have p11213_1 := h11213c.2.1
                          have p11213_2 := h11213c.2.2.1
                          have p11213_3 := h11213c.2.2.2
                          linarith only [h10685, h11191, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p11213_1]
                        · have p11213_0 := h11213c.1
                          have p11213_1 := h11213c.2.1
                          have p11213_2 := h11213c.2.2.1
                          have p11213_3 := h11213c.2.2.2
                          linarith only [h10685, hlam, p11213_1]
                        · have p11213_0 := h11213c.1
                          have p11213_1 := h11213c.2.1
                          have p11213_2 := h11213c.2.2.1
                          have p11213_3 := h11213c.2.2.2
                          rcases p11213_3 (m.d 0 4) (by simp) with h11229 | h11229
                          · linarith only [h11229, h6874, hlam]
                          · linarith only [h10681, h11229, hlam]
                        · have p11213_0 := h11213c.1
                          have p11213_1 := h11213c.2.1
                          have p11213_2 := h11213c.2.2.1
                          have p11213_3 := h11213c.2.2.2
                          linarith only [h8887, hlam, p11213_0]
                        · have p11213_0 := h11213c.1
                          have p11213_1 := h11213c.2.1
                          have p11213_2 := h11213c.2.2.1
                          have p11213_3 := h11213c.2.2.2
                          linarith only [h10683, hlam, p11213_0]
                        · have p11213_0 := h11213c.1
                          have p11213_1 := h11213c.2.1
                          have p11213_2 := h11213c.2.2.1
                          have p11213_3 := h11213c.2.2.2
                          linarith only [hlam, p11213_0]
                        · have p11213_0 := h11213c.1
                          have p11213_1 := h11213c.2.1
                          have p11213_2 := h11213c.2.2.1
                          have p11213_3 := h11213c.2.2.2
                          linarith only [h11042, hlam, p11213_1]
                        · have p11213_0 := h11213c.1
                          have p11213_1 := h11213c.2.1
                          have p11213_2 := h11213c.2.2.1
                          have p11213_3 := h11213c.2.2.2
                          linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11193_1, p11213_1]
                        · have p11213_0 := h11213c.1
                          have p11213_1 := h11213c.2.1
                          have p11213_2 := h11213c.2.2.1
                          have p11213_3 := h11213c.2.2.2
                          linarith only [h8889, hc03, hc34, hlam, hphi, p11213_1]
                        · have p11213_0 := h11213c.1
                          have p11213_1 := h11213c.2.1
                          have p11213_2 := h11213c.2.2.1
                          have p11213_3 := h11213c.2.2.2
                          linarith only [h6874, hc01, hc34, hlam, hphi, ht12, ht23, p11213_1]
                        · have p11213_0 := h11213c.1
                          have p11213_1 := h11213c.2.1
                          have p11213_2 := h11213c.2.2.1
                          have p11213_3 := h11213c.2.2.2
                          linarith only [h11042, hc23, hc34, hlam, hphi, p11213_1]
                        · have p11213_0 := h11213c.1
                          have p11213_1 := h11213c.2.1
                          have p11213_2 := h11213c.2.2.1
                          have p11213_3 := h11213c.2.2.2
                          linarith only [hlam, p11213_0]
                        · have p11213_0 := h11213c.1
                          have p11213_1 := h11213c.2.1
                          have p11213_2 := h11213c.2.2.1
                          have p11213_3 := h11213c.2.2.2
                          rcases p11213_3 (m.d 0 4) (by simp) with h11241 | h11241
                          · linarith only [h11241, h8889, hlam]
                          · linarith only [h10681, h11241, hlam]
                        · have p11213_0 := h11213c.1
                          have p11213_1 := h11213c.2.1
                          have p11213_2 := h11213c.2.2.1
                          have p11213_3 := h11213c.2.2.2
                          linarith only [h10681, hlam, p11213_0]
                        · have p11213_0 := h11213c.1
                          have p11213_1 := h11213c.2.1
                          have p11213_2 := h11213c.2.2.1
                          have p11213_3 := h11213c.2.2.2
                          linarith only [h11041, hlam, p11213_0]
                        · have p11213_0 := h11213c.1
                          have p11213_1 := h11213c.2.1
                          have p11213_2 := h11213c.2.2.1
                          have p11213_3 := h11213c.2.2.2
                          linarith only [h11191, hlam, p11213_0]
                        · have p11213_0 := h11213c.1
                          have p11213_1 := h11213c.2.1
                          have p11213_2 := h11213c.2.2.1
                          have p11213_3 := h11213c.2.2.2
                          linarith only [h11192, hlam, p11213_0]
                        · have p11213_0 := h11213c.1
                          have p11213_1 := h11213c.2.1
                          have p11213_2 := h11213c.2.2.1
                          have p11213_3 := h11213c.2.2.2
                          linarith only [hlam, p11213_0]
                · linarith only [h10683, h11206, hlam]
              · linarith only [h11205, hlam, p11193_0]
            · have p11193_0 := h11193c.1
              have p11193_1 := h11193c.2.1
              have p11193_2 := h11193c.2.2.1
              have p11193_3 := h11193c.2.2.2
              rcases p11193_3 (m.d 0 2) (by simp) with h11251 | h11251
              · rcases p11193_3 (m.d 1 2) (by simp) with h11252 | h11252
                · rcases p11193_3 (m.d 2 3) (by simp) with h11253 | h11253
                  · linarith only [h11253, h8886, hlam]
                  · rcases p11193_3 (m.d 2 4) (by simp) with h11255 | h11255
                    · linarith only [h11255, h8887, hlam]
                    · linarith only [h11191, h11255, hlam]
                · linarith only [h10684, h11252, hlam]
              · linarith only [h11251, hlam, p11193_0]
            · have p11193_0 := h11193c.1
              have p11193_1 := h11193c.2.1
              have p11193_2 := h11193c.2.2.1
              have p11193_3 := h11193c.2.2.2
              linarith only [h11191, h8887, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11193_1]
            · have p11193_0 := h11193c.1
              have p11193_1 := h11193c.2.1
              have p11193_2 := h11193c.2.2.1
              have p11193_3 := h11193c.2.2.2
              linarith only [hlam, p11193_0]
            · have p11193_0 := h11193c.1
              have p11193_1 := h11193c.2.1
              have p11193_2 := h11193c.2.2.1
              have p11193_3 := h11193c.2.2.2
              rcases p11193_3 (m.d 0 2) (by simp) with h11262 | h11262
              · linarith only [h0, h11262, hlam]
              · linarith only [h11262, h8886, hlam]
            · have p11193_0 := h11193c.1
              have p11193_1 := h11193c.2.1
              have p11193_2 := h11193c.2.2.1
              have p11193_3 := h11193c.2.2.2
              rcases p11193_3 (m.d 0 2) (by simp) with h11265 | h11265
              · linarith only [h0, h11265, hlam]
              · linarith only [h11265, h8887, hlam]
            · have p11193_0 := h11193c.1
              have p11193_1 := h11193c.2.1
              have p11193_2 := h11193c.2.2.1
              have p11193_3 := h11193c.2.2.2
              rcases p11193_3 (m.d 0 2) (by simp) with h11268 | h11268
              · linarith only [h0, h11268, hlam]
              · linarith only [h11268, h8888, hlam]
            · have p11193_0 := h11193c.1
              have p11193_1 := h11193c.2.1
              have p11193_2 := h11193c.2.2.1
              have p11193_3 := h11193c.2.2.2
              linarith only [h8886, hlam, p11193_0]
            · have p11193_0 := h11193c.1
              have p11193_1 := h11193c.2.1
              have p11193_2 := h11193c.2.2.1
              have p11193_3 := h11193c.2.2.2
              linarith only [h10682, hlam, p11193_0]
            · have p11193_0 := h11193c.1
              have p11193_1 := h11193c.2.1
              have p11193_2 := h11193c.2.2.1
              have p11193_3 := h11193c.2.2.2
              linarith only [hlam, p11193_0]
            · have p11193_0 := h11193c.1
              have p11193_1 := h11193c.2.1
              have p11193_2 := h11193c.2.2.1
              have p11193_3 := h11193c.2.2.2
              linarith only [h11042, hlam, p11193_1]
            · have p11193_0 := h11193c.1
              have p11193_1 := h11193c.2.1
              have p11193_2 := h11193c.2.2.1
              have p11193_3 := h11193c.2.2.2
              linarith only [h11044, hlam, p11193_1]
            · have p11193_0 := h11193c.1
              have p11193_1 := h11193c.2.1
              have p11193_2 := h11193c.2.2.1
              have p11193_3 := h11193c.2.2.2
              linarith only [h8887, hlam, p11193_0]
            · have p11193_0 := h11193c.1
              have p11193_1 := h11193c.2.1
              have p11193_2 := h11193c.2.2.1
              have p11193_3 := h11193c.2.2.2
              linarith only [h10683, hlam, p11193_0]
            · have p11193_0 := h11193c.1
              have p11193_1 := h11193c.2.1
              have p11193_2 := h11193c.2.2.1
              have p11193_3 := h11193c.2.2.2
              rcases p11193_3 (m.d 0 2) (by simp) with h11278 | h11278
              · rcases p11193_3 (m.d 1 2) (by simp) with h11279 | h11279
                · rcases p11193_3 (m.d 2 3) (by simp) with h11280 | h11280
                  · linarith only [h11042, h11280, hlam]
                  · rcases p11193_3 (m.d 2 4) (by simp) with h11282 | h11282
                    · rcases p11193_3 (m.d 2 5) (by simp) with h11283 | h11283
                      · linarith only [h11191, h11283, hlam]
                      · linarith only [h11044, h11283, hlam]
                    · linarith only [h11042, h11282, hlam]
                · linarith only [h10682, h11279, hlam]
              · linarith only [h11278, h8886, hlam]
            · have p11193_0 := h11193c.1
              have p11193_1 := h11193c.2.1
              have p11193_2 := h11193c.2.2.1
              have p11193_3 := h11193c.2.2.2
              linarith only [hlam, p11193_0]
            · have p11193_0 := h11193c.1
              have p11193_1 := h11193c.2.1
              have p11193_2 := h11193c.2.2.1
              have p11193_3 := h11193c.2.2.2
              rcases p11193_3 (m.d 0 2) (by simp) with h11290 | h11290
              · rcases p11193_3 (m.d 1 2) (by simp) with h11291 | h11291
                · rcases p11193_3 (m.d 2 3) (by simp) with h11292 | h11292
                  · linarith only [h11042, h11292, hlam]
                  · rcases p11193_3 (m.d 2 4) (by simp) with h11294 | h11294
                    · rcases p11193_3 (m.d 2 5) (by simp) with h11295 | h11295
                      · linarith only [h11191, h11295, hlam]
                      · rcases h4bigk with h11297c | h11297c | h11297c | h11297c | h11297c | h11297c | h11297c | h11297c | h11297c | h11297c | h11297c | h11297c | h11297c | h11297c | h11297c | h11297c | h11297c | h11297c | h11297c | h11297c | h11297c | h11297c | h11297c | h11297c | h11297c
                        · have p11297_0 := h11297c.1
                          have p11297_1 := h11297c.2.1
                          have p11297_2 := h11297c.2.2.1
                          have p11297_3 := h11297c.2.2.2
                          linarith only [hlam, p11297_0]
                        · have p11297_0 := h11297c.1
                          have p11297_1 := h11297c.2.1
                          have p11297_2 := h11297c.2.2.1
                          have p11297_3 := h11297c.2.2.2
                          linarith only [h6874, hlam, p11297_1]
                        · have p11297_0 := h11297c.1
                          have p11297_1 := h11297c.2.1
                          have p11297_2 := h11297c.2.2.1
                          have p11297_3 := h11297c.2.2.2
                          linarith only [h11044, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11193_1, p11297_1]
                        · have p11297_0 := h11297c.1
                          have p11297_1 := h11297c.2.1
                          have p11297_2 := h11297c.2.2.1
                          have p11297_3 := h11297c.2.2.2
                          linarith only [h8889, hlam, p11297_1]
                        · have p11297_0 := h11297c.1
                          have p11297_1 := h11297c.2.1
                          have p11297_2 := h11297c.2.2.1
                          have p11297_3 := h11297c.2.2.2
                          rcases p11297_3 (m.d 0 4) (by simp) with h11302 | h11302
                          · rcases p11297_3 (m.d 1 4) (by simp) with h11303 | h11303
                            · rcases p11297_3 (m.d 2 4) (by simp) with h11304 | h11304
                              · linarith only [h11304, h8887, hlam]
                              · linarith only [h11191, h11304, hlam]
                            · linarith only [h11041, h11303, hlam]
                          · linarith only [h11302, hlam, p11297_0]
                        · have p11297_0 := h11297c.1
                          have p11297_1 := h11297c.2.1
                          have p11297_2 := h11297c.2.2.1
                          have p11297_3 := h11297c.2.2.2
                          linarith only [h0, h10685, h11044, h6874, h8887, hc01, hc12, hc23, hc34, hlam, hphi, p11193_1, p11297_1]
                        · have p11297_0 := h11297c.1
                          have p11297_1 := h11297c.2.1
                          have p11297_2 := h11297c.2.2.1
                          have p11297_3 := h11297c.2.2.2
                          linarith only [hlam, p11297_0]
                        · have p11297_0 := h11297c.1
                          have p11297_1 := h11297c.2.1
                          have p11297_2 := h11297c.2.2.1
                          have p11297_3 := h11297c.2.2.2
                          linarith only [h10685, h11044, hc23, hc34, hlam, hphi, p11193_1, p11297_1]
                        · have p11297_0 := h11297c.1
                          have p11297_1 := h11297c.2.1
                          have p11297_2 := h11297c.2.2.1
                          have p11297_3 := h11297c.2.2.2
                          linarith only [h10685, hlam, p11297_1]
                        · have p11297_0 := h11297c.1
                          have p11297_1 := h11297c.2.1
                          have p11297_2 := h11297c.2.2.1
                          have p11297_3 := h11297c.2.2.2
                          rcases p11297_3 (m.d 0 4) (by simp) with h11313 | h11313
                          · linarith only [h11313, h6874, hlam]
                          · linarith only [h10681, h11313, hlam]
                        · have p11297_0 := h11297c.1
                          have p11297_1 := h11297c.2.1
                          have p11297_2 := h11297c.2.2.1
                          have p11297_3 := h11297c.2.2.2
                          linarith only [h8887, hlam, p11297_0]
                        · have p11297_0 := h11297c.1
                          have p11297_1 := h11297c.2.1
                          have p11297_2 := h11297c.2.2.1
                          have p11297_3 := h11297c.2.2.2
                          linarith only [h10683, hlam, p11297_0]
                        · have p11297_0 := h11297c.1
                          have p11297_1 := h11297c.2.1
                          have p11297_2 := h11297c.2.2.1
                          have p11297_3 := h11297c.2.2.2
                          linarith only [hlam, p11297_0]
                        · have p11297_0 := h11297c.1
                          have p11297_1 := h11297c.2.1
                          have p11297_2 := h11297c.2.2.1
                          have p11297_3 := h11297c.2.2.2
                          linarith only [h11042, hlam, p11297_1]
                        · have p11297_0 := h11297c.1
                          have p11297_1 := h11297c.2.1
                          have p11297_2 := h11297c.2.2.1
                          have p11297_3 := h11297c.2.2.2
                          linarith only [h0, h8887, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11297_1]
                        · have p11297_0 := h11297c.1
                          have p11297_1 := h11297c.2.1
                          have p11297_2 := h11297c.2.2.1
                          have p11297_3 := h11297c.2.2.2
                          linarith only [h11044, h8887, hc23, hc34, hlam, hphi, p11193_1, p11297_1]
                        · have p11297_0 := h11297c.1
                          have p11297_1 := h11297c.2.1
                          have p11297_2 := h11297c.2.2.1
                          have p11297_3 := h11297c.2.2.2
                          linarith only [h0, h11044, h6874, h8887, hc01, hc12, hc23, hc34, hlam, hphi, p11193_1, p11297_1]
                        · have p11297_0 := h11297c.1
                          have p11297_1 := h11297c.2.1
                          have p11297_2 := h11297c.2.2.1
                          have p11297_3 := h11297c.2.2.2
                          linarith only [h11044, hc23, hc34, hlam, hphi, p11193_1, p11297_1]
                        · have p11297_0 := h11297c.1
                          have p11297_1 := h11297c.2.1
                          have p11297_2 := h11297c.2.2.1
                          have p11297_3 := h11297c.2.2.2
                          linarith only [hlam, p11297_0]
                        · have p11297_0 := h11297c.1
                          have p11297_1 := h11297c.2.1
                          have p11297_2 := h11297c.2.2.1
                          have p11297_3 := h11297c.2.2.2
                          rcases p11297_3 (m.d 0 4) (by simp) with h11325 | h11325
                          · linarith only [h11325, h8889, hlam]
                          · linarith only [h10681, h11325, hlam]
                        · have p11297_0 := h11297c.1
                          have p11297_1 := h11297c.2.1
                          have p11297_2 := h11297c.2.2.1
                          have p11297_3 := h11297c.2.2.2
                          linarith only [h10681, hlam, p11297_0]
                        · have p11297_0 := h11297c.1
                          have p11297_1 := h11297c.2.1
                          have p11297_2 := h11297c.2.2.1
                          have p11297_3 := h11297c.2.2.2
                          linarith only [h11041, hlam, p11297_0]
                        · have p11297_0 := h11297c.1
                          have p11297_1 := h11297c.2.1
                          have p11297_2 := h11297c.2.2.1
                          have p11297_3 := h11297c.2.2.2
                          linarith only [h11191, hlam, p11297_0]
                        · have p11297_0 := h11297c.1
                          have p11297_1 := h11297c.2.1
                          have p11297_2 := h11297c.2.2.1
                          have p11297_3 := h11297c.2.2.2
                          linarith only [h11192, hlam, p11297_0]
                        · have p11297_0 := h11297c.1
                          have p11297_1 := h11297c.2.1
                          have p11297_2 := h11297c.2.2.1
                          have p11297_3 := h11297c.2.2.2
                          linarith only [hlam, p11297_0]
                    · linarith only [h11191, h11294, hlam]
                · linarith only [h10684, h11291, hlam]
              · linarith only [h11290, h8888, hlam]
            · have p11193_0 := h11193c.1
              have p11193_1 := h11193c.2.1
              have p11193_2 := h11193c.2.2.1
              have p11193_3 := h11193c.2.2.2
              linarith only [h8888, hlam, p11193_0]
            · have p11193_0 := h11193c.1
              have p11193_1 := h11193c.2.1
              have p11193_2 := h11193c.2.2.1
              have p11193_3 := h11193c.2.2.2
              linarith only [h10684, hlam, p11193_0]
            · have p11193_0 := h11193c.1
              have p11193_1 := h11193c.2.1
              have p11193_2 := h11193c.2.2.1
              have p11193_3 := h11193c.2.2.2
              rcases p11193_3 (m.d 0 2) (by simp) with h11338 | h11338
              · rcases p11193_3 (m.d 1 2) (by simp) with h11339 | h11339
                · rcases p11193_3 (m.d 2 3) (by simp) with h11340 | h11340
                  · linarith only [h11044, h11340, hlam]
                  · rcases p11193_3 (m.d 2 4) (by simp) with h11342 | h11342
                    · rcases p11193_3 (m.d 2 5) (by simp) with h11343 | h11343
                      · rcases h4bigk with h11344c | h11344c | h11344c | h11344c | h11344c | h11344c | h11344c | h11344c | h11344c | h11344c | h11344c | h11344c | h11344c | h11344c | h11344c | h11344c | h11344c | h11344c | h11344c | h11344c | h11344c | h11344c | h11344c | h11344c | h11344c
                        · have p11344_0 := h11344c.1
                          have p11344_1 := h11344c.2.1
                          have p11344_2 := h11344c.2.2.1
                          have p11344_3 := h11344c.2.2.2
                          linarith only [hlam, p11344_0]
                        · have p11344_0 := h11344c.1
                          have p11344_1 := h11344c.2.1
                          have p11344_2 := h11344c.2.2.1
                          have p11344_3 := h11344c.2.2.2
                          linarith only [h6874, hlam, p11344_1]
                        · have p11344_0 := h11344c.1
                          have p11344_1 := h11344c.2.1
                          have p11344_2 := h11344c.2.2.1
                          have p11344_3 := h11344c.2.2.2
                          linarith only [h10685, h11042, h6874, hc23, hc34, hlam, hphi, p11344_1]
                        · have p11344_0 := h11344c.1
                          have p11344_1 := h11344c.2.1
                          have p11344_2 := h11344c.2.2.1
                          have p11344_3 := h11344c.2.2.2
                          linarith only [h8889, hlam, p11344_1]
                        · have p11344_0 := h11344c.1
                          have p11344_1 := h11344c.2.1
                          have p11344_2 := h11344c.2.2.1
                          have p11344_3 := h11344c.2.2.2
                          rcases p11344_3 (m.d 0 4) (by simp) with h11349 | h11349
                          · rcases p11344_3 (m.d 1 4) (by simp) with h11350 | h11350
                            · rcases p11344_3 (m.d 2 4) (by simp) with h11351 | h11351
                              · linarith only [h11351, h8887, hlam]
                              · linarith only [h11191, h11351, hlam]
                            · linarith only [h11041, h11350, hlam]
                          · linarith only [h11349, hlam, p11344_0]
                        · have p11344_0 := h11344c.1
                          have p11344_1 := h11344c.2.1
                          have p11344_2 := h11344c.2.2.1
                          have p11344_3 := h11344c.2.2.2
                          linarith only [h10685, h6874, hc01, hc34, hlam, hphi, ht12, ht23, p11344_1]
                        · have p11344_0 := h11344c.1
                          have p11344_1 := h11344c.2.1
                          have p11344_2 := h11344c.2.2.1
                          have p11344_3 := h11344c.2.2.2
                          linarith only [hlam, p11344_0]
                        · have p11344_0 := h11344c.1
                          have p11344_1 := h11344c.2.1
                          have p11344_2 := h11344c.2.2.1
                          have p11344_3 := h11344c.2.2.2
                          linarith only [h10685, h11191, hc23, hc34, hlam, hphi, p11193_1, p11344_1]
                        · have p11344_0 := h11344c.1
                          have p11344_1 := h11344c.2.1
                          have p11344_2 := h11344c.2.2.1
                          have p11344_3 := h11344c.2.2.2
                          linarith only [h10685, hlam, p11344_1]
                        · have p11344_0 := h11344c.1
                          have p11344_1 := h11344c.2.1
                          have p11344_2 := h11344c.2.2.1
                          have p11344_3 := h11344c.2.2.2
                          rcases p11344_3 (m.d 0 4) (by simp) with h11360 | h11360
                          · linarith only [h11360, h6874, hlam]
                          · linarith only [h10681, h11360, hlam]
                        · have p11344_0 := h11344c.1
                          have p11344_1 := h11344c.2.1
                          have p11344_2 := h11344c.2.2.1
                          have p11344_3 := h11344c.2.2.2
                          linarith only [h8887, hlam, p11344_0]
                        · have p11344_0 := h11344c.1
                          have p11344_1 := h11344c.2.1
                          have p11344_2 := h11344c.2.2.1
                          have p11344_3 := h11344c.2.2.2
                          linarith only [h10683, hlam, p11344_0]
                        · have p11344_0 := h11344c.1
                          have p11344_1 := h11344c.2.1
                          have p11344_2 := h11344c.2.2.1
                          have p11344_3 := h11344c.2.2.2
                          linarith only [hlam, p11344_0]
                        · have p11344_0 := h11344c.1
                          have p11344_1 := h11344c.2.1
                          have p11344_2 := h11344c.2.2.1
                          have p11344_3 := h11344c.2.2.2
                          linarith only [h11042, hlam, p11344_1]
                        · have p11344_0 := h11344c.1
                          have p11344_1 := h11344c.2.1
                          have p11344_2 := h11344c.2.2.1
                          have p11344_3 := h11344c.2.2.2
                          linarith only [h0, h8887, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11344_1]
                        · have p11344_0 := h11344c.1
                          have p11344_1 := h11344c.2.1
                          have p11344_2 := h11344c.2.2.1
                          have p11344_3 := h11344c.2.2.2
                          linarith only [h11191, h8887, hc23, hc34, hlam, hphi, p11193_1, p11344_1]
                        · have p11344_0 := h11344c.1
                          have p11344_1 := h11344c.2.1
                          have p11344_2 := h11344c.2.2.1
                          have p11344_3 := h11344c.2.2.2
                          linarith only [h0, h11191, h6874, h8887, hc01, hc12, hc23, hc34, hlam, hphi, p11193_1, p11344_1]
                        · have p11344_0 := h11344c.1
                          have p11344_1 := h11344c.2.1
                          have p11344_2 := h11344c.2.2.1
                          have p11344_3 := h11344c.2.2.2
                          linarith only [h11191, hc23, hc34, hlam, hphi, p11193_1, p11344_1]
                        · have p11344_0 := h11344c.1
                          have p11344_1 := h11344c.2.1
                          have p11344_2 := h11344c.2.2.1
                          have p11344_3 := h11344c.2.2.2
                          linarith only [hlam, p11344_0]
                        · have p11344_0 := h11344c.1
                          have p11344_1 := h11344c.2.1
                          have p11344_2 := h11344c.2.2.1
                          have p11344_3 := h11344c.2.2.2
                          rcases p11344_3 (m.d 0 4) (by simp) with h11372 | h11372
                          · linarith only [h11372, h8889, hlam]
                          · linarith only [h10681, h11372, hlam]
                        · have p11344_0 := h11344c.1
                          have p11344_1 := h11344c.2.1
                          have p11344_2 := h11344c.2.2.1
                          have p11344_3 := h11344c.2.2.2
                          linarith only [h10681, hlam, p11344_0]
                        · have p11344_0 := h11344c.1
                          have p11344_1 := h11344c.2.1
                          have p11344_2 := h11344c.2.2.1
                          have p11344_3 := h11344c.2.2.2
                          linarith only [h11041, hlam, p11344_0]
                        · have p11344_0 := h11344c.1
                          have p11344_1 := h11344c.2.1
                          have p11344_2 := h11344c.2.2.1
                          have p11344_3 := h11344c.2.2.2
                          linarith only [h11191, hlam, p11344_0]
                        · have p11344_0 := h11344c.1
                          have p11344_1 := h11344c.2.1
                          have p11344_2 := h11344c.2.2.1
                          have p11344_3 := h11344c.2.2.2
                          linarith only [h11192, hlam, p11344_0]
                        · have p11344_0 := h11344c.1
                          have p11344_1 := h11344c.2.1
                          have p11344_2 := h11344c.2.2.1
                          have p11344_3 := h11344c.2.2.2
                          linarith only [hlam, p11344_0]
                      · linarith only [h11044, h11343, hlam]
                    · linarith only [h11042, h11342, hlam]
                · linarith only [h10682, h11339, hlam]
              · linarith only [h11338, h8886, hlam]
            · have p11193_0 := h11193c.1
              have p11193_1 := h11193c.2.1
              have p11193_2 := h11193c.2.2.1
              have p11193_3 := h11193c.2.2.2
              linarith only [h11191, hlam, p11193_1]
            · have p11193_0 := h11193c.1
              have p11193_1 := h11193c.2.1
              have p11193_2 := h11193c.2.2.1
              have p11193_3 := h11193c.2.2.2
              linarith only [hlam, p11193_0]
          · linarith only [h10681, h11192, h8889, hlam]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h11387 | h11387
          · rcases h2bigk with h11388c | h11388c | h11388c | h11388c | h11388c | h11388c | h11388c | h11388c | h11388c | h11388c | h11388c | h11388c | h11388c | h11388c | h11388c | h11388c | h11388c | h11388c | h11388c | h11388c | h11388c | h11388c | h11388c | h11388c | h11388c
            · have p11388_0 := h11388c.1
              have p11388_1 := h11388c.2.1
              have p11388_2 := h11388c.2.2.1
              have p11388_3 := h11388c.2.2.2
              linarith only [hlam, p11388_0]
            · have p11388_0 := h11388c.1
              have p11388_1 := h11388c.2.1
              have p11388_2 := h11388c.2.2.1
              have p11388_3 := h11388c.2.2.2
              linarith only [h0, hlam, p11388_0]
            · have p11388_0 := h11388c.1
              have p11388_1 := h11388c.2.1
              have p11388_2 := h11388c.2.2.1
              have p11388_3 := h11388c.2.2.2
              rcases p11388_3 (m.d 0 2) (by simp) with h11391 | h11391
              · rcases p11388_3 (m.d 1 2) (by simp) with h11392 | h11392
                · rcases p11388_3 (m.d 2 3) (by simp) with h11393 | h11393
                  · linarith only [h11393, hlam, p11388_0]
                  · rcases p11388_3 (m.d 2 4) (by simp) with h11395 | h11395
                    · linarith only [h11395, h8887, hlam]
                    · linarith only [h11042, h11395, hlam]
                · linarith only [h10682, h11392, hlam]
              · linarith only [h11391, hlam, p11388_0]
            · have p11388_0 := h11388c.1
              have p11388_1 := h11388c.2.1
              have p11388_2 := h11388c.2.2.1
              have p11388_3 := h11388c.2.2.2
              rcases p11388_3 (m.d 0 2) (by simp) with h11400 | h11400
              · rcases p11388_3 (m.d 1 2) (by simp) with h11401 | h11401
                · rcases p11388_3 (m.d 2 3) (by simp) with h11402 | h11402
                  · linarith only [h11402, h8886, hlam]
                  · rcases p11388_3 (m.d 2 4) (by simp) with h11404 | h11404
                    · linarith only [h11404, hlam, p11388_0]
                    · rcases p11388_3 (m.d 2 5) (by simp) with h11406 | h11406
                      · linarith only [h11406, h8888, hlam]
                      · linarith only [h11191, h11406, hlam]
                · linarith only [h10683, h11401, hlam]
              · linarith only [h11400, hlam, p11388_0]
            · have p11388_0 := h11388c.1
              have p11388_1 := h11388c.2.1
              have p11388_2 := h11388c.2.2.1
              have p11388_3 := h11388c.2.2.2
              rcases p11388_3 (m.d 0 2) (by simp) with h11411 | h11411
              · rcases p11388_3 (m.d 1 2) (by simp) with h11412 | h11412
                · rcases p11388_3 (m.d 2 3) (by simp) with h11413 | h11413
                  · linarith only [h11413, h8886, hlam]
                  · rcases p11388_3 (m.d 2 4) (by simp) with h11415 | h11415
                    · linarith only [h11415, h8887, hlam]
                    · rcases p11388_3 (m.d 2 5) (by simp) with h11417 | h11417
                      · linarith only [h11417, hlam, p11388_0]
                      · rcases h4bigk with h11419c | h11419c | h11419c | h11419c | h11419c | h11419c | h11419c | h11419c | h11419c | h11419c | h11419c | h11419c | h11419c | h11419c | h11419c | h11419c | h11419c | h11419c | h11419c | h11419c | h11419c | h11419c | h11419c | h11419c | h11419c
                        · have p11419_0 := h11419c.1
                          have p11419_1 := h11419c.2.1
                          have p11419_2 := h11419c.2.2.1
                          have p11419_3 := h11419c.2.2.2
                          linarith only [hlam, p11419_0]
                        · have p11419_0 := h11419c.1
                          have p11419_1 := h11419c.2.1
                          have p11419_2 := h11419c.2.2.1
                          have p11419_3 := h11419c.2.2.2
                          linarith only [h6874, hlam, p11419_1]
                        · have p11419_0 := h11419c.1
                          have p11419_1 := h11419c.2.1
                          have p11419_2 := h11419c.2.2.1
                          have p11419_3 := h11419c.2.2.2
                          linarith only [h10685, h11042, h6874, hc23, hc34, hlam, hphi, p11419_1]
                        · have p11419_0 := h11419c.1
                          have p11419_1 := h11419c.2.1
                          have p11419_2 := h11419c.2.2.1
                          have p11419_3 := h11419c.2.2.2
                          linarith only [h8889, hlam, p11419_1]
                        · have p11419_0 := h11419c.1
                          have p11419_1 := h11419c.2.1
                          have p11419_2 := h11419c.2.2.1
                          have p11419_3 := h11419c.2.2.2
                          linarith only [h10685, h11042, h11191, h6874, hc23, hc34, hlam, hphi, p11419_1]
                        · have p11419_0 := h11419c.1
                          have p11419_1 := h11419c.2.1
                          have p11419_2 := h11419c.2.2.1
                          have p11419_3 := h11419c.2.2.2
                          linarith only [h10685, h6874, hc01, hc34, hlam, hphi, ht12, ht23, p11419_1]
                        · have p11419_0 := h11419c.1
                          have p11419_1 := h11419c.2.1
                          have p11419_2 := h11419c.2.2.1
                          have p11419_3 := h11419c.2.2.2
                          linarith only [hlam, p11419_0]
                        · have p11419_0 := h11419c.1
                          have p11419_1 := h11419c.2.1
                          have p11419_2 := h11419c.2.2.1
                          have p11419_3 := h11419c.2.2.2
                          linarith only [h10685, h11042, hc23, hc34, hlam, hphi, p11419_1]
                        · have p11419_0 := h11419c.1
                          have p11419_1 := h11419c.2.1
                          have p11419_2 := h11419c.2.2.1
                          have p11419_3 := h11419c.2.2.2
                          linarith only [h10685, hlam, p11419_1]
                        · have p11419_0 := h11419c.1
                          have p11419_1 := h11419c.2.1
                          have p11419_2 := h11419c.2.2.1
                          have p11419_3 := h11419c.2.2.2
                          linarith only [h10685, h11042, h11191, hc23, hc34, hlam, hphi, p11419_1]
                        · have p11419_0 := h11419c.1
                          have p11419_1 := h11419c.2.1
                          have p11419_2 := h11419c.2.2.1
                          have p11419_3 := h11419c.2.2.2
                          linarith only [h8887, hlam, p11419_0]
                        · have p11419_0 := h11419c.1
                          have p11419_1 := h11419c.2.1
                          have p11419_2 := h11419c.2.2.1
                          have p11419_3 := h11419c.2.2.2
                          linarith only [h10683, hlam, p11419_0]
                        · have p11419_0 := h11419c.1
                          have p11419_1 := h11419c.2.1
                          have p11419_2 := h11419c.2.2.1
                          have p11419_3 := h11419c.2.2.2
                          linarith only [hlam, p11419_0]
                        · have p11419_0 := h11419c.1
                          have p11419_1 := h11419c.2.1
                          have p11419_2 := h11419c.2.2.1
                          have p11419_3 := h11419c.2.2.2
                          linarith only [h11042, hlam, p11419_1]
                        · have p11419_0 := h11419c.1
                          have p11419_1 := h11419c.2.1
                          have p11419_2 := h11419c.2.2.1
                          have p11419_3 := h11419c.2.2.2
                          linarith only [h11191, hlam, p11419_0]
                        · have p11419_0 := h11419c.1
                          have p11419_1 := h11419c.2.1
                          have p11419_2 := h11419c.2.2.1
                          have p11419_3 := h11419c.2.2.2
                          linarith only [h10681, h11042, h11191, hc23, hc34, hlam, hphi, p11419_1]
                        · have p11419_0 := h11419c.1
                          have p11419_1 := h11419c.2.1
                          have p11419_2 := h11419c.2.2.1
                          have p11419_3 := h11419c.2.2.2
                          linarith only [h6874, hc01, hc34, hlam, hphi, ht12, ht23, p11419_1]
                        · have p11419_0 := h11419c.1
                          have p11419_1 := h11419c.2.1
                          have p11419_2 := h11419c.2.2.1
                          have p11419_3 := h11419c.2.2.2
                          linarith only [h11042, hc23, hc34, hlam, hphi, p11419_1]
                        · have p11419_0 := h11419c.1
                          have p11419_1 := h11419c.2.1
                          have p11419_2 := h11419c.2.2.1
                          have p11419_3 := h11419c.2.2.2
                          linarith only [hlam, p11419_0]
                        · have p11419_0 := h11419c.1
                          have p11419_1 := h11419c.2.1
                          have p11419_2 := h11419c.2.2.1
                          have p11419_3 := h11419c.2.2.2
                          linarith only [h11042, h11191, hc23, hc34, hlam, hphi, p11419_1]
                        · have p11419_0 := h11419c.1
                          have p11419_1 := h11419c.2.1
                          have p11419_2 := h11419c.2.2.1
                          have p11419_3 := h11419c.2.2.2
                          linarith only [h10681, hlam, p11419_0]
                        · have p11419_0 := h11419c.1
                          have p11419_1 := h11419c.2.1
                          have p11419_2 := h11419c.2.2.1
                          have p11419_3 := h11419c.2.2.2
                          linarith only [h11041, hlam, p11419_0]
                        · have p11419_0 := h11419c.1
                          have p11419_1 := h11419c.2.1
                          have p11419_2 := h11419c.2.2.1
                          have p11419_3 := h11419c.2.2.2
                          linarith only [h10681, h11042, h8887, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11419_1]
                        · have p11419_0 := h11419c.1
                          have p11419_1 := h11419c.2.1
                          have p11419_2 := h11419c.2.2.1
                          have p11419_3 := h11419c.2.2.2
                          linarith only [h11387, hlam, p11419_0]
                        · have p11419_0 := h11419c.1
                          have p11419_1 := h11419c.2.1
                          have p11419_2 := h11419c.2.2.1
                          have p11419_3 := h11419c.2.2.2
                          linarith only [hlam, p11419_0]
                · linarith only [h10684, h11412, hlam]
              · linarith only [h11411, hlam, p11388_0]
            · have p11388_0 := h11388c.1
              have p11388_1 := h11388c.2.1
              have p11388_2 := h11388c.2.2.1
              have p11388_3 := h11388c.2.2.2
              linarith only [h10681, h11042, h11191, h8887, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11388_1]
            · have p11388_0 := h11388c.1
              have p11388_1 := h11388c.2.1
              have p11388_2 := h11388c.2.2.1
              have p11388_3 := h11388c.2.2.2
              linarith only [hlam, p11388_0]
            · have p11388_0 := h11388c.1
              have p11388_1 := h11388c.2.1
              have p11388_2 := h11388c.2.2.1
              have p11388_3 := h11388c.2.2.2
              rcases p11388_3 (m.d 0 2) (by simp) with h11449 | h11449
              · linarith only [h0, h11449, hlam]
              · linarith only [h11449, h8886, hlam]
            · have p11388_0 := h11388c.1
              have p11388_1 := h11388c.2.1
              have p11388_2 := h11388c.2.2.1
              have p11388_3 := h11388c.2.2.2
              rcases p11388_3 (m.d 0 2) (by simp) with h11452 | h11452
              · linarith only [h0, h11452, hlam]
              · linarith only [h11452, h8887, hlam]
            · have p11388_0 := h11388c.1
              have p11388_1 := h11388c.2.1
              have p11388_2 := h11388c.2.2.1
              have p11388_3 := h11388c.2.2.2
              rcases p11388_3 (m.d 0 2) (by simp) with h11455 | h11455
              · linarith only [h0, h11455, hlam]
              · linarith only [h11455, h8888, hlam]
            · have p11388_0 := h11388c.1
              have p11388_1 := h11388c.2.1
              have p11388_2 := h11388c.2.2.1
              have p11388_3 := h11388c.2.2.2
              linarith only [h8886, hlam, p11388_0]
            · have p11388_0 := h11388c.1
              have p11388_1 := h11388c.2.1
              have p11388_2 := h11388c.2.2.1
              have p11388_3 := h11388c.2.2.2
              linarith only [h10682, hlam, p11388_0]
            · have p11388_0 := h11388c.1
              have p11388_1 := h11388c.2.1
              have p11388_2 := h11388c.2.2.1
              have p11388_3 := h11388c.2.2.2
              linarith only [hlam, p11388_0]
            · have p11388_0 := h11388c.1
              have p11388_1 := h11388c.2.1
              have p11388_2 := h11388c.2.2.1
              have p11388_3 := h11388c.2.2.2
              linarith only [h11042, hlam, p11388_1]
            · have p11388_0 := h11388c.1
              have p11388_1 := h11388c.2.1
              have p11388_2 := h11388c.2.2.1
              have p11388_3 := h11388c.2.2.2
              linarith only [h11044, hlam, p11388_1]
            · have p11388_0 := h11388c.1
              have p11388_1 := h11388c.2.1
              have p11388_2 := h11388c.2.2.1
              have p11388_3 := h11388c.2.2.2
              linarith only [h8887, hlam, p11388_0]
            · have p11388_0 := h11388c.1
              have p11388_1 := h11388c.2.1
              have p11388_2 := h11388c.2.2.1
              have p11388_3 := h11388c.2.2.2
              linarith only [h10683, hlam, p11388_0]
            · have p11388_0 := h11388c.1
              have p11388_1 := h11388c.2.1
              have p11388_2 := h11388c.2.2.1
              have p11388_3 := h11388c.2.2.2
              linarith only [h10681, h11191, h6874, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11388_1]
            · have p11388_0 := h11388c.1
              have p11388_1 := h11388c.2.1
              have p11388_2 := h11388c.2.2.1
              have p11388_3 := h11388c.2.2.2
              linarith only [hlam, p11388_0]
            · have p11388_0 := h11388c.1
              have p11388_1 := h11388c.2.1
              have p11388_2 := h11388c.2.2.1
              have p11388_3 := h11388c.2.2.2
              linarith only [h11191, hlam, p11388_0]
            · have p11388_0 := h11388c.1
              have p11388_1 := h11388c.2.1
              have p11388_2 := h11388c.2.2.1
              have p11388_3 := h11388c.2.2.2
              linarith only [h8888, hlam, p11388_0]
            · have p11388_0 := h11388c.1
              have p11388_1 := h11388c.2.1
              have p11388_2 := h11388c.2.2.1
              have p11388_3 := h11388c.2.2.2
              linarith only [h10684, hlam, p11388_0]
            · have p11388_0 := h11388c.1
              have p11388_1 := h11388c.2.1
              have p11388_2 := h11388c.2.2.1
              have p11388_3 := h11388c.2.2.2
              linarith only [h10681, h10685, h11191, h6874, hc23, hc34, hlam, hphi, p11388_1]
            · have p11388_0 := h11388c.1
              have p11388_1 := h11388c.2.1
              have p11388_2 := h11388c.2.2.1
              have p11388_3 := h11388c.2.2.2
              linarith only [h10681, h10685, h11042, h11191, h6874, hc23, hc34, hlam, hphi, p11388_1]
            · have p11388_0 := h11388c.1
              have p11388_1 := h11388c.2.1
              have p11388_2 := h11388c.2.2.1
              have p11388_3 := h11388c.2.2.2
              linarith only [hlam, p11388_0]
          · linarith only [h10681, h10685, h11387, h6874, hlam]
  · linarith only [h10681, h11041, h6874, hlam]

set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x1_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h10681 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10682 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10683 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h10684 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  rcases m.htr 1 3 4 (by decide) (by decide) with h10685 | h10685
  · exact r1l7_12_24_L_I_H_I_s10_x1_x0_x0_x0_x0_x0 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h10681 h10682 h10683 h10684 h10685
  · exact r1l7_12_24_L_I_H_I_s10_x1_x0_x0_x0_x0_x1 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h10681 h10682 h10683 h10684 h10685

set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x1_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h10681 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10682 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10683 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h10684 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  linarith only [h0, h10684, h8888, hlam]

set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x1_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h10681 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10682 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10683 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  rcases m.htr 1 2 5 (by decide) (by decide) with h10684 | h10684
  · exact r1l7_12_24_L_I_H_I_s10_x1_x0_x0_x0_x0 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h10681 h10682 h10683 h10684
  · exact r1l7_12_24_L_I_H_I_s10_x1_x0_x0_x0_x1 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h10681 h10682 h10683 h10684

set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x1_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h10681 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10682 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10683 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  linarith only [h0, h10683, h8887, hlam]

set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x1_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h10681 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10682 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  rcases m.htr 1 2 4 (by decide) (by decide) with h10683 | h10683
  · exact r1l7_12_24_L_I_H_I_s10_x1_x0_x0_x0 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h10681 h10682 h10683
  · exact r1l7_12_24_L_I_H_I_s10_x1_x0_x0_x1 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h10681 h10682 h10683

set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x1_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h10681 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10682 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  linarith only [h0, h10682, h8886, hlam]

set_option maxHeartbeats 6502000 in
set_option maxHeartbeats 6502000 in
theorem r1l7_12_24_L_I_H_I_s10_x1_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg8887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg8888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8889 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h10681 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h6874 := hg6874
  have h8886 := hg8886
  have h8887 := hg8887
  have h8888 := hg8888
  rcases m.htr 1 2 3 (by decide) (by decide) with h10682 | h10682
  · exact r1l7_12_24_L_I_H_I_s10_x1_x0_x0 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h10681 h10682
  · exact r1l7_12_24_L_I_H_I_s10_x1_x0_x1 m hb2 hb4 hg0 hg6874 hg8886 hg8887 hg8888 h8889 h10681 h10682

end R2N4
