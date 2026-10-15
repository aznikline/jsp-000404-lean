import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_49S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5790000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1519 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1521 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1523 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1525 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1526 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1527 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1528 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1529 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1530 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1531 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h1532 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h1533 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1534 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1535 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1536 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h1537 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 2 3 5 (by decide) (by decide) with h2056 | h2056
  · linarith only [h0, h1525, h1528, h1537, h2056, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
  · rcases m.htr 2 4 5 (by decide) (by decide) with h2058 | h2058
    · rcases m.htr 3 4 5 (by decide) (by decide) with h2059 | h2059
      · rcases h2bigk with h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c | h2060c
        · have p2060_0 := h2060c.1
          have p2060_1 := h2060c.2.1
          have p2060_2 := h2060c.2.2.1
          have p2060_3 := h2060c.2.2.2
          linarith only [hlam, p2060_0]
        · have p2060_0 := h2060c.1
          have p2060_1 := h2060c.2.1
          have p2060_2 := h2060c.2.2.1
          have p2060_3 := h2060c.2.2.2
          linarith only [h0, hlam, p2060_0]
        · have p2060_0 := h2060c.1
          have p2060_1 := h2060c.2.1
          have p2060_2 := h2060c.2.2.1
          have p2060_3 := h2060c.2.2.2
          rcases p2060_3 (m.d 0 2) (by simp) with h2063 | h2063
          · rcases p2060_3 (m.d 1 2) (by simp) with h2064 | h2064
            · rcases p2060_3 (m.d 2 3) (by simp) with h2065 | h2065
              · linarith only [h2065, hlam, p2060_0]
              · rcases p2060_3 (m.d 2 4) (by simp) with h2067 | h2067
                · linarith only [h1526, h2067, hlam]
                · linarith only [h1537, h2067, hlam]
            · linarith only [h1531, h2064, hlam]
          · linarith only [h2063, hlam, p2060_0]
        · have p2060_0 := h2060c.1
          have p2060_1 := h2060c.2.1
          have p2060_2 := h2060c.2.2.1
          have p2060_3 := h2060c.2.2.2
          linarith only [h0, h2058, hc12, hlam, hphi, ht01, ht0b, ht5b, p2060_1, u5ehi4]
        · have p2060_0 := h2060c.1
          have p2060_1 := h2060c.2.1
          have p2060_2 := h2060c.2.2.1
          have p2060_3 := h2060c.2.2.2
          rcases p2060_3 (m.d 0 2) (by simp) with h2073 | h2073
          · rcases p2060_3 (m.d 1 2) (by simp) with h2074 | h2074
            · rcases p2060_3 (m.d 2 3) (by simp) with h2075 | h2075
              · linarith only [h1525, h2075, hlam]
              · rcases p2060_3 (m.d 2 4) (by simp) with h2077 | h2077
                · linarith only [h1526, h2077, hlam]
                · linarith only [h2058, h2077, hlam]
            · linarith only [h1533, h2074, hlam]
          · linarith only [h2073, hlam, p2060_0]
        · have p2060_0 := h2060c.1
          have p2060_1 := h2060c.2.1
          have p2060_2 := h2060c.2.2.1
          have p2060_3 := h2060c.2.2.2
          linarith only [h1525, h1528, h2056, h2059, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2060_1]
        · have p2060_0 := h2060c.1
          have p2060_1 := h2060c.2.1
          have p2060_2 := h2060c.2.2.1
          have p2060_3 := h2060c.2.2.2
          linarith only [hlam, p2060_0]
        · have p2060_0 := h2060c.1
          have p2060_1 := h2060c.2.1
          have p2060_2 := h2060c.2.2.1
          have p2060_3 := h2060c.2.2.2
          rcases p2060_3 (m.d 0 2) (by simp) with h2084 | h2084
          · linarith only [h0, h2084, hlam]
          · linarith only [h1525, h2084, hlam]
        · have p2060_0 := h2060c.1
          have p2060_1 := h2060c.2.1
          have p2060_2 := h2060c.2.2.1
          have p2060_3 := h2060c.2.2.2
          linarith only [h2058, hc12, hlam, hphi, ht01, ht0b, ht5b, p2060_1, u5ehi4]
        · have p2060_0 := h2060c.1
          have p2060_1 := h2060c.2.1
          have p2060_2 := h2060c.2.2.1
          have p2060_3 := h2060c.2.2.2
          rcases p2060_3 (m.d 0 2) (by simp) with h2088 | h2088
          · linarith only [h0, h2088, hlam]
          · linarith only [h1527, h2088, hlam]
        · have p2060_0 := h2060c.1
          have p2060_1 := h2060c.2.1
          have p2060_2 := h2060c.2.2.1
          have p2060_3 := h2060c.2.2.2
          linarith only [h1525, hlam, p2060_0]
        · have p2060_0 := h2060c.1
          have p2060_1 := h2060c.2.1
          have p2060_2 := h2060c.2.2.1
          have p2060_3 := h2060c.2.2.2
          linarith only [h1531, hlam, p2060_0]
        · have p2060_0 := h2060c.1
          have p2060_1 := h2060c.2.1
          have p2060_2 := h2060c.2.2.1
          have p2060_3 := h2060c.2.2.2
          linarith only [hlam, p2060_0]
        · have p2060_0 := h2060c.1
          have p2060_1 := h2060c.2.1
          have p2060_2 := h2060c.2.2.1
          have p2060_3 := h2060c.2.2.2
          linarith only [h1537, hlam, p2060_1]
        · have p2060_0 := h2060c.1
          have p2060_1 := h2060c.2.1
          have p2060_2 := h2060c.2.2.1
          have p2060_3 := h2060c.2.2.2
          linarith only [h2056, hlam, p2060_1]
        · have p2060_0 := h2060c.1
          have p2060_1 := h2060c.2.1
          have p2060_2 := h2060c.2.2.1
          have p2060_3 := h2060c.2.2.2
          linarith only [h1526, hlam, p2060_0]
        · have p2060_0 := h2060c.1
          have p2060_1 := h2060c.2.1
          have p2060_2 := h2060c.2.2.1
          have p2060_3 := h2060c.2.2.2
          linarith only [h1532, hlam, p2060_0]
        · have p2060_0 := h2060c.1
          have p2060_1 := h2060c.2.1
          have p2060_2 := h2060c.2.2.1
          have p2060_3 := h2060c.2.2.2
          rcases p2060_3 (m.d 0 2) (by simp) with h2098 | h2098
          · rcases p2060_3 (m.d 1 2) (by simp) with h2099 | h2099
            · rcases p2060_3 (m.d 2 3) (by simp) with h2100 | h2100
              · linarith only [h1537, h2100, hlam]
              · rcases p2060_3 (m.d 2 4) (by simp) with h2102 | h2102
                · rcases p2060_3 (m.d 2 5) (by simp) with h2103 | h2103
                  · linarith only [h2058, h2103, hlam]
                  · linarith only [h2056, h2103, hlam]
                · linarith only [h1537, h2102, hlam]
            · linarith only [h1531, h2099, hlam]
          · linarith only [h1525, h2098, hlam]
        · have p2060_0 := h2060c.1
          have p2060_1 := h2060c.2.1
          have p2060_2 := h2060c.2.2.1
          have p2060_3 := h2060c.2.2.2
          linarith only [hlam, p2060_0]
        · have p2060_0 := h2060c.1
          have p2060_1 := h2060c.2.1
          have p2060_2 := h2060c.2.2.1
          have p2060_3 := h2060c.2.2.2
          linarith only [h1525, h1528, h1537, hc02, hlam, hphi, ht0b, ht5b, p2060_1, u5ehi2]
        · have p2060_0 := h2060c.1
          have p2060_1 := h2060c.2.1
          have p2060_2 := h2060c.2.2.1
          have p2060_3 := h2060c.2.2.2
          linarith only [h1527, hlam, p2060_0]
        · have p2060_0 := h2060c.1
          have p2060_1 := h2060c.2.1
          have p2060_2 := h2060c.2.2.1
          have p2060_3 := h2060c.2.2.2
          linarith only [h1533, hlam, p2060_0]
        · have p2060_0 := h2060c.1
          have p2060_1 := h2060c.2.1
          have p2060_2 := h2060c.2.2.1
          have p2060_3 := h2060c.2.2.2
          rcases p2060_3 (m.d 0 2) (by simp) with h2113 | h2113
          · rcases p2060_3 (m.d 1 2) (by simp) with h2114 | h2114
            · rcases p2060_3 (m.d 2 3) (by simp) with h2115 | h2115
              · linarith only [h2056, h2115, hlam]
              · rcases p2060_3 (m.d 2 4) (by simp) with h2117 | h2117
                · rcases p2060_3 (m.d 2 5) (by simp) with h2118 | h2118
                  · rcases h2emax with h2119 | h2119 | h2119 | h2119 | h2119
                    · linarith only [h1525, h1528, h1537, h2058, h2119, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2060_1]
                    · linarith only [h0, h1525, h1528, h1537, h2058, h2119, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2060_1]
                    · rcases h4bigk with h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c | h2122c
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [hlam, p2122_0]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h1521, hlam, p2122_1]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h1525, h1528, h2058, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2060_1, p2122_1]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h0, h1525, h1528, h1537, h2058, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2060_1, p2122_1]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        rcases p2122_3 (m.d 0 4) (by simp) with h2127 | h2127
                        · rcases p2122_3 (m.d 1 4) (by simp) with h2128 | h2128
                          · rcases p2122_3 (m.d 2 4) (by simp) with h2129 | h2129
                            · linarith only [h1526, h2129, hlam]
                            · linarith only [h2058, h2129, hlam]
                          · linarith only [h1536, h2128, hlam]
                        · linarith only [h2127, hlam, p2122_0]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h1521, h1531, h1534, hc12, hlam, hphi, p2122_1, u1ehi0]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [hlam, p2122_0]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h1531, h1534, h2058, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2060_1, p2122_1]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h1531, h1534, h1537, h2058, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2060_1, p2122_1]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        rcases p2122_3 (m.d 0 4) (by simp) with h2138 | h2138
                        · linarith only [h1521, h2138, hlam]
                        · linarith only [h1530, h2138, hlam]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h1526, hlam, p2122_0]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h1532, hlam, p2122_0]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [hlam, p2122_0]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h1537, hlam, p2122_1]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h0, h1526, hc12, hlam, hphi, ht01, ht0b, ht5b, p2122_1, u5ehi4]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h1528, hlam, p2122_0]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h1534, hlam, p2122_0]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h0, h1525, h1528, h2058, hc12, hlam, hphi, ht01, ht0b, ht5b, p2122_1, u5ehi4]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [hlam, p2122_0]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h0, h1525, h1528, hc12, hlam, hphi, ht01, ht0b, ht5b, p2122_1, u5ehi4]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h1530, hlam, p2122_0]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h1536, hlam, p2122_0]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h2058, hlam, p2122_0]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [h2059, hlam, p2122_0]
                      · have p2122_0 := h2122c.1
                        have p2122_1 := h2122c.2.1
                        have p2122_2 := h2122c.2.2.1
                        have p2122_3 := h2122c.2.2.2
                        linarith only [hlam, p2122_0]
                    · linarith only [h2058, h2119, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2060_1]
                    · linarith only [h2119, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2060_1]
                  · linarith only [h2056, h2118, hlam]
                · linarith only [h1537, h2117, hlam]
            · linarith only [h1531, h2114, hlam]
          · linarith only [h1525, h2113, hlam]
        · have p2060_0 := h2060c.1
          have p2060_1 := h2060c.2.1
          have p2060_2 := h2060c.2.2.1
          have p2060_3 := h2060c.2.2.2
          linarith only [h2058, hlam, p2060_1]
        · have p2060_0 := h2060c.1
          have p2060_1 := h2060c.2.1
          have p2060_2 := h2060c.2.2.1
          have p2060_3 := h2060c.2.2.2
          linarith only [hlam, p2060_0]
      · linarith only [h1537, h2058, h2059, hlam]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h2165 | h2165
      · rcases h2bigk with h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c | h2166c
        · have p2166_0 := h2166c.1
          have p2166_1 := h2166c.2.1
          have p2166_2 := h2166c.2.2.1
          have p2166_3 := h2166c.2.2.2
          linarith only [hlam, p2166_0]
        · have p2166_0 := h2166c.1
          have p2166_1 := h2166c.2.1
          have p2166_2 := h2166c.2.2.1
          have p2166_3 := h2166c.2.2.2
          linarith only [h0, hlam, p2166_0]
        · have p2166_0 := h2166c.1
          have p2166_1 := h2166c.2.1
          have p2166_2 := h2166c.2.2.1
          have p2166_3 := h2166c.2.2.2
          linarith only [h1525, h1528, h1537, h2058, h2165, hlam, p2166_2]
        · have p2166_0 := h2166c.1
          have p2166_1 := h2166c.2.1
          have p2166_2 := h2166c.2.2.1
          have p2166_3 := h2166c.2.2.2
          linarith only [h1525, h1528, h2058, h2165, hlam, p2166_2]
        · have p2166_0 := h2166c.1
          have p2166_1 := h2166c.2.1
          have p2166_2 := h2166c.2.2.1
          have p2166_3 := h2166c.2.2.2
          rcases p2166_3 (m.d 0 2) (by simp) with h2171 | h2171
          · rcases p2166_3 (m.d 1 2) (by simp) with h2172 | h2172
            · rcases p2166_3 (m.d 2 3) (by simp) with h2173 | h2173
              · linarith only [h1525, h2173, hlam]
              · rcases p2166_3 (m.d 2 4) (by simp) with h2175 | h2175
                · linarith only [h1526, h2175, hlam]
                · rcases p2166_3 (m.d 2 5) (by simp) with h2177 | h2177
                  · linarith only [h2177, hlam, p2166_0]
                  · rcases h2emax with h2179 | h2179 | h2179 | h2179 | h2179
                    · linarith only [h1525, h1528, h1537, h2058, h2165, h2179, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h0, h1525, h1528, h1537, h2058, h2165, h2179, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases h4bigk with h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c | h2182c
                      · have p2182_0 := h2182c.1
                        have p2182_1 := h2182c.2.1
                        have p2182_2 := h2182c.2.2.1
                        have p2182_3 := h2182c.2.2.2
                        linarith only [hlam, p2182_0]
                      · have p2182_0 := h2182c.1
                        have p2182_1 := h2182c.2.1
                        have p2182_2 := h2182c.2.2.1
                        have p2182_3 := h2182c.2.2.2
                        linarith only [h1521, hlam, p2182_1]
                      · have p2182_0 := h2182c.1
                        have p2182_1 := h2182c.2.1
                        have p2182_2 := h2182c.2.2.1
                        have p2182_3 := h2182c.2.2.2
                        rcases p2182_3 (m.d 0 4) (by simp) with h2185 | h2185
                        · rcases p2182_3 (m.d 1 4) (by simp) with h2186 | h2186
                          · rcases p2182_3 (m.d 2 4) (by simp) with h2187 | h2187
                            · linarith only [h1526, h2187, hlam]
                            · rcases p2182_3 (m.d 3 4) (by simp) with h2189 | h2189
                              · linarith only [h1528, h2189, hlam]
                              · linarith only [h1537, h2189, hlam]
                          · linarith only [h1532, h2186, hlam]
                        · linarith only [h1526, h2185, hlam]
                      · have p2182_0 := h2182c.1
                        have p2182_1 := h2182c.2.1
                        have p2182_2 := h2182c.2.2.1
                        have p2182_3 := h2182c.2.2.2
                        linarith only [h1537, h2058, h2165, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2182_1]
                      · have p2182_0 := h2182c.1
                        have p2182_1 := h2182c.2.1
                        have p2182_2 := h2182c.2.2.1
                        have p2182_3 := h2182c.2.2.2
                        rcases p2182_3 (m.d 0 4) (by simp) with h2195 | h2195
                        · rcases p2182_3 (m.d 1 4) (by simp) with h2196 | h2196
                          · rcases p2182_3 (m.d 2 4) (by simp) with h2197 | h2197
                            · linarith only [h1526, h2197, hlam]
                            · rcases p2182_3 (m.d 3 4) (by simp) with h2199 | h2199
                              · linarith only [h1528, h2199, hlam]
                              · linarith only [h2165, h2199, hlam]
                          · linarith only [h1536, h2196, hlam]
                        · linarith only [h2195, hlam, p2182_0]
                      · have p2182_0 := h2182c.1
                        have p2182_1 := h2182c.2.1
                        have p2182_2 := h2182c.2.2.1
                        have p2182_3 := h2182c.2.2.2
                        linarith only [h1521, h1531, h1534, hc12, hlam, hphi, p2182_1, u1ehi0]
                      · have p2182_0 := h2182c.1
                        have p2182_1 := h2182c.2.1
                        have p2182_2 := h2182c.2.2.1
                        have p2182_3 := h2182c.2.2.2
                        linarith only [hlam, p2182_0]
                      · have p2182_0 := h2182c.1
                        have p2182_1 := h2182c.2.1
                        have p2182_2 := h2182c.2.2.1
                        have p2182_3 := h2182c.2.2.2
                        rcases p2182_3 (m.d 0 4) (by simp) with h2206 | h2206
                        · linarith only [h1521, h2206, hlam]
                        · linarith only [h1526, h2206, hlam]
                      · have p2182_0 := h2182c.1
                        have p2182_1 := h2182c.2.1
                        have p2182_2 := h2182c.2.2.1
                        have p2182_3 := h2182c.2.2.2
                        linarith only [h2058, h2165, hc14, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2182_1]
                      · have p2182_0 := h2182c.1
                        have p2182_1 := h2182c.2.1
                        have p2182_2 := h2182c.2.2.1
                        have p2182_3 := h2182c.2.2.2
                        rcases p2182_3 (m.d 0 4) (by simp) with h2210 | h2210
                        · linarith only [h1521, h2210, hlam]
                        · linarith only [h1530, h2210, hlam]
                      · have p2182_0 := h2182c.1
                        have p2182_1 := h2182c.2.1
                        have p2182_2 := h2182c.2.2.1
                        have p2182_3 := h2182c.2.2.2
                        linarith only [h1526, hlam, p2182_0]
                      · have p2182_0 := h2182c.1
                        have p2182_1 := h2182c.2.1
                        have p2182_2 := h2182c.2.2.1
                        have p2182_3 := h2182c.2.2.2
                        linarith only [h1532, hlam, p2182_0]
                      · have p2182_0 := h2182c.1
                        have p2182_1 := h2182c.2.1
                        have p2182_2 := h2182c.2.2.1
                        have p2182_3 := h2182c.2.2.2
                        linarith only [hlam, p2182_0]
                      · have p2182_0 := h2182c.1
                        have p2182_1 := h2182c.2.1
                        have p2182_2 := h2182c.2.2.1
                        have p2182_3 := h2182c.2.2.2
                        linarith only [h1537, hlam, p2182_1]
                      · have p2182_0 := h2182c.1
                        have p2182_1 := h2182c.2.1
                        have p2182_2 := h2182c.2.2.1
                        have p2182_3 := h2182c.2.2.2
                        linarith only [h2058, hlam, p2182_0]
                      · have p2182_0 := h2182c.1
                        have p2182_1 := h2182c.2.1
                        have p2182_2 := h2182c.2.2.1
                        have p2182_3 := h2182c.2.2.2
                        linarith only [h1528, hlam, p2182_0]
                      · have p2182_0 := h2182c.1
                        have p2182_1 := h2182c.2.1
                        have p2182_2 := h2182c.2.2.1
                        have p2182_3 := h2182c.2.2.2
                        linarith only [h1534, hlam, p2182_0]
                      · have p2182_0 := h2182c.1
                        have p2182_1 := h2182c.2.1
                        have p2182_2 := h2182c.2.2.1
                        have p2182_3 := h2182c.2.2.2
                        rcases p2182_3 (m.d 0 4) (by simp) with h2220 | h2220
                        · rcases p2182_3 (m.d 1 4) (by simp) with h2221 | h2221
                          · rcases p2182_3 (m.d 2 4) (by simp) with h2222 | h2222
                            · linarith only [h1537, h2222, hlam]
                            · rcases p2182_3 (m.d 3 4) (by simp) with h2224 | h2224
                              · rcases p2182_3 (m.d 4 5) (by simp) with h2225 | h2225
                                · linarith only [h2165, h2225, hlam]
                                · linarith only [h2058, h2225, hlam]
                              · linarith only [h1537, h2224, hlam]
                          · linarith only [h1532, h2221, hlam]
                        · linarith only [h1526, h2220, hlam]
                      · have p2182_0 := h2182c.1
                        have p2182_1 := h2182c.2.1
                        have p2182_2 := h2182c.2.2.1
                        have p2182_3 := h2182c.2.2.2
                        linarith only [hlam, p2182_0]
                      · have p2182_0 := h2182c.1
                        have p2182_1 := h2182c.2.1
                        have p2182_2 := h2182c.2.2.1
                        have p2182_3 := h2182c.2.2.2
                        linarith only [h1537, h2058, hc23, hc34, hlam, hphi, p2182_1]
                      · have p2182_0 := h2182c.1
                        have p2182_1 := h2182c.2.1
                        have p2182_2 := h2182c.2.2.1
                        have p2182_3 := h2182c.2.2.2
                        linarith only [h1530, hlam, p2182_0]
                      · have p2182_0 := h2182c.1
                        have p2182_1 := h2182c.2.1
                        have p2182_2 := h2182c.2.2.1
                        have p2182_3 := h2182c.2.2.2
                        linarith only [h1536, hlam, p2182_0]
                      · have p2182_0 := h2182c.1
                        have p2182_1 := h2182c.2.1
                        have p2182_2 := h2182c.2.2.1
                        have p2182_3 := h2182c.2.2.2
                        linarith only [h0, h1525, h1528, h1537, h2165, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2182_1]
                      · have p2182_0 := h2182c.1
                        have p2182_1 := h2182c.2.1
                        have p2182_2 := h2182c.2.2.1
                        have p2182_3 := h2182c.2.2.2
                        linarith only [h2165, hlam, p2182_0]
                      · have p2182_0 := h2182c.1
                        have p2182_1 := h2182c.2.1
                        have p2182_2 := h2182c.2.2.1
                        have p2182_3 := h2182c.2.2.2
                        linarith only [hlam, p2182_0]
                    · rcases h4bigk with h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c | h2238c
                      · have p2238_0 := h2238c.1
                        have p2238_1 := h2238c.2.1
                        have p2238_2 := h2238c.2.2.1
                        have p2238_3 := h2238c.2.2.2
                        linarith only [hlam, p2238_0]
                      · have p2238_0 := h2238c.1
                        have p2238_1 := h2238c.2.1
                        have p2238_2 := h2238c.2.2.1
                        have p2238_3 := h2238c.2.2.2
                        linarith only [h1521, hlam, p2238_1]
                      · have p2238_0 := h2238c.1
                        have p2238_1 := h2238c.2.1
                        have p2238_2 := h2238c.2.2.1
                        have p2238_3 := h2238c.2.2.2
                        rcases p2238_3 (m.d 0 4) (by simp) with h2241 | h2241
                        · rcases p2238_3 (m.d 1 4) (by simp) with h2242 | h2242
                          · rcases p2238_3 (m.d 2 4) (by simp) with h2243 | h2243
                            · linarith only [h1526, h2243, hlam]
                            · rcases p2238_3 (m.d 3 4) (by simp) with h2245 | h2245
                              · linarith only [h1528, h2245, hlam]
                              · linarith only [h1537, h2245, hlam]
                          · linarith only [h1532, h2242, hlam]
                        · linarith only [h1526, h2241, hlam]
                      · have p2238_0 := h2238c.1
                        have p2238_1 := h2238c.2.1
                        have p2238_2 := h2238c.2.2.1
                        have p2238_3 := h2238c.2.2.2
                        linarith only [h0, h1525, h1528, h2165, hc12, hlam, hphi, ht01, ht0b, ht5b, p2238_1, u5ehi4]
                      · have p2238_0 := h2238c.1
                        have p2238_1 := h2238c.2.1
                        have p2238_2 := h2238c.2.2.1
                        have p2238_3 := h2238c.2.2.2
                        rcases p2238_3 (m.d 0 4) (by simp) with h2251 | h2251
                        · rcases p2238_3 (m.d 1 4) (by simp) with h2252 | h2252
                          · rcases p2238_3 (m.d 2 4) (by simp) with h2253 | h2253
                            · linarith only [h1526, h2253, hlam]
                            · rcases p2238_3 (m.d 3 4) (by simp) with h2255 | h2255
                              · linarith only [h1528, h2255, hlam]
                              · linarith only [h2165, h2255, hlam]
                          · linarith only [h1536, h2252, hlam]
                        · linarith only [h2251, hlam, p2238_0]
                      · have p2238_0 := h2238c.1
                        have p2238_1 := h2238c.2.1
                        have p2238_2 := h2238c.2.2.1
                        have p2238_3 := h2238c.2.2.2
                        linarith only [h1521, h1531, h1534, hc12, hlam, hphi, p2238_1, u1ehi0]
                      · have p2238_0 := h2238c.1
                        have p2238_1 := h2238c.2.1
                        have p2238_2 := h2238c.2.2.1
                        have p2238_3 := h2238c.2.2.2
                        linarith only [hlam, p2238_0]
                      · have p2238_0 := h2238c.1
                        have p2238_1 := h2238c.2.1
                        have p2238_2 := h2238c.2.2.1
                        have p2238_3 := h2238c.2.2.2
                        rcases p2238_3 (m.d 0 4) (by simp) with h2262 | h2262
                        · linarith only [h1521, h2262, hlam]
                        · linarith only [h1526, h2262, hlam]
                      · have p2238_0 := h2238c.1
                        have p2238_1 := h2238c.2.1
                        have p2238_2 := h2238c.2.2.1
                        have p2238_3 := h2238c.2.2.2
                        linarith only [h1537, h2058, h2165, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2238_1]
                      · have p2238_0 := h2238c.1
                        have p2238_1 := h2238c.2.1
                        have p2238_2 := h2238c.2.2.1
                        have p2238_3 := h2238c.2.2.2
                        rcases p2238_3 (m.d 0 4) (by simp) with h2266 | h2266
                        · linarith only [h1521, h2266, hlam]
                        · linarith only [h1530, h2266, hlam]
                      · have p2238_0 := h2238c.1
                        have p2238_1 := h2238c.2.1
                        have p2238_2 := h2238c.2.2.1
                        have p2238_3 := h2238c.2.2.2
                        linarith only [h1526, hlam, p2238_0]
                      · have p2238_0 := h2238c.1
                        have p2238_1 := h2238c.2.1
                        have p2238_2 := h2238c.2.2.1
                        have p2238_3 := h2238c.2.2.2
                        linarith only [h1532, hlam, p2238_0]
                      · have p2238_0 := h2238c.1
                        have p2238_1 := h2238c.2.1
                        have p2238_2 := h2238c.2.2.1
                        have p2238_3 := h2238c.2.2.2
                        linarith only [hlam, p2238_0]
                      · have p2238_0 := h2238c.1
                        have p2238_1 := h2238c.2.1
                        have p2238_2 := h2238c.2.2.1
                        have p2238_3 := h2238c.2.2.2
                        linarith only [h1537, hlam, p2238_1]
                      · have p2238_0 := h2238c.1
                        have p2238_1 := h2238c.2.1
                        have p2238_2 := h2238c.2.2.1
                        have p2238_3 := h2238c.2.2.2
                        linarith only [h2058, hlam, p2238_0]
                      · have p2238_0 := h2238c.1
                        have p2238_1 := h2238c.2.1
                        have p2238_2 := h2238c.2.2.1
                        have p2238_3 := h2238c.2.2.2
                        linarith only [h1528, hlam, p2238_0]
                      · have p2238_0 := h2238c.1
                        have p2238_1 := h2238c.2.1
                        have p2238_2 := h2238c.2.2.1
                        have p2238_3 := h2238c.2.2.2
                        linarith only [h1534, hlam, p2238_0]
                      · have p2238_0 := h2238c.1
                        have p2238_1 := h2238c.2.1
                        have p2238_2 := h2238c.2.2.1
                        have p2238_3 := h2238c.2.2.2
                        rcases p2238_3 (m.d 0 4) (by simp) with h2276 | h2276
                        · rcases p2238_3 (m.d 1 4) (by simp) with h2277 | h2277
                          · rcases p2238_3 (m.d 2 4) (by simp) with h2278 | h2278
                            · linarith only [h1537, h2278, hlam]
                            · rcases p2238_3 (m.d 3 4) (by simp) with h2280 | h2280
                              · rcases p2238_3 (m.d 4 5) (by simp) with h2281 | h2281
                                · linarith only [h2165, h2281, hlam]
                                · linarith only [h2058, h2281, hlam]
                              · linarith only [h1537, h2280, hlam]
                          · linarith only [h1532, h2277, hlam]
                        · linarith only [h1526, h2276, hlam]
                      · have p2238_0 := h2238c.1
                        have p2238_1 := h2238c.2.1
                        have p2238_2 := h2238c.2.2.1
                        have p2238_3 := h2238c.2.2.2
                        linarith only [hlam, p2238_0]
                      · have p2238_0 := h2238c.1
                        have p2238_1 := h2238c.2.1
                        have p2238_2 := h2238c.2.2.1
                        have p2238_3 := h2238c.2.2.2
                        linarith only [h1537, h2058, hc23, hc34, hlam, hphi, p2238_1]
                      · have p2238_0 := h2238c.1
                        have p2238_1 := h2238c.2.1
                        have p2238_2 := h2238c.2.2.1
                        have p2238_3 := h2238c.2.2.2
                        linarith only [h1530, hlam, p2238_0]
                      · have p2238_0 := h2238c.1
                        have p2238_1 := h2238c.2.1
                        have p2238_2 := h2238c.2.2.1
                        have p2238_3 := h2238c.2.2.2
                        linarith only [h1536, hlam, p2238_0]
                      · have p2238_0 := h2238c.1
                        have p2238_1 := h2238c.2.1
                        have p2238_2 := h2238c.2.2.1
                        have p2238_3 := h2238c.2.2.2
                        linarith only [h0, h1525, h1528, h1537, h2165, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2238_1]
                      · have p2238_0 := h2238c.1
                        have p2238_1 := h2238c.2.1
                        have p2238_2 := h2238c.2.2.1
                        have p2238_3 := h2238c.2.2.2
                        linarith only [h2165, hlam, p2238_0]
                      · have p2238_0 := h2238c.1
                        have p2238_1 := h2238c.2.1
                        have p2238_2 := h2238c.2.2.1
                        have p2238_3 := h2238c.2.2.2
                        linarith only [hlam, p2238_0]
                    · rcases h4bigk with h2294c | h2294c | h2294c | h2294c | h2294c | h2294c | h2294c | h2294c | h2294c | h2294c | h2294c | h2294c | h2294c | h2294c | h2294c | h2294c | h2294c | h2294c | h2294c | h2294c | h2294c | h2294c | h2294c | h2294c | h2294c
                      · have p2294_0 := h2294c.1
                        have p2294_1 := h2294c.2.1
                        have p2294_2 := h2294c.2.2.1
                        have p2294_3 := h2294c.2.2.2
                        linarith only [hlam, p2294_0]
                      · have p2294_0 := h2294c.1
                        have p2294_1 := h2294c.2.1
                        have p2294_2 := h2294c.2.2.1
                        have p2294_3 := h2294c.2.2.2
                        linarith only [h1521, hlam, p2294_1]
                      · have p2294_0 := h2294c.1
                        have p2294_1 := h2294c.2.1
                        have p2294_2 := h2294c.2.2.1
                        have p2294_3 := h2294c.2.2.2
                        rcases p2294_3 (m.d 0 4) (by simp) with h2297 | h2297
                        · rcases p2294_3 (m.d 1 4) (by simp) with h2298 | h2298
                          · rcases p2294_3 (m.d 2 4) (by simp) with h2299 | h2299
                            · linarith only [h1526, h2299, hlam]
                            · rcases p2294_3 (m.d 3 4) (by simp) with h2301 | h2301
                              · linarith only [h1528, h2301, hlam]
                              · linarith only [h1537, h2301, hlam]
                          · linarith only [h1532, h2298, hlam]
                        · linarith only [h1526, h2297, hlam]
                      · have p2294_0 := h2294c.1
                        have p2294_1 := h2294c.2.1
                        have p2294_2 := h2294c.2.2.1
                        have p2294_3 := h2294c.2.2.2
                        linarith only [h2165, hc04, hlam, hphi, ht0b, ht5b, p2294_1, u5ehi4]
                      · have p2294_0 := h2294c.1
                        have p2294_1 := h2294c.2.1
                        have p2294_2 := h2294c.2.2.1
                        have p2294_3 := h2294c.2.2.2
                        rcases p2294_3 (m.d 0 4) (by simp) with h2307 | h2307
                        · rcases p2294_3 (m.d 1 4) (by simp) with h2308 | h2308
                          · rcases p2294_3 (m.d 2 4) (by simp) with h2309 | h2309
                            · linarith only [h1526, h2309, hlam]
                            · rcases p2294_3 (m.d 3 4) (by simp) with h2311 | h2311
                              · linarith only [h1528, h2311, hlam]
                              · linarith only [h2165, h2311, hlam]
                          · linarith only [h1536, h2308, hlam]
                        · linarith only [h2307, hlam, p2294_0]
                      · have p2294_0 := h2294c.1
                        have p2294_1 := h2294c.2.1
                        have p2294_2 := h2294c.2.2.1
                        have p2294_3 := h2294c.2.2.2
                        linarith only [h1521, h1531, h1534, hc12, hlam, hphi, p2294_1, u1ehi0]
                      · have p2294_0 := h2294c.1
                        have p2294_1 := h2294c.2.1
                        have p2294_2 := h2294c.2.2.1
                        have p2294_3 := h2294c.2.2.2
                        linarith only [hlam, p2294_0]
                      · have p2294_0 := h2294c.1
                        have p2294_1 := h2294c.2.1
                        have p2294_2 := h2294c.2.2.1
                        have p2294_3 := h2294c.2.2.2
                        rcases p2294_3 (m.d 0 4) (by simp) with h2318 | h2318
                        · linarith only [h1521, h2318, hlam]
                        · linarith only [h1526, h2318, hlam]
                      · have p2294_0 := h2294c.1
                        have p2294_1 := h2294c.2.1
                        have p2294_2 := h2294c.2.2.1
                        have p2294_3 := h2294c.2.2.2
                        linarith only [h1537, h2058, h2165, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2294_1]
                      · have p2294_0 := h2294c.1
                        have p2294_1 := h2294c.2.1
                        have p2294_2 := h2294c.2.2.1
                        have p2294_3 := h2294c.2.2.2
                        rcases p2294_3 (m.d 0 4) (by simp) with h2322 | h2322
                        · linarith only [h1521, h2322, hlam]
                        · linarith only [h1530, h2322, hlam]
                      · have p2294_0 := h2294c.1
                        have p2294_1 := h2294c.2.1
                        have p2294_2 := h2294c.2.2.1
                        have p2294_3 := h2294c.2.2.2
                        linarith only [h1526, hlam, p2294_0]
                      · have p2294_0 := h2294c.1
                        have p2294_1 := h2294c.2.1
                        have p2294_2 := h2294c.2.2.1
                        have p2294_3 := h2294c.2.2.2
                        linarith only [h1532, hlam, p2294_0]
                      · have p2294_0 := h2294c.1
                        have p2294_1 := h2294c.2.1
                        have p2294_2 := h2294c.2.2.1
                        have p2294_3 := h2294c.2.2.2
                        linarith only [hlam, p2294_0]
                      · have p2294_0 := h2294c.1
                        have p2294_1 := h2294c.2.1
                        have p2294_2 := h2294c.2.2.1
                        have p2294_3 := h2294c.2.2.2
                        linarith only [h1537, hlam, p2294_1]
                      · have p2294_0 := h2294c.1
                        have p2294_1 := h2294c.2.1
                        have p2294_2 := h2294c.2.2.1
                        have p2294_3 := h2294c.2.2.2
                        linarith only [h2058, hlam, p2294_0]
                      · have p2294_0 := h2294c.1
                        have p2294_1 := h2294c.2.1
                        have p2294_2 := h2294c.2.2.1
                        have p2294_3 := h2294c.2.2.2
                        linarith only [h1528, hlam, p2294_0]
                      · have p2294_0 := h2294c.1
                        have p2294_1 := h2294c.2.1
                        have p2294_2 := h2294c.2.2.1
                        have p2294_3 := h2294c.2.2.2
                        linarith only [h1534, hlam, p2294_0]
                      · have p2294_0 := h2294c.1
                        have p2294_1 := h2294c.2.1
                        have p2294_2 := h2294c.2.2.1
                        have p2294_3 := h2294c.2.2.2
                        rcases p2294_3 (m.d 0 4) (by simp) with h2332 | h2332
                        · rcases p2294_3 (m.d 1 4) (by simp) with h2333 | h2333
                          · rcases p2294_3 (m.d 2 4) (by simp) with h2334 | h2334
                            · linarith only [h1537, h2334, hlam]
                            · rcases p2294_3 (m.d 3 4) (by simp) with h2336 | h2336
                              · rcases p2294_3 (m.d 4 5) (by simp) with h2337 | h2337
                                · linarith only [h2165, h2337, hlam]
                                · linarith only [h2058, h2337, hlam]
                              · linarith only [h1537, h2336, hlam]
                          · linarith only [h1532, h2333, hlam]
                        · linarith only [h1526, h2332, hlam]
                      · have p2294_0 := h2294c.1
                        have p2294_1 := h2294c.2.1
                        have p2294_2 := h2294c.2.2.1
                        have p2294_3 := h2294c.2.2.2
                        linarith only [hlam, p2294_0]
                      · have p2294_0 := h2294c.1
                        have p2294_1 := h2294c.2.1
                        have p2294_2 := h2294c.2.2.1
                        have p2294_3 := h2294c.2.2.2
                        linarith only [h1537, h2058, hc23, hc34, hlam, hphi, p2294_1]
                      · have p2294_0 := h2294c.1
                        have p2294_1 := h2294c.2.1
                        have p2294_2 := h2294c.2.2.1
                        have p2294_3 := h2294c.2.2.2
                        linarith only [h1530, hlam, p2294_0]
                      · have p2294_0 := h2294c.1
                        have p2294_1 := h2294c.2.1
                        have p2294_2 := h2294c.2.2.1
                        have p2294_3 := h2294c.2.2.2
                        linarith only [h1536, hlam, p2294_0]
                      · have p2294_0 := h2294c.1
                        have p2294_1 := h2294c.2.1
                        have p2294_2 := h2294c.2.2.1
                        have p2294_3 := h2294c.2.2.2
                        linarith only [h0, h1525, h1528, h1537, h2165, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2294_1]
                      · have p2294_0 := h2294c.1
                        have p2294_1 := h2294c.2.1
                        have p2294_2 := h2294c.2.2.1
                        have p2294_3 := h2294c.2.2.2
                        linarith only [h2165, hlam, p2294_0]
                      · have p2294_0 := h2294c.1
                        have p2294_1 := h2294c.2.1
                        have p2294_2 := h2294c.2.2.1
                        have p2294_3 := h2294c.2.2.2
                        linarith only [hlam, p2294_0]
            · linarith only [h1533, h2172, hlam]
          · linarith only [h2171, hlam, p2166_0]
        · have p2166_0 := h2166c.1
          have p2166_1 := h2166c.2.1
          have p2166_2 := h2166c.2.2.1
          have p2166_3 := h2166c.2.2.2
          linarith only [h0, hc12, hlam, hphi, p2166_1, u1ehi0]
        · have p2166_0 := h2166c.1
          have p2166_1 := h2166c.2.1
          have p2166_2 := h2166c.2.2.1
          have p2166_3 := h2166c.2.2.2
          linarith only [hlam, p2166_0]
        · have p2166_0 := h2166c.1
          have p2166_1 := h2166c.2.1
          have p2166_2 := h2166c.2.2.1
          have p2166_3 := h2166c.2.2.2
          linarith only [h0, h1525, h1528, h1537, h2058, h2165, hlam, p2166_2]
        · have p2166_0 := h2166c.1
          have p2166_1 := h2166c.2.1
          have p2166_2 := h2166c.2.2.1
          have p2166_3 := h2166c.2.2.2
          linarith only [h0, h1525, h1528, h2058, h2165, hlam, p2166_2]
        · have p2166_0 := h2166c.1
          have p2166_1 := h2166c.2.1
          have p2166_2 := h2166c.2.2.1
          have p2166_3 := h2166c.2.2.2
          rcases p2166_3 (m.d 0 2) (by simp) with h2356 | h2356
          · linarith only [h0, h2356, hlam]
          · linarith only [h1527, h2356, hlam]
        · have p2166_0 := h2166c.1
          have p2166_1 := h2166c.2.1
          have p2166_2 := h2166c.2.2.1
          have p2166_3 := h2166c.2.2.2
          linarith only [h1525, hlam, p2166_0]
        · have p2166_0 := h2166c.1
          have p2166_1 := h2166c.2.1
          have p2166_2 := h2166c.2.2.1
          have p2166_3 := h2166c.2.2.2
          linarith only [h1531, hlam, p2166_0]
        · have p2166_0 := h2166c.1
          have p2166_1 := h2166c.2.1
          have p2166_2 := h2166c.2.2.1
          have p2166_3 := h2166c.2.2.2
          linarith only [hlam, p2166_0]
        · have p2166_0 := h2166c.1
          have p2166_1 := h2166c.2.1
          have p2166_2 := h2166c.2.2.1
          have p2166_3 := h2166c.2.2.2
          linarith only [h1537, hlam, p2166_1]
        · have p2166_0 := h2166c.1
          have p2166_1 := h2166c.2.1
          have p2166_2 := h2166c.2.2.1
          have p2166_3 := h2166c.2.2.2
          linarith only [h2056, hlam, p2166_1]
        · have p2166_0 := h2166c.1
          have p2166_1 := h2166c.2.1
          have p2166_2 := h2166c.2.2.1
          have p2166_3 := h2166c.2.2.2
          linarith only [h1526, hlam, p2166_0]
        · have p2166_0 := h2166c.1
          have p2166_1 := h2166c.2.1
          have p2166_2 := h2166c.2.2.1
          have p2166_3 := h2166c.2.2.2
          linarith only [h1532, hlam, p2166_0]
        · have p2166_0 := h2166c.1
          have p2166_1 := h2166c.2.1
          have p2166_2 := h2166c.2.2.1
          have p2166_3 := h2166c.2.2.2
          linarith only [h0, h1525, h1528, h2058, h2165, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2166_1]
        · have p2166_0 := h2166c.1
          have p2166_1 := h2166c.2.1
          have p2166_2 := h2166c.2.2.1
          have p2166_3 := h2166c.2.2.2
          linarith only [hlam, p2166_0]
        · have p2166_0 := h2166c.1
          have p2166_1 := h2166c.2.1
          have p2166_2 := h2166c.2.2.1
          have p2166_3 := h2166c.2.2.2
          linarith only [h2058, hlam, p2166_0]
        · have p2166_0 := h2166c.1
          have p2166_1 := h2166c.2.1
          have p2166_2 := h2166c.2.2.1
          have p2166_3 := h2166c.2.2.2
          linarith only [h1527, hlam, p2166_0]
        · have p2166_0 := h2166c.1
          have p2166_1 := h2166c.2.1
          have p2166_2 := h2166c.2.2.1
          have p2166_3 := h2166c.2.2.2
          linarith only [h1533, hlam, p2166_0]
        · have p2166_0 := h2166c.1
          have p2166_1 := h2166c.2.1
          have p2166_2 := h2166c.2.2.1
          have p2166_3 := h2166c.2.2.2
          linarith only [h0, h1525, h1528, h2058, h2165, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2166_1]
        · have p2166_0 := h2166c.1
          have p2166_1 := h2166c.2.1
          have p2166_2 := h2166c.2.2.1
          have p2166_3 := h2166c.2.2.2
          linarith only [h0, h1525, h1528, h2058, h2165, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2166_1]
        · have p2166_0 := h2166c.1
          have p2166_1 := h2166c.2.1
          have p2166_2 := h2166c.2.2.1
          have p2166_3 := h2166c.2.2.2
          linarith only [hlam, p2166_0]
      · rcases h2bigk with h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c | h2374c
        · have p2374_0 := h2374c.1
          have p2374_1 := h2374c.2.1
          have p2374_2 := h2374c.2.2.1
          have p2374_3 := h2374c.2.2.2
          linarith only [hlam, p2374_0]
        · have p2374_0 := h2374c.1
          have p2374_1 := h2374c.2.1
          have p2374_2 := h2374c.2.2.1
          have p2374_3 := h2374c.2.2.2
          linarith only [h0, hlam, p2374_0]
        · have p2374_0 := h2374c.1
          have p2374_1 := h2374c.2.1
          have p2374_2 := h2374c.2.2.1
          have p2374_3 := h2374c.2.2.2
          linarith only [h1526, h1530, h1537, h2165, hlam, p2374_2]
        · have p2374_0 := h2374c.1
          have p2374_1 := h2374c.2.1
          have p2374_2 := h2374c.2.2.1
          have p2374_3 := h2374c.2.2.2
          rcases p2374_3 (m.d 0 2) (by simp) with h2378 | h2378
          · rcases p2374_3 (m.d 1 2) (by simp) with h2379 | h2379
            · rcases p2374_3 (m.d 2 3) (by simp) with h2380 | h2380
              · linarith only [h1525, h2380, hlam]
              · rcases p2374_3 (m.d 2 4) (by simp) with h2382 | h2382
                · linarith only [h2382, hlam, p2374_0]
                · rcases p2374_3 (m.d 2 5) (by simp) with h2384 | h2384
                  · linarith only [h1527, h2384, hlam]
                  · linarith only [h2058, h2384, hlam]
            · linarith only [h1532, h2379, hlam]
          · linarith only [h2378, hlam, p2374_0]
        · have p2374_0 := h2374c.1
          have p2374_1 := h2374c.2.1
          have p2374_2 := h2374c.2.2.1
          have p2374_3 := h2374c.2.2.2
          rcases p2374_3 (m.d 0 2) (by simp) with h2389 | h2389
          · rcases p2374_3 (m.d 1 2) (by simp) with h2390 | h2390
            · rcases p2374_3 (m.d 2 3) (by simp) with h2391 | h2391
              · linarith only [h1525, h2391, hlam]
              · rcases p2374_3 (m.d 2 4) (by simp) with h2393 | h2393
                · linarith only [h1526, h2393, hlam]
                · rcases p2374_3 (m.d 2 5) (by simp) with h2395 | h2395
                  · linarith only [h2395, hlam, p2374_0]
                  · rcases h2emax with h2397 | h2397 | h2397 | h2397 | h2397
                    · linarith only [h1525, h1528, h1530, h1537, h2165, h2397, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h2397, hlam, ht12, u1ehi1]
                    · rcases h4bigk with h2400c | h2400c | h2400c | h2400c | h2400c | h2400c | h2400c | h2400c | h2400c | h2400c | h2400c | h2400c | h2400c | h2400c | h2400c | h2400c | h2400c | h2400c | h2400c | h2400c | h2400c | h2400c | h2400c | h2400c | h2400c
                      · have p2400_0 := h2400c.1
                        have p2400_1 := h2400c.2.1
                        have p2400_2 := h2400c.2.2.1
                        have p2400_3 := h2400c.2.2.2
                        linarith only [hlam, p2400_0]
                      · have p2400_0 := h2400c.1
                        have p2400_1 := h2400c.2.1
                        have p2400_2 := h2400c.2.2.1
                        have p2400_3 := h2400c.2.2.2
                        linarith only [h1521, hlam, p2400_1]
                      · have p2400_0 := h2400c.1
                        have p2400_1 := h2400c.2.1
                        have p2400_2 := h2400c.2.2.1
                        have p2400_3 := h2400c.2.2.2
                        rcases p2400_3 (m.d 0 4) (by simp) with h2403 | h2403
                        · rcases p2400_3 (m.d 1 4) (by simp) with h2404 | h2404
                          · rcases p2400_3 (m.d 2 4) (by simp) with h2405 | h2405
                            · linarith only [h1526, h2405, hlam]
                            · rcases p2400_3 (m.d 3 4) (by simp) with h2407 | h2407
                              · linarith only [h1528, h2407, hlam]
                              · linarith only [h1537, h2407, hlam]
                          · linarith only [h1532, h2404, hlam]
                        · linarith only [h1526, h2403, hlam]
                      · have p2400_0 := h2400c.1
                        have p2400_1 := h2400c.2.1
                        have p2400_2 := h2400c.2.2.1
                        have p2400_3 := h2400c.2.2.2
                        rcases p2400_3 (m.d 0 4) (by simp) with h2412 | h2412
                        · rcases p2400_3 (m.d 1 4) (by simp) with h2413 | h2413
                          · rcases p2400_3 (m.d 2 4) (by simp) with h2414 | h2414
                            · linarith only [h1526, h2414, hlam]
                            · rcases p2400_3 (m.d 3 4) (by simp) with h2416 | h2416
                              · linarith only [h1528, h2416, hlam]
                              · rcases p2400_3 (m.d 4 5) (by simp) with h2418 | h2418
                                · linarith only [h1530, h2418, hlam]
                                · linarith only [h2165, h2418, hlam]
                          · linarith only [h1534, h2413, hlam]
                        · linarith only [h1528, h2412, hlam]
                      · have p2400_0 := h2400c.1
                        have p2400_1 := h2400c.2.1
                        have p2400_2 := h2400c.2.2.1
                        have p2400_3 := h2400c.2.2.2
                        linarith only [h1525, h1528, h1537, h2165, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2400_1]
                      · have p2400_0 := h2400c.1
                        have p2400_1 := h2400c.2.1
                        have p2400_2 := h2400c.2.2.1
                        have p2400_3 := h2400c.2.2.2
                        linarith only [h1521, hc14, hlam, hphi, p2400_1, u1ehi0]
                      · have p2400_0 := h2400c.1
                        have p2400_1 := h2400c.2.1
                        have p2400_2 := h2400c.2.2.1
                        have p2400_3 := h2400c.2.2.2
                        linarith only [hlam, p2400_0]
                      · have p2400_0 := h2400c.1
                        have p2400_1 := h2400c.2.1
                        have p2400_2 := h2400c.2.2.1
                        have p2400_3 := h2400c.2.2.2
                        rcases p2400_3 (m.d 0 4) (by simp) with h2426 | h2426
                        · linarith only [h1521, h2426, hlam]
                        · linarith only [h1526, h2426, hlam]
                      · have p2400_0 := h2400c.1
                        have p2400_1 := h2400c.2.1
                        have p2400_2 := h2400c.2.2.1
                        have p2400_3 := h2400c.2.2.2
                        rcases p2400_3 (m.d 0 4) (by simp) with h2429 | h2429
                        · linarith only [h1521, h2429, hlam]
                        · linarith only [h1528, h2429, hlam]
                      · have p2400_0 := h2400c.1
                        have p2400_1 := h2400c.2.1
                        have p2400_2 := h2400c.2.2.1
                        have p2400_3 := h2400c.2.2.2
                        linarith only [h1534, h1537, h2165, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2400_1]
                      · have p2400_0 := h2400c.1
                        have p2400_1 := h2400c.2.1
                        have p2400_2 := h2400c.2.2.1
                        have p2400_3 := h2400c.2.2.2
                        linarith only [h1526, hlam, p2400_0]
                      · have p2400_0 := h2400c.1
                        have p2400_1 := h2400c.2.1
                        have p2400_2 := h2400c.2.2.1
                        have p2400_3 := h2400c.2.2.2
                        linarith only [h1532, hlam, p2400_0]
                      · have p2400_0 := h2400c.1
                        have p2400_1 := h2400c.2.1
                        have p2400_2 := h2400c.2.2.1
                        have p2400_3 := h2400c.2.2.2
                        linarith only [hlam, p2400_0]
                      · have p2400_0 := h2400c.1
                        have p2400_1 := h2400c.2.1
                        have p2400_2 := h2400c.2.2.1
                        have p2400_3 := h2400c.2.2.2
                        linarith only [h1537, hlam, p2400_1]
                      · have p2400_0 := h2400c.1
                        have p2400_1 := h2400c.2.1
                        have p2400_2 := h2400c.2.2.1
                        have p2400_3 := h2400c.2.2.2
                        linarith only [h2058, hlam, p2400_0]
                      · have p2400_0 := h2400c.1
                        have p2400_1 := h2400c.2.1
                        have p2400_2 := h2400c.2.2.1
                        have p2400_3 := h2400c.2.2.2
                        linarith only [h1528, hlam, p2400_0]
                      · have p2400_0 := h2400c.1
                        have p2400_1 := h2400c.2.1
                        have p2400_2 := h2400c.2.2.1
                        have p2400_3 := h2400c.2.2.2
                        linarith only [h1534, hlam, p2400_0]
                      · have p2400_0 := h2400c.1
                        have p2400_1 := h2400c.2.1
                        have p2400_2 := h2400c.2.2.1
                        have p2400_3 := h2400c.2.2.2
                        linarith only [h1530, h2165, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b, p2400_1]
                      · have p2400_0 := h2400c.1
                        have p2400_1 := h2400c.2.1
                        have p2400_2 := h2400c.2.2.1
                        have p2400_3 := h2400c.2.2.2
                        linarith only [hlam, p2400_0]
                      · have p2400_0 := h2400c.1
                        have p2400_1 := h2400c.2.1
                        have p2400_2 := h2400c.2.2.1
                        have p2400_3 := h2400c.2.2.2
                        linarith only [h2165, hlam, p2400_0]
                      · have p2400_0 := h2400c.1
                        have p2400_1 := h2400c.2.1
                        have p2400_2 := h2400c.2.2.1
                        have p2400_3 := h2400c.2.2.2
                        linarith only [h1530, hlam, p2400_0]
                      · have p2400_0 := h2400c.1
                        have p2400_1 := h2400c.2.1
                        have p2400_2 := h2400c.2.2.1
                        have p2400_3 := h2400c.2.2.2
                        linarith only [h1536, hlam, p2400_0]
                      · have p2400_0 := h2400c.1
                        have p2400_1 := h2400c.2.1
                        have p2400_2 := h2400c.2.2.1
                        have p2400_3 := h2400c.2.2.2
                        rcases p2400_3 (m.d 0 4) (by simp) with h2445 | h2445
                        · rcases p2400_3 (m.d 1 4) (by simp) with h2446 | h2446
                          · rcases p2400_3 (m.d 2 4) (by simp) with h2447 | h2447
                            · linarith only [h2447, hlam, p2400_0]
                            · rcases p2400_3 (m.d 3 4) (by simp) with h2449 | h2449
                              · linarith only [h2165, h2449, hlam]
                              · linarith only [h1537, h2449, hlam]
                          · linarith only [h1532, h2446, hlam]
                        · linarith only [h1526, h2445, hlam]
                      · have p2400_0 := h2400c.1
                        have p2400_1 := h2400c.2.1
                        have p2400_2 := h2400c.2.2.1
                        have p2400_3 := h2400c.2.2.2
                        linarith only [h1521, h1530, h1531, h1534, h1537, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2400_1]
                      · have p2400_0 := h2400c.1
                        have p2400_1 := h2400c.2.1
                        have p2400_2 := h2400c.2.2.1
                        have p2400_3 := h2400c.2.2.2
                        linarith only [hlam, p2400_0]
                    · rcases h4bigk with h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c | h2456c
                      · have p2456_0 := h2456c.1
                        have p2456_1 := h2456c.2.1
                        have p2456_2 := h2456c.2.2.1
                        have p2456_3 := h2456c.2.2.2
                        linarith only [hlam, p2456_0]
                      · have p2456_0 := h2456c.1
                        have p2456_1 := h2456c.2.1
                        have p2456_2 := h2456c.2.2.1
                        have p2456_3 := h2456c.2.2.2
                        linarith only [h1521, hlam, p2456_1]
                      · have p2456_0 := h2456c.1
                        have p2456_1 := h2456c.2.1
                        have p2456_2 := h2456c.2.2.1
                        have p2456_3 := h2456c.2.2.2
                        rcases p2456_3 (m.d 0 4) (by simp) with h2459 | h2459
                        · rcases p2456_3 (m.d 1 4) (by simp) with h2460 | h2460
                          · rcases p2456_3 (m.d 2 4) (by simp) with h2461 | h2461
                            · linarith only [h1526, h2461, hlam]
                            · rcases p2456_3 (m.d 3 4) (by simp) with h2463 | h2463
                              · linarith only [h1528, h2463, hlam]
                              · linarith only [h1537, h2463, hlam]
                          · linarith only [h1532, h2460, hlam]
                        · linarith only [h1526, h2459, hlam]
                      · have p2456_0 := h2456c.1
                        have p2456_1 := h2456c.2.1
                        have p2456_2 := h2456c.2.2.1
                        have p2456_3 := h2456c.2.2.2
                        rcases p2456_3 (m.d 0 4) (by simp) with h2468 | h2468
                        · rcases p2456_3 (m.d 1 4) (by simp) with h2469 | h2469
                          · rcases p2456_3 (m.d 2 4) (by simp) with h2470 | h2470
                            · linarith only [h1526, h2470, hlam]
                            · rcases p2456_3 (m.d 3 4) (by simp) with h2472 | h2472
                              · linarith only [h1528, h2472, hlam]
                              · rcases p2456_3 (m.d 4 5) (by simp) with h2474 | h2474
                                · linarith only [h1530, h2474, hlam]
                                · linarith only [h2165, h2474, hlam]
                          · linarith only [h1534, h2469, hlam]
                        · linarith only [h1528, h2468, hlam]
                      · have p2456_0 := h2456c.1
                        have p2456_1 := h2456c.2.1
                        have p2456_2 := h2456c.2.2.1
                        have p2456_3 := h2456c.2.2.2
                        linarith only [h1521, h1531, h1534, h1537, h2165, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2456_1]
                      · have p2456_0 := h2456c.1
                        have p2456_1 := h2456c.2.1
                        have p2456_2 := h2456c.2.2.1
                        have p2456_3 := h2456c.2.2.2
                        linarith only [h1521, h1531, h1534, hc12, hlam, hphi, p2456_1, u1ehi0]
                      · have p2456_0 := h2456c.1
                        have p2456_1 := h2456c.2.1
                        have p2456_2 := h2456c.2.2.1
                        have p2456_3 := h2456c.2.2.2
                        linarith only [hlam, p2456_0]
                      · have p2456_0 := h2456c.1
                        have p2456_1 := h2456c.2.1
                        have p2456_2 := h2456c.2.2.1
                        have p2456_3 := h2456c.2.2.2
                        rcases p2456_3 (m.d 0 4) (by simp) with h2482 | h2482
                        · linarith only [h1521, h2482, hlam]
                        · linarith only [h1526, h2482, hlam]
                      · have p2456_0 := h2456c.1
                        have p2456_1 := h2456c.2.1
                        have p2456_2 := h2456c.2.2.1
                        have p2456_3 := h2456c.2.2.2
                        rcases p2456_3 (m.d 0 4) (by simp) with h2485 | h2485
                        · linarith only [h1521, h2485, hlam]
                        · linarith only [h1528, h2485, hlam]
                      · have p2456_0 := h2456c.1
                        have p2456_1 := h2456c.2.1
                        have p2456_2 := h2456c.2.2.1
                        have p2456_3 := h2456c.2.2.2
                        linarith only [h1531, h1534, h1537, h2165, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2456_1]
                      · have p2456_0 := h2456c.1
                        have p2456_1 := h2456c.2.1
                        have p2456_2 := h2456c.2.2.1
                        have p2456_3 := h2456c.2.2.2
                        linarith only [h1526, hlam, p2456_0]
                      · have p2456_0 := h2456c.1
                        have p2456_1 := h2456c.2.1
                        have p2456_2 := h2456c.2.2.1
                        have p2456_3 := h2456c.2.2.2
                        linarith only [h1532, hlam, p2456_0]
                      · have p2456_0 := h2456c.1
                        have p2456_1 := h2456c.2.1
                        have p2456_2 := h2456c.2.2.1
                        have p2456_3 := h2456c.2.2.2
                        linarith only [hlam, p2456_0]
                      · have p2456_0 := h2456c.1
                        have p2456_1 := h2456c.2.1
                        have p2456_2 := h2456c.2.2.1
                        have p2456_3 := h2456c.2.2.2
                        linarith only [h1537, hlam, p2456_1]
                      · have p2456_0 := h2456c.1
                        have p2456_1 := h2456c.2.1
                        have p2456_2 := h2456c.2.2.1
                        have p2456_3 := h2456c.2.2.2
                        linarith only [h2058, hlam, p2456_0]
                      · have p2456_0 := h2456c.1
                        have p2456_1 := h2456c.2.1
                        have p2456_2 := h2456c.2.2.1
                        have p2456_3 := h2456c.2.2.2
                        linarith only [h1528, hlam, p2456_0]
                      · have p2456_0 := h2456c.1
                        have p2456_1 := h2456c.2.1
                        have p2456_2 := h2456c.2.2.1
                        have p2456_3 := h2456c.2.2.2
                        linarith only [h1534, hlam, p2456_0]
                      · have p2456_0 := h2456c.1
                        have p2456_1 := h2456c.2.1
                        have p2456_2 := h2456c.2.2.1
                        have p2456_3 := h2456c.2.2.2
                        linarith only [h1530, h2165, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b, p2456_1]
                      · have p2456_0 := h2456c.1
                        have p2456_1 := h2456c.2.1
                        have p2456_2 := h2456c.2.2.1
                        have p2456_3 := h2456c.2.2.2
                        linarith only [hlam, p2456_0]
                      · have p2456_0 := h2456c.1
                        have p2456_1 := h2456c.2.1
                        have p2456_2 := h2456c.2.2.1
                        have p2456_3 := h2456c.2.2.2
                        linarith only [h2165, hlam, p2456_0]
                      · have p2456_0 := h2456c.1
                        have p2456_1 := h2456c.2.1
                        have p2456_2 := h2456c.2.2.1
                        have p2456_3 := h2456c.2.2.2
                        linarith only [h1530, hlam, p2456_0]
                      · have p2456_0 := h2456c.1
                        have p2456_1 := h2456c.2.1
                        have p2456_2 := h2456c.2.2.1
                        have p2456_3 := h2456c.2.2.2
                        linarith only [h1536, hlam, p2456_0]
                      · have p2456_0 := h2456c.1
                        have p2456_1 := h2456c.2.1
                        have p2456_2 := h2456c.2.2.1
                        have p2456_3 := h2456c.2.2.2
                        rcases p2456_3 (m.d 0 4) (by simp) with h2501 | h2501
                        · rcases p2456_3 (m.d 1 4) (by simp) with h2502 | h2502
                          · rcases p2456_3 (m.d 2 4) (by simp) with h2503 | h2503
                            · linarith only [h2503, hlam, p2456_0]
                            · rcases p2456_3 (m.d 3 4) (by simp) with h2505 | h2505
                              · linarith only [h2165, h2505, hlam]
                              · linarith only [h1537, h2505, hlam]
                          · linarith only [h1532, h2502, hlam]
                        · linarith only [h1526, h2501, hlam]
                      · have p2456_0 := h2456c.1
                        have p2456_1 := h2456c.2.1
                        have p2456_2 := h2456c.2.2.1
                        have p2456_3 := h2456c.2.2.2
                        linarith only [h1521, h1530, h1531, h1534, h1537, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2456_1]
                      · have p2456_0 := h2456c.1
                        have p2456_1 := h2456c.2.1
                        have p2456_2 := h2456c.2.2.1
                        have p2456_3 := h2456c.2.2.2
                        linarith only [hlam, p2456_0]
                    · rcases h4bigk with h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c | h2512c
                      · have p2512_0 := h2512c.1
                        have p2512_1 := h2512c.2.1
                        have p2512_2 := h2512c.2.2.1
                        have p2512_3 := h2512c.2.2.2
                        linarith only [hlam, p2512_0]
                      · have p2512_0 := h2512c.1
                        have p2512_1 := h2512c.2.1
                        have p2512_2 := h2512c.2.2.1
                        have p2512_3 := h2512c.2.2.2
                        linarith only [h1521, hlam, p2512_1]
                      · have p2512_0 := h2512c.1
                        have p2512_1 := h2512c.2.1
                        have p2512_2 := h2512c.2.2.1
                        have p2512_3 := h2512c.2.2.2
                        rcases p2512_3 (m.d 0 4) (by simp) with h2515 | h2515
                        · rcases p2512_3 (m.d 1 4) (by simp) with h2516 | h2516
                          · rcases p2512_3 (m.d 2 4) (by simp) with h2517 | h2517
                            · linarith only [h1526, h2517, hlam]
                            · rcases p2512_3 (m.d 3 4) (by simp) with h2519 | h2519
                              · linarith only [h1528, h2519, hlam]
                              · linarith only [h1537, h2519, hlam]
                          · linarith only [h1532, h2516, hlam]
                        · linarith only [h1526, h2515, hlam]
                      · have p2512_0 := h2512c.1
                        have p2512_1 := h2512c.2.1
                        have p2512_2 := h2512c.2.2.1
                        have p2512_3 := h2512c.2.2.2
                        rcases p2512_3 (m.d 0 4) (by simp) with h2524 | h2524
                        · rcases p2512_3 (m.d 1 4) (by simp) with h2525 | h2525
                          · rcases p2512_3 (m.d 2 4) (by simp) with h2526 | h2526
                            · linarith only [h1526, h2526, hlam]
                            · rcases p2512_3 (m.d 3 4) (by simp) with h2528 | h2528
                              · linarith only [h1528, h2528, hlam]
                              · rcases p2512_3 (m.d 4 5) (by simp) with h2530 | h2530
                                · linarith only [h1530, h2530, hlam]
                                · linarith only [h2165, h2530, hlam]
                          · linarith only [h1534, h2525, hlam]
                        · linarith only [h1528, h2524, hlam]
                      · have p2512_0 := h2512c.1
                        have p2512_1 := h2512c.2.1
                        have p2512_2 := h2512c.2.2.1
                        have p2512_3 := h2512c.2.2.2
                        linarith only [h1521, h1531, h1534, h1537, h2165, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2512_1]
                      · have p2512_0 := h2512c.1
                        have p2512_1 := h2512c.2.1
                        have p2512_2 := h2512c.2.2.1
                        have p2512_3 := h2512c.2.2.2
                        linarith only [h1521, h1531, h1534, hc12, hlam, hphi, p2512_1, u1ehi0]
                      · have p2512_0 := h2512c.1
                        have p2512_1 := h2512c.2.1
                        have p2512_2 := h2512c.2.2.1
                        have p2512_3 := h2512c.2.2.2
                        linarith only [hlam, p2512_0]
                      · have p2512_0 := h2512c.1
                        have p2512_1 := h2512c.2.1
                        have p2512_2 := h2512c.2.2.1
                        have p2512_3 := h2512c.2.2.2
                        rcases p2512_3 (m.d 0 4) (by simp) with h2538 | h2538
                        · linarith only [h1521, h2538, hlam]
                        · linarith only [h1526, h2538, hlam]
                      · have p2512_0 := h2512c.1
                        have p2512_1 := h2512c.2.1
                        have p2512_2 := h2512c.2.2.1
                        have p2512_3 := h2512c.2.2.2
                        rcases p2512_3 (m.d 0 4) (by simp) with h2541 | h2541
                        · linarith only [h1521, h2541, hlam]
                        · linarith only [h1528, h2541, hlam]
                      · have p2512_0 := h2512c.1
                        have p2512_1 := h2512c.2.1
                        have p2512_2 := h2512c.2.2.1
                        have p2512_3 := h2512c.2.2.2
                        linarith only [h1537, h2165, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2512_1]
                      · have p2512_0 := h2512c.1
                        have p2512_1 := h2512c.2.1
                        have p2512_2 := h2512c.2.2.1
                        have p2512_3 := h2512c.2.2.2
                        linarith only [h1526, hlam, p2512_0]
                      · have p2512_0 := h2512c.1
                        have p2512_1 := h2512c.2.1
                        have p2512_2 := h2512c.2.2.1
                        have p2512_3 := h2512c.2.2.2
                        linarith only [h1532, hlam, p2512_0]
                      · have p2512_0 := h2512c.1
                        have p2512_1 := h2512c.2.1
                        have p2512_2 := h2512c.2.2.1
                        have p2512_3 := h2512c.2.2.2
                        linarith only [hlam, p2512_0]
                      · have p2512_0 := h2512c.1
                        have p2512_1 := h2512c.2.1
                        have p2512_2 := h2512c.2.2.1
                        have p2512_3 := h2512c.2.2.2
                        linarith only [h1537, hlam, p2512_1]
                      · have p2512_0 := h2512c.1
                        have p2512_1 := h2512c.2.1
                        have p2512_2 := h2512c.2.2.1
                        have p2512_3 := h2512c.2.2.2
                        linarith only [h2058, hlam, p2512_0]
                      · have p2512_0 := h2512c.1
                        have p2512_1 := h2512c.2.1
                        have p2512_2 := h2512c.2.2.1
                        have p2512_3 := h2512c.2.2.2
                        linarith only [h1528, hlam, p2512_0]
                      · have p2512_0 := h2512c.1
                        have p2512_1 := h2512c.2.1
                        have p2512_2 := h2512c.2.2.1
                        have p2512_3 := h2512c.2.2.2
                        linarith only [h1534, hlam, p2512_0]
                      · have p2512_0 := h2512c.1
                        have p2512_1 := h2512c.2.1
                        have p2512_2 := h2512c.2.2.1
                        have p2512_3 := h2512c.2.2.2
                        linarith only [h1530, h2165, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b, p2512_1]
                      · have p2512_0 := h2512c.1
                        have p2512_1 := h2512c.2.1
                        have p2512_2 := h2512c.2.2.1
                        have p2512_3 := h2512c.2.2.2
                        linarith only [hlam, p2512_0]
                      · have p2512_0 := h2512c.1
                        have p2512_1 := h2512c.2.1
                        have p2512_2 := h2512c.2.2.1
                        have p2512_3 := h2512c.2.2.2
                        linarith only [h2165, hlam, p2512_0]
                      · have p2512_0 := h2512c.1
                        have p2512_1 := h2512c.2.1
                        have p2512_2 := h2512c.2.2.1
                        have p2512_3 := h2512c.2.2.2
                        linarith only [h1530, hlam, p2512_0]
                      · have p2512_0 := h2512c.1
                        have p2512_1 := h2512c.2.1
                        have p2512_2 := h2512c.2.2.1
                        have p2512_3 := h2512c.2.2.2
                        linarith only [h1536, hlam, p2512_0]
                      · have p2512_0 := h2512c.1
                        have p2512_1 := h2512c.2.1
                        have p2512_2 := h2512c.2.2.1
                        have p2512_3 := h2512c.2.2.2
                        rcases p2512_3 (m.d 0 4) (by simp) with h2557 | h2557
                        · rcases p2512_3 (m.d 1 4) (by simp) with h2558 | h2558
                          · rcases p2512_3 (m.d 2 4) (by simp) with h2559 | h2559
                            · linarith only [h2559, hlam, p2512_0]
                            · rcases p2512_3 (m.d 3 4) (by simp) with h2561 | h2561
                              · linarith only [h2165, h2561, hlam]
                              · linarith only [h1537, h2561, hlam]
                          · linarith only [h1532, h2558, hlam]
                        · linarith only [h1526, h2557, hlam]
                      · have p2512_0 := h2512c.1
                        have p2512_1 := h2512c.2.1
                        have p2512_2 := h2512c.2.2.1
                        have p2512_3 := h2512c.2.2.2
                        linarith only [h1521, h1530, h1531, h1534, h1537, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2512_1]
                      · have p2512_0 := h2512c.1
                        have p2512_1 := h2512c.2.1
                        have p2512_2 := h2512c.2.2.1
                        have p2512_3 := h2512c.2.2.2
                        linarith only [hlam, p2512_0]
            · linarith only [h1533, h2390, hlam]
          · linarith only [h2389, hlam, p2374_0]
        · have p2374_0 := h2374c.1
          have p2374_1 := h2374c.2.1
          have p2374_2 := h2374c.2.2.1
          have p2374_3 := h2374c.2.2.2
          linarith only [h0, hc12, hlam, hphi, p2374_1, u1ehi0]
        · have p2374_0 := h2374c.1
          have p2374_1 := h2374c.2.1
          have p2374_2 := h2374c.2.2.1
          have p2374_3 := h2374c.2.2.2
          linarith only [hlam, p2374_0]
        · have p2374_0 := h2374c.1
          have p2374_1 := h2374c.2.1
          have p2374_2 := h2374c.2.2.1
          have p2374_3 := h2374c.2.2.2
          linarith only [h1521, h1530, h1531, h1534, h1537, h2165, hlam, p2374_2]
        · have p2374_0 := h2374c.1
          have p2374_1 := h2374c.2.1
          have p2374_2 := h2374c.2.2.1
          have p2374_3 := h2374c.2.2.2
          rcases p2374_3 (m.d 0 2) (by simp) with h2573 | h2573
          · linarith only [h0, h2573, hlam]
          · linarith only [h1526, h2573, hlam]
        · have p2374_0 := h2374c.1
          have p2374_1 := h2374c.2.1
          have p2374_2 := h2374c.2.2.1
          have p2374_3 := h2374c.2.2.2
          rcases p2374_3 (m.d 0 2) (by simp) with h2576 | h2576
          · linarith only [h0, h2576, hlam]
          · linarith only [h1527, h2576, hlam]
        · have p2374_0 := h2374c.1
          have p2374_1 := h2374c.2.1
          have p2374_2 := h2374c.2.2.1
          have p2374_3 := h2374c.2.2.2
          linarith only [h1525, hlam, p2374_0]
        · have p2374_0 := h2374c.1
          have p2374_1 := h2374c.2.1
          have p2374_2 := h2374c.2.2.1
          have p2374_3 := h2374c.2.2.2
          linarith only [h1531, hlam, p2374_0]
        · have p2374_0 := h2374c.1
          have p2374_1 := h2374c.2.1
          have p2374_2 := h2374c.2.2.1
          have p2374_3 := h2374c.2.2.2
          linarith only [hlam, p2374_0]
        · have p2374_0 := h2374c.1
          have p2374_1 := h2374c.2.1
          have p2374_2 := h2374c.2.2.1
          have p2374_3 := h2374c.2.2.2
          linarith only [h1537, hlam, p2374_1]
        · have p2374_0 := h2374c.1
          have p2374_1 := h2374c.2.1
          have p2374_2 := h2374c.2.2.1
          have p2374_3 := h2374c.2.2.2
          linarith only [h2056, hlam, p2374_1]
        · have p2374_0 := h2374c.1
          have p2374_1 := h2374c.2.1
          have p2374_2 := h2374c.2.2.1
          have p2374_3 := h2374c.2.2.2
          linarith only [h1526, hlam, p2374_0]
        · have p2374_0 := h2374c.1
          have p2374_1 := h2374c.2.1
          have p2374_2 := h2374c.2.2.1
          have p2374_3 := h2374c.2.2.2
          linarith only [h1532, hlam, p2374_0]
        · have p2374_0 := h2374c.1
          have p2374_1 := h2374c.2.1
          have p2374_2 := h2374c.2.2.1
          have p2374_3 := h2374c.2.2.2
          linarith only [h1521, h1530, h1531, h1534, h1537, h2165, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2374_1]
        · have p2374_0 := h2374c.1
          have p2374_1 := h2374c.2.1
          have p2374_2 := h2374c.2.2.1
          have p2374_3 := h2374c.2.2.2
          linarith only [hlam, p2374_0]
        · have p2374_0 := h2374c.1
          have p2374_1 := h2374c.2.1
          have p2374_2 := h2374c.2.2.1
          have p2374_3 := h2374c.2.2.2
          linarith only [h2058, hlam, p2374_0]
        · have p2374_0 := h2374c.1
          have p2374_1 := h2374c.2.1
          have p2374_2 := h2374c.2.2.1
          have p2374_3 := h2374c.2.2.2
          linarith only [h1527, hlam, p2374_0]
        · have p2374_0 := h2374c.1
          have p2374_1 := h2374c.2.1
          have p2374_2 := h2374c.2.2.1
          have p2374_3 := h2374c.2.2.2
          linarith only [h1533, hlam, p2374_0]
        · have p2374_0 := h2374c.1
          have p2374_1 := h2374c.2.1
          have p2374_2 := h2374c.2.2.1
          have p2374_3 := h2374c.2.2.2
          rcases p2374_3 (m.d 0 2) (by simp) with h2591 | h2591
          · rcases p2374_3 (m.d 1 2) (by simp) with h2592 | h2592
            · rcases p2374_3 (m.d 2 3) (by simp) with h2593 | h2593
              · linarith only [h2056, h2593, hlam]
              · rcases p2374_3 (m.d 2 4) (by simp) with h2595 | h2595
                · linarith only [h2058, h2595, hlam]
                · linarith only [h1537, h2595, hlam]
            · linarith only [h1531, h2592, hlam]
          · linarith only [h1525, h2591, hlam]
        · have p2374_0 := h2374c.1
          have p2374_1 := h2374c.2.1
          have p2374_2 := h2374c.2.2.1
          have p2374_3 := h2374c.2.2.2
          rcases p2374_3 (m.d 0 2) (by simp) with h2600 | h2600
          · rcases p2374_3 (m.d 1 2) (by simp) with h2601 | h2601
            · rcases p2374_3 (m.d 2 3) (by simp) with h2602 | h2602
              · linarith only [h2056, h2602, hlam]
              · rcases p2374_3 (m.d 2 4) (by simp) with h2604 | h2604
                · linarith only [h2058, h2604, hlam]
                · rcases p2374_3 (m.d 2 5) (by simp) with h2606 | h2606
                  · rcases h2emax with h2607 | h2607 | h2607 | h2607 | h2607
                    · linarith only [h1525, h1528, h1530, h2165, h2607, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h2607, hlam, ht12, u1ehi1]
                    · rcases h4bigk with h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c | h2610c
                      · have p2610_0 := h2610c.1
                        have p2610_1 := h2610c.2.1
                        have p2610_2 := h2610c.2.2.1
                        have p2610_3 := h2610c.2.2.2
                        linarith only [hlam, p2610_0]
                      · have p2610_0 := h2610c.1
                        have p2610_1 := h2610c.2.1
                        have p2610_2 := h2610c.2.2.1
                        have p2610_3 := h2610c.2.2.2
                        linarith only [h1521, hlam, p2610_1]
                      · have p2610_0 := h2610c.1
                        have p2610_1 := h2610c.2.1
                        have p2610_2 := h2610c.2.2.1
                        have p2610_3 := h2610c.2.2.2
                        linarith only [h1530, h2056, h2165, hlam, p2374_1, p2610_2]
                      · have p2610_0 := h2610c.1
                        have p2610_1 := h2610c.2.1
                        have p2610_2 := h2610c.2.2.1
                        have p2610_3 := h2610c.2.2.2
                        rcases p2610_3 (m.d 0 4) (by simp) with h2614 | h2614
                        · rcases p2610_3 (m.d 1 4) (by simp) with h2615 | h2615
                          · rcases p2610_3 (m.d 2 4) (by simp) with h2616 | h2616
                            · linarith only [h1526, h2616, hlam]
                            · rcases p2610_3 (m.d 3 4) (by simp) with h2618 | h2618
                              · linarith only [h1528, h2618, hlam]
                              · rcases p2610_3 (m.d 4 5) (by simp) with h2620 | h2620
                                · linarith only [h1530, h2620, hlam]
                                · linarith only [h2165, h2620, hlam]
                          · linarith only [h1534, h2615, hlam]
                        · linarith only [h1528, h2614, hlam]
                      · have p2610_0 := h2610c.1
                        have p2610_1 := h2610c.2.1
                        have p2610_2 := h2610c.2.2.1
                        have p2610_3 := h2610c.2.2.2
                        linarith only [h1525, h1528, h1537, h2056, h2165, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2374_1, p2610_1]
                      · have p2610_0 := h2610c.1
                        have p2610_1 := h2610c.2.1
                        have p2610_2 := h2610c.2.2.1
                        have p2610_3 := h2610c.2.2.2
                        linarith only [h1521, hc14, hlam, hphi, p2610_1, u1ehi0]
                      · have p2610_0 := h2610c.1
                        have p2610_1 := h2610c.2.1
                        have p2610_2 := h2610c.2.2.1
                        have p2610_3 := h2610c.2.2.2
                        linarith only [hlam, p2610_0]
                      · have p2610_0 := h2610c.1
                        have p2610_1 := h2610c.2.1
                        have p2610_2 := h2610c.2.2.1
                        have p2610_3 := h2610c.2.2.2
                        linarith only [h1521, h1530, h2056, h2165, hlam, p2374_1, p2610_2]
                      · have p2610_0 := h2610c.1
                        have p2610_1 := h2610c.2.1
                        have p2610_2 := h2610c.2.2.1
                        have p2610_3 := h2610c.2.2.2
                        rcases p2610_3 (m.d 0 4) (by simp) with h2629 | h2629
                        · linarith only [h1521, h2629, hlam]
                        · linarith only [h1528, h2629, hlam]
                      · have p2610_0 := h2610c.1
                        have p2610_1 := h2610c.2.1
                        have p2610_2 := h2610c.2.2.1
                        have p2610_3 := h2610c.2.2.2
                        linarith only [h1537, h2056, h2165, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2374_1, p2610_1]
                      · have p2610_0 := h2610c.1
                        have p2610_1 := h2610c.2.1
                        have p2610_2 := h2610c.2.2.1
                        have p2610_3 := h2610c.2.2.2
                        linarith only [h1526, hlam, p2610_0]
                      · have p2610_0 := h2610c.1
                        have p2610_1 := h2610c.2.1
                        have p2610_2 := h2610c.2.2.1
                        have p2610_3 := h2610c.2.2.2
                        linarith only [h1532, hlam, p2610_0]
                      · have p2610_0 := h2610c.1
                        have p2610_1 := h2610c.2.1
                        have p2610_2 := h2610c.2.2.1
                        have p2610_3 := h2610c.2.2.2
                        linarith only [hlam, p2610_0]
                      · have p2610_0 := h2610c.1
                        have p2610_1 := h2610c.2.1
                        have p2610_2 := h2610c.2.2.1
                        have p2610_3 := h2610c.2.2.2
                        linarith only [h1537, hlam, p2610_1]
                      · have p2610_0 := h2610c.1
                        have p2610_1 := h2610c.2.1
                        have p2610_2 := h2610c.2.2.1
                        have p2610_3 := h2610c.2.2.2
                        linarith only [h2058, hlam, p2610_0]
                      · have p2610_0 := h2610c.1
                        have p2610_1 := h2610c.2.1
                        have p2610_2 := h2610c.2.2.1
                        have p2610_3 := h2610c.2.2.2
                        linarith only [h1528, hlam, p2610_0]
                      · have p2610_0 := h2610c.1
                        have p2610_1 := h2610c.2.1
                        have p2610_2 := h2610c.2.2.1
                        have p2610_3 := h2610c.2.2.2
                        linarith only [h1534, hlam, p2610_0]
                      · have p2610_0 := h2610c.1
                        have p2610_1 := h2610c.2.1
                        have p2610_2 := h2610c.2.2.1
                        have p2610_3 := h2610c.2.2.2
                        linarith only [h1530, h1537, h2165, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2610_1]
                      · have p2610_0 := h2610c.1
                        have p2610_1 := h2610c.2.1
                        have p2610_2 := h2610c.2.2.1
                        have p2610_3 := h2610c.2.2.2
                        linarith only [hlam, p2610_0]
                      · have p2610_0 := h2610c.1
                        have p2610_1 := h2610c.2.1
                        have p2610_2 := h2610c.2.2.1
                        have p2610_3 := h2610c.2.2.2
                        linarith only [h2165, hlam, p2610_0]
                      · have p2610_0 := h2610c.1
                        have p2610_1 := h2610c.2.1
                        have p2610_2 := h2610c.2.2.1
                        have p2610_3 := h2610c.2.2.2
                        linarith only [h1530, hlam, p2610_0]
                      · have p2610_0 := h2610c.1
                        have p2610_1 := h2610c.2.1
                        have p2610_2 := h2610c.2.2.1
                        have p2610_3 := h2610c.2.2.2
                        linarith only [h1536, hlam, p2610_0]
                      · have p2610_0 := h2610c.1
                        have p2610_1 := h2610c.2.1
                        have p2610_2 := h2610c.2.2.1
                        have p2610_3 := h2610c.2.2.2
                        rcases p2610_3 (m.d 0 4) (by simp) with h2645 | h2645
                        · rcases p2610_3 (m.d 1 4) (by simp) with h2646 | h2646
                          · rcases p2610_3 (m.d 2 4) (by simp) with h2647 | h2647
                            · linarith only [h2647, hlam, p2610_0]
                            · rcases p2610_3 (m.d 3 4) (by simp) with h2649 | h2649
                              · linarith only [h2165, h2649, hlam]
                              · linarith only [h1537, h2649, hlam]
                          · linarith only [h1532, h2646, hlam]
                        · linarith only [h1526, h2645, hlam]
                      · have p2610_0 := h2610c.1
                        have p2610_1 := h2610c.2.1
                        have p2610_2 := h2610c.2.2.1
                        have p2610_3 := h2610c.2.2.2
                        linarith only [h1521, h1530, h1531, h1534, h1537, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2610_1]
                      · have p2610_0 := h2610c.1
                        have p2610_1 := h2610c.2.1
                        have p2610_2 := h2610c.2.2.1
                        have p2610_3 := h2610c.2.2.2
                        linarith only [hlam, p2610_0]
                    · rcases h4bigk with h2656c | h2656c | h2656c | h2656c | h2656c | h2656c | h2656c | h2656c | h2656c | h2656c | h2656c | h2656c | h2656c | h2656c | h2656c | h2656c | h2656c | h2656c | h2656c | h2656c | h2656c | h2656c | h2656c | h2656c | h2656c
                      · have p2656_0 := h2656c.1
                        have p2656_1 := h2656c.2.1
                        have p2656_2 := h2656c.2.2.1
                        have p2656_3 := h2656c.2.2.2
                        linarith only [hlam, p2656_0]
                      · have p2656_0 := h2656c.1
                        have p2656_1 := h2656c.2.1
                        have p2656_2 := h2656c.2.2.1
                        have p2656_3 := h2656c.2.2.2
                        linarith only [h1521, hlam, p2656_1]
                      · have p2656_0 := h2656c.1
                        have p2656_1 := h2656c.2.1
                        have p2656_2 := h2656c.2.2.1
                        have p2656_3 := h2656c.2.2.2
                        linarith only [h1530, h2058, hlam, p2374_1, p2656_2]
                      · have p2656_0 := h2656c.1
                        have p2656_1 := h2656c.2.1
                        have p2656_2 := h2656c.2.2.1
                        have p2656_3 := h2656c.2.2.2
                        rcases p2656_3 (m.d 0 4) (by simp) with h2660 | h2660
                        · rcases p2656_3 (m.d 1 4) (by simp) with h2661 | h2661
                          · rcases p2656_3 (m.d 2 4) (by simp) with h2662 | h2662
                            · linarith only [h1526, h2662, hlam]
                            · rcases p2656_3 (m.d 3 4) (by simp) with h2664 | h2664
                              · linarith only [h1528, h2664, hlam]
                              · rcases p2656_3 (m.d 4 5) (by simp) with h2666 | h2666
                                · linarith only [h1530, h2666, hlam]
                                · linarith only [h2165, h2666, hlam]
                          · linarith only [h1534, h2661, hlam]
                        · linarith only [h1528, h2660, hlam]
                      · have p2656_0 := h2656c.1
                        have p2656_1 := h2656c.2.1
                        have p2656_2 := h2656c.2.2.1
                        have p2656_3 := h2656c.2.2.2
                        linarith only [h1537, h2056, h2165, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2374_1, p2656_1]
                      · have p2656_0 := h2656c.1
                        have p2656_1 := h2656c.2.1
                        have p2656_2 := h2656c.2.2.1
                        have p2656_3 := h2656c.2.2.2
                        linarith only [h1521, h1531, h1534, hc12, hlam, hphi, p2656_1, u1ehi0]
                      · have p2656_0 := h2656c.1
                        have p2656_1 := h2656c.2.1
                        have p2656_2 := h2656c.2.2.1
                        have p2656_3 := h2656c.2.2.2
                        linarith only [hlam, p2656_0]
                      · have p2656_0 := h2656c.1
                        have p2656_1 := h2656c.2.1
                        have p2656_2 := h2656c.2.2.1
                        have p2656_3 := h2656c.2.2.2
                        linarith only [h1521, h1530, h2056, h2165, hlam, p2374_1, p2656_2]
                      · have p2656_0 := h2656c.1
                        have p2656_1 := h2656c.2.1
                        have p2656_2 := h2656c.2.2.1
                        have p2656_3 := h2656c.2.2.2
                        rcases p2656_3 (m.d 0 4) (by simp) with h2675 | h2675
                        · linarith only [h1521, h2675, hlam]
                        · linarith only [h1528, h2675, hlam]
                      · have p2656_0 := h2656c.1
                        have p2656_1 := h2656c.2.1
                        have p2656_2 := h2656c.2.2.1
                        have p2656_3 := h2656c.2.2.2
                        linarith only [h1537, h2056, h2165, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2374_1, p2656_1]
                      · have p2656_0 := h2656c.1
                        have p2656_1 := h2656c.2.1
                        have p2656_2 := h2656c.2.2.1
                        have p2656_3 := h2656c.2.2.2
                        linarith only [h1526, hlam, p2656_0]
                      · have p2656_0 := h2656c.1
                        have p2656_1 := h2656c.2.1
                        have p2656_2 := h2656c.2.2.1
                        have p2656_3 := h2656c.2.2.2
                        linarith only [h1532, hlam, p2656_0]
                      · have p2656_0 := h2656c.1
                        have p2656_1 := h2656c.2.1
                        have p2656_2 := h2656c.2.2.1
                        have p2656_3 := h2656c.2.2.2
                        linarith only [hlam, p2656_0]
                      · have p2656_0 := h2656c.1
                        have p2656_1 := h2656c.2.1
                        have p2656_2 := h2656c.2.2.1
                        have p2656_3 := h2656c.2.2.2
                        linarith only [h1537, hlam, p2656_1]
                      · have p2656_0 := h2656c.1
                        have p2656_1 := h2656c.2.1
                        have p2656_2 := h2656c.2.2.1
                        have p2656_3 := h2656c.2.2.2
                        linarith only [h2058, hlam, p2656_0]
                      · have p2656_0 := h2656c.1
                        have p2656_1 := h2656c.2.1
                        have p2656_2 := h2656c.2.2.1
                        have p2656_3 := h2656c.2.2.2
                        linarith only [h1528, hlam, p2656_0]
                      · have p2656_0 := h2656c.1
                        have p2656_1 := h2656c.2.1
                        have p2656_2 := h2656c.2.2.1
                        have p2656_3 := h2656c.2.2.2
                        linarith only [h1534, hlam, p2656_0]
                      · have p2656_0 := h2656c.1
                        have p2656_1 := h2656c.2.1
                        have p2656_2 := h2656c.2.2.1
                        have p2656_3 := h2656c.2.2.2
                        linarith only [h1530, h1537, h2165, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2656_1]
                      · have p2656_0 := h2656c.1
                        have p2656_1 := h2656c.2.1
                        have p2656_2 := h2656c.2.2.1
                        have p2656_3 := h2656c.2.2.2
                        linarith only [hlam, p2656_0]
                      · have p2656_0 := h2656c.1
                        have p2656_1 := h2656c.2.1
                        have p2656_2 := h2656c.2.2.1
                        have p2656_3 := h2656c.2.2.2
                        linarith only [h2165, hlam, p2656_0]
                      · have p2656_0 := h2656c.1
                        have p2656_1 := h2656c.2.1
                        have p2656_2 := h2656c.2.2.1
                        have p2656_3 := h2656c.2.2.2
                        linarith only [h1530, hlam, p2656_0]
                      · have p2656_0 := h2656c.1
                        have p2656_1 := h2656c.2.1
                        have p2656_2 := h2656c.2.2.1
                        have p2656_3 := h2656c.2.2.2
                        linarith only [h1536, hlam, p2656_0]
                      · have p2656_0 := h2656c.1
                        have p2656_1 := h2656c.2.1
                        have p2656_2 := h2656c.2.2.1
                        have p2656_3 := h2656c.2.2.2
                        rcases p2656_3 (m.d 0 4) (by simp) with h2691 | h2691
                        · rcases p2656_3 (m.d 1 4) (by simp) with h2692 | h2692
                          · rcases p2656_3 (m.d 2 4) (by simp) with h2693 | h2693
                            · linarith only [h2693, hlam, p2656_0]
                            · rcases p2656_3 (m.d 3 4) (by simp) with h2695 | h2695
                              · linarith only [h2165, h2695, hlam]
                              · linarith only [h1537, h2695, hlam]
                          · linarith only [h1532, h2692, hlam]
                        · linarith only [h1526, h2691, hlam]
                      · have p2656_0 := h2656c.1
                        have p2656_1 := h2656c.2.1
                        have p2656_2 := h2656c.2.2.1
                        have p2656_3 := h2656c.2.2.2
                        linarith only [h1521, h1530, h1531, h1534, h1537, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2656_1]
                      · have p2656_0 := h2656c.1
                        have p2656_1 := h2656c.2.1
                        have p2656_2 := h2656c.2.2.1
                        have p2656_3 := h2656c.2.2.2
                        linarith only [hlam, p2656_0]
                    · linarith only [h1537, h2607, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2374_1]
                  · linarith only [h2058, h2606, hlam]
            · linarith only [h1532, h2601, hlam]
          · linarith only [h1526, h2600, hlam]
        · have p2374_0 := h2374c.1
          have p2374_1 := h2374c.2.1
          have p2374_2 := h2374c.2.2.1
          have p2374_3 := h2374c.2.2.2
          linarith only [hlam, p2374_0]

set_option maxHeartbeats 5790000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1519 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1521 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1523 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1525 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1526 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1527 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1528 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1529 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1530 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1531 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h1532 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h1533 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1534 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1535 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1536 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 2 3 4 (by decide) (by decide) with h1537 | h1537
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 h0 h1519 h1521 h1523 h1525 h1526 h1527 h1528 h1529 h1530 h1531 h1532 h1533 h1534 h1535 h1536 h1537
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 h0 h1519 h1521 h1523 h1525 h1526 h1527 h1528 h1529 h1530 h1531 h1532 h1533 h1534 h1535 h1536 h1537

set_option maxHeartbeats 5790000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1519 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1521 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1523 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1525 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1526 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1527 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1528 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1529 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1530 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1531 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h1532 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h1533 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1534 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1535 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h1536 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  linarith only [h1521, h1530, h1536, hlam]

set_option maxHeartbeats 5790000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1519 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1521 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1523 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1525 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1526 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1527 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1528 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1529 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1530 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1531 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h1532 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h1533 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1534 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1535 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 4 5 (by decide) (by decide) with h1536 | h1536
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 h0 h1519 h1521 h1523 h1525 h1526 h1527 h1528 h1529 h1530 h1531 h1532 h1533 h1534 h1535 h1536
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 h0 h1519 h1521 h1523 h1525 h1526 h1527 h1528 h1529 h1530 h1531 h1532 h1533 h1534 h1535 h1536

set_option maxHeartbeats 5790000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1519 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1521 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1523 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1525 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1526 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1527 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1528 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1529 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1530 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1531 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h1532 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h1533 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1534 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h1535 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  linarith only [h1519, h1535, hc35, hlam, hphi, ht12, ht23, u1ehi0]

set_option maxHeartbeats 5790000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1519 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1521 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1523 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1525 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1526 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1527 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1528 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1529 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1530 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1531 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h1532 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h1533 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1534 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 3 5 (by decide) (by decide) with h1535 | h1535
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 h0 h1519 h1521 h1523 h1525 h1526 h1527 h1528 h1529 h1530 h1531 h1532 h1533 h1534 h1535
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 h0 h1519 h1521 h1523 h1525 h1526 h1527 h1528 h1529 h1530 h1531 h1532 h1533 h1534 h1535

set_option maxHeartbeats 5790000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1519 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1521 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1523 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1525 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1526 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1527 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1528 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1529 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1530 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1531 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h1532 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h1533 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h1534 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  linarith only [h1519, h1534, hc34, hlam, hphi, ht12, ht23, u1ehi0]

set_option maxHeartbeats 5790000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1519 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1521 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1523 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1525 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1526 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1527 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1528 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h1529 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h1530 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h1531 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h1532 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h1533 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 3 4 (by decide) (by decide) with h1534 | h1534
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 h0 h1519 h1521 h1523 h1525 h1526 h1527 h1528 h1529 h1530 h1531 h1532 h1533 h1534
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_M_IR_x1_x1_x1_x1_x0_x0_x0_x0_x0_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 h0 h1519 h1521 h1523 h1525 h1526 h1527 h1528 h1529 h1530 h1531 h1532 h1533 h1534

end R2N4
