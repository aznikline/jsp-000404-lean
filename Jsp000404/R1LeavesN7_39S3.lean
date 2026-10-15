import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_39S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7188000 in
theorem r1l7_11_13_25_L_I_L_0_H_I_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_11_13_25_L_I_L_0_H_I_x0_x0_x0_x0 m hb1 hb3 hb5 h0 h1 h2 h3
  · exact r1l7_11_13_25_L_I_L_0_H_I_x0_x0_x0_x1 m hb1 hb3 hb5 h0 h1 h2 h3

set_option maxHeartbeats 7188000 in
theorem r1l7_11_13_25_L_I_L_0_H_I_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2072 | h2072
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2073 | h2073
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2074 | h2074
      · linarith only [h1, h2, h2074, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2076 | h2076
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2077 | h2077
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2078 | h2078
            · linarith only [h0, h2, h2074, h2078, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2080 | h2080
              · linarith only [h1, h2, h2078, h2080, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2082 | h2082
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2083 | h2083
                  · linarith only [h1, h2, h2074, h2083, hlam]
                  · linarith only [h1, h2, h2078, h2083, hc12, hlam, hphi, ht23, u3elo3]
                · linarith only [h0, h2, h2073, h2080, h2082, hc12, hc24, hlam, hphi]
          · linarith only [h0, h2, h2074, h2076, h2077, hc12, hlam, hphi, ht23, u3elo3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2088 | h2088
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2089 | h2089
            · linarith only [h0, h2, h2074, h2089, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2091 | h2091
              · linarith only [h1, h2, h2089, h2091, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2093 | h2093
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2094 | h2094
                  · linarith only [h1, h2, h2074, h2094, hlam]
                  · linarith only [h1, h2, h2089, h2094, hc12, hlam, hphi, ht23, u3elo3]
                · linarith only [h0, h2, h2073, h2091, h2093, hc12, hc24, hlam, hphi]
          · linarith only [h0, h2, h2073, h2088, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2099 | h2099
      · linarith only [h1, h2, h2099, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2101 | h2101
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2102 | h2102
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2103 | h2103
            · linarith only [h0, h2073, h2099, h2101, h2103, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2105 | h2105
              · linarith only [h0, h2, h2073, h2099, h2101, h2105, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2107 | h2107
                · linarith only [h0, h2073, h2107, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2109 | h2109
                  · linarith only [h1, h2, h2073, h2099, h2101, h2109, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h1, h2, h2109, hc13, hlam, hphi, u3elo3]
          · linarith only [h1, h2, h2101, h2102, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2113 | h2113
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2114 | h2114
            · linarith only [h0, h2, h2099, h2114, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2116 | h2116
              · linarith only [h1, h2, h2114, h2116, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2118 | h2118
                · linarith only [h1, h2, h2073, h2099, h2114, h2118, hc02, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2120 | h2120
                  · linarith only [h1, h2, h2099, h2120, hlam]
                  · linarith only [h1, h2, h2114, h2120, hc12, hlam, hphi, ht23, u3elo3]
          · linarith only [h2, h2072, h2113, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h2124 | h2124
    · linarith only [h0, h2072, h2124, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2126 | h2126
      · linarith only [h1, h2, h2126, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2128 | h2128
        · linarith only [h0, h2072, h2126, h2128, hc12, hlam, hphi, ht23, u3elo3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2130 | h2130
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2131 | h2131
            · linarith only [h0, h2072, h2126, h2130, h2131, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2133 | h2133
              · linarith only [h1, h2, h2131, h2133, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2135 | h2135
                · linarith only [h1, h2072, h2124, h2126, h2130, h2131, h2135, hc02, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2137 | h2137
                  · linarith only [h1, h2072, h2126, h2130, h2137, hlam]
                  · linarith only [h1, h2, h2131, h2137, hc12, hlam, hphi, ht23, u3elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2140 | h2140
            · linarith only [h0, h2, h2128, h2130, h2140, hc23, hlam, hphi, u3elo4]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2142 | h2142
              · linarith only [h1, h2, h2130, h2140, h2142, hc24, hc45, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2144 | h2144
                · linarith only [h0, h2124, h2144, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2146 | h2146
                  · linarith only [h1, h2, h2126, h2128, h2130, h2146, hc03, hlam, hphi, u3elo4]
                  · linarith only [h1, h2, h2140, h2146, hc12, hlam, hphi, ht23, u3elo3]

set_option maxHeartbeats 7188000 in
theorem r1l7_11_13_25_L_I_L_0_H_I_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_11_13_25_L_I_L_0_H_I_x0_x0_x0 m hb1 hb3 hb5 h0 h1 h2
  · exact r1l7_11_13_25_L_I_L_0_H_I_x0_x0_x1 m hb1 hb3 hb5 h0 h1 h2

set_option maxHeartbeats 7188000 in
theorem r1l7_11_13_25_L_I_L_0_H_I_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h1bigk := hb1.1
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]

set_option maxHeartbeats 7188000 in
theorem r1l7_11_13_25_L_I_L_0_H_I_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_13_25_L_I_L_0_H_I_x0_x0 m hb1 hb3 hb5 h0 h1
  · exact r1l7_11_13_25_L_I_L_0_H_I_x0_x1 m hb1 hb3 hb5 h0 h1

set_option maxHeartbeats 7188000 in
theorem r1l7_11_13_25_L_I_L_0_H_I_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2150 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2151 | h2151
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2152 | h2152
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2153 | h2153
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2154 | h2154
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2155 | h2155
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2156 | h2156
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2157 | h2157
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2158 | h2158
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2159 | h2159
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2160 | h2160
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2161 | h2161
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2162 | h2162
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2163 | h2163
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2164 | h2164
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2165 | h2165
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2166 | h2166
                                · linarith only [h0, h2150, h2157, h2163, h2166, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h0, h2150, h2160, h2162, h2166, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h0, h2150, h2160, h2162, h2165, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h2155, h2164, hc23, hlam, hphi, u3elo0]
                          · linarith only [h2154, h2163, hc23, hlam, hphi, u3elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2172 | h2172
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2173 | h2173
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2174 | h2174
                              · linarith only [h2158, h2162, h2174, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2176 | h2176
                                · linarith only [h2158, h2162, h2172, h2176, hlam]
                                · rcases h1bigk with h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c | h2178c
                                  · have p2178_0 := h2178c.1
                                    have p2178_1 := h2178c.2.1
                                    have p2178_2 := h2178c.2.2.1
                                    have p2178_3 := h2178c.2.2.2
                                    linarith only [hlam, p2178_0]
                                  · have p2178_0 := h2178c.1
                                    have p2178_1 := h2178c.2.1
                                    have p2178_2 := h2178c.2.2.1
                                    have p2178_3 := h2178c.2.2.2
                                    linarith only [h0, hlam, p2178_0]
                                  · have p2178_0 := h2178c.1
                                    have p2178_1 := h2178c.2.1
                                    have p2178_2 := h2178c.2.2.1
                                    have p2178_3 := h2178c.2.2.2
                                    linarith only [h0, h2157, h2173, h2176, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2178_1]
                                  · have p2178_0 := h2178c.1
                                    have p2178_1 := h2178c.2.1
                                    have p2178_2 := h2178c.2.2.1
                                    have p2178_3 := h2178c.2.2.2
                                    rcases p2178_3 (m.d 0 1) (by simp) with h2182 | h2182
                                    · rcases p2178_3 (m.d 1 2) (by simp) with h2183 | h2183
                                      · rcases p2178_3 (m.d 1 3) (by simp) with h2184 | h2184
                                        · linarith only [h2150, h2184, hlam]
                                        · linarith only [h2160, h2184, hlam]
                                      · linarith only [h2158, h2183, hlam]
                                    · linarith only [h2182, hlam, p2178_0]
                                  · have p2178_0 := h2178c.1
                                    have p2178_1 := h2178c.2.1
                                    have p2178_2 := h2178c.2.2.1
                                    have p2178_3 := h2178c.2.2.2
                                    rcases p2178_3 (m.d 0 1) (by simp) with h2189 | h2189
                                    · rcases p2178_3 (m.d 1 2) (by simp) with h2190 | h2190
                                      · rcases p2178_3 (m.d 1 3) (by simp) with h2191 | h2191
                                        · linarith only [h2150, h2191, hlam]
                                        · linarith only [h2161, h2191, hlam]
                                      · linarith only [h2159, h2190, hlam]
                                    · linarith only [h2189, hlam, p2178_0]
                                  · have p2178_0 := h2178c.1
                                    have p2178_1 := h2178c.2.1
                                    have p2178_2 := h2178c.2.2.1
                                    have p2178_3 := h2178c.2.2.2
                                    linarith only [h2150, h2157, h2173, h2176, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2178_1]
                                  · have p2178_0 := h2178c.1
                                    have p2178_1 := h2178c.2.1
                                    have p2178_2 := h2178c.2.2.1
                                    have p2178_3 := h2178c.2.2.2
                                    linarith only [hlam, p2178_0]
                                  · have p2178_0 := h2178c.1
                                    have p2178_1 := h2178c.2.1
                                    have p2178_2 := h2178c.2.2.1
                                    have p2178_3 := h2178c.2.2.2
                                    rcases p2178_3 (m.d 0 1) (by simp) with h2198 | h2198
                                    · linarith only [h0, h2198, hlam]
                                    · linarith only [h2150, h2198, hlam]
                                  · have p2178_0 := h2178c.1
                                    have p2178_1 := h2178c.2.1
                                    have p2178_2 := h2178c.2.2.1
                                    have p2178_3 := h2178c.2.2.2
                                    linarith only [h0, h2150, h2154, h2156, h2162, hlam, p2178_2]
                                  · have p2178_0 := h2178c.1
                                    have p2178_1 := h2178c.2.1
                                    have p2178_2 := h2178c.2.2.1
                                    have p2178_3 := h2178c.2.2.2
                                    rcases p2178_3 (m.d 0 1) (by simp) with h2202 | h2202
                                    · linarith only [h0, h2202, hlam]
                                    · linarith only [h2152, h2202, hlam]
                                  · have p2178_0 := h2178c.1
                                    have p2178_1 := h2178c.2.1
                                    have p2178_2 := h2178c.2.2.1
                                    have p2178_3 := h2178c.2.2.2
                                    linarith only [h2150, hlam, p2178_0]
                                  · have p2178_0 := h2178c.1
                                    have p2178_1 := h2178c.2.1
                                    have p2178_2 := h2178c.2.2.1
                                    have p2178_3 := h2178c.2.2.2
                                    linarith only [h2157, hlam, p2178_1]
                                  · have p2178_0 := h2178c.1
                                    have p2178_1 := h2178c.2.1
                                    have p2178_2 := h2178c.2.2.1
                                    have p2178_3 := h2178c.2.2.2
                                    linarith only [hlam, p2178_0]
                                  · have p2178_0 := h2178c.1
                                    have p2178_1 := h2178c.2.1
                                    have p2178_2 := h2178c.2.2.1
                                    have p2178_3 := h2178c.2.2.2
                                    linarith only [h0, h2150, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2178_1]
                                  · have p2178_0 := h2178c.1
                                    have p2178_1 := h2178c.2.1
                                    have p2178_2 := h2178c.2.2.1
                                    have p2178_3 := h2178c.2.2.2
                                    linarith only [h0, h2150, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p2178_1]
                                  · have p2178_0 := h2178c.1
                                    have p2178_1 := h2178c.2.1
                                    have p2178_2 := h2178c.2.2.1
                                    have p2178_3 := h2178c.2.2.2
                                    linarith only [h2151, hlam, p2178_0]
                                  · have p2178_0 := h2178c.1
                                    have p2178_1 := h2178c.2.1
                                    have p2178_2 := h2178c.2.2.1
                                    have p2178_3 := h2178c.2.2.2
                                    linarith only [h2158, hlam, p2178_1]
                                  · have p2178_0 := h2178c.1
                                    have p2178_1 := h2178c.2.1
                                    have p2178_2 := h2178c.2.2.1
                                    have p2178_3 := h2178c.2.2.2
                                    linarith only [h2160, hlam, p2178_0]
                                  · have p2178_0 := h2178c.1
                                    have p2178_1 := h2178c.2.1
                                    have p2178_2 := h2178c.2.2.1
                                    have p2178_3 := h2178c.2.2.2
                                    linarith only [hlam, p2178_0]
                                  · have p2178_0 := h2178c.1
                                    have p2178_1 := h2178c.2.1
                                    have p2178_2 := h2178c.2.2.1
                                    have p2178_3 := h2178c.2.2.2
                                    linarith only [h2162, hlam, p2178_1]
                                  · have p2178_0 := h2178c.1
                                    have p2178_1 := h2178c.2.1
                                    have p2178_2 := h2178c.2.2.1
                                    have p2178_3 := h2178c.2.2.2
                                    linarith only [h2152, hlam, p2178_0]
                                  · have p2178_0 := h2178c.1
                                    have p2178_1 := h2178c.2.1
                                    have p2178_2 := h2178c.2.2.1
                                    have p2178_3 := h2178c.2.2.2
                                    linarith only [h2159, hlam, p2178_1]
                                  · have p2178_0 := h2178c.1
                                    have p2178_1 := h2178c.2.1
                                    have p2178_2 := h2178c.2.2.1
                                    have p2178_3 := h2178c.2.2.2
                                    linarith only [h2161, hlam, p2178_0]
                                  · have p2178_0 := h2178c.1
                                    have p2178_1 := h2178c.2.1
                                    have p2178_2 := h2178c.2.2.1
                                    have p2178_3 := h2178c.2.2.2
                                    linarith only [h0, h2152, h2158, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p2178_1]
                                  · have p2178_0 := h2178c.1
                                    have p2178_1 := h2178c.2.1
                                    have p2178_2 := h2178c.2.2.1
                                    have p2178_3 := h2178c.2.2.2
                                    linarith only [hlam, p2178_0]
                            · linarith only [h2155, h2173, hc23, hlam, hphi, u3elo0]
                          · linarith only [h2154, h2172, hc23, hlam, hphi, u3elo0]
                      · linarith only [h2155, h2161, hc13, hlam, hphi, u3elo0]
                    · linarith only [h2154, h2157, h2160, hc23, hlam, hphi, u3elo0]
                  · linarith only [h0, h2150, h2153, h2157, h2159, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h2151, h2158, hlam]
              · linarith only [h0, h2157, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2227 | h2227
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2228 | h2228
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2229 | h2229
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2230 | h2230
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2231 | h2231
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2232 | h2232
                        · linarith only [h2151, h2156, h2232, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2234 | h2234
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2235 | h2235
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2236 | h2236
                              · linarith only [h0, h2151, h2156, h2228, h2236, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2238 | h2238
                                · linarith only [h2151, h2156, h2228, h2234, h2238, hlam]
                                · rcases h1bigk with h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c | h2240c
                                  · have p2240_0 := h2240c.1
                                    have p2240_1 := h2240c.2.1
                                    have p2240_2 := h2240c.2.2.1
                                    have p2240_3 := h2240c.2.2.2
                                    linarith only [hlam, p2240_0]
                                  · have p2240_0 := h2240c.1
                                    have p2240_1 := h2240c.2.1
                                    have p2240_2 := h2240c.2.2.1
                                    have p2240_3 := h2240c.2.2.2
                                    linarith only [h0, hlam, p2240_0]
                                  · have p2240_0 := h2240c.1
                                    have p2240_1 := h2240c.2.1
                                    have p2240_2 := h2240c.2.2.1
                                    have p2240_3 := h2240c.2.2.2
                                    linarith only [h0, h2230, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2240_1]
                                  · have p2240_0 := h2240c.1
                                    have p2240_1 := h2240c.2.1
                                    have p2240_2 := h2240c.2.2.1
                                    have p2240_3 := h2240c.2.2.2
                                    rcases p2240_3 (m.d 0 1) (by simp) with h2244 | h2244
                                    · rcases p2240_3 (m.d 1 2) (by simp) with h2245 | h2245
                                      · rcases p2240_3 (m.d 1 3) (by simp) with h2246 | h2246
                                        · linarith only [h2150, h2246, hlam]
                                        · linarith only [h2230, h2246, hlam]
                                      · linarith only [h2228, h2245, hlam]
                                    · linarith only [h2244, hlam, p2240_0]
                                  · have p2240_0 := h2240c.1
                                    have p2240_1 := h2240c.2.1
                                    have p2240_2 := h2240c.2.2.1
                                    have p2240_3 := h2240c.2.2.2
                                    rcases p2240_3 (m.d 0 1) (by simp) with h2251 | h2251
                                    · rcases p2240_3 (m.d 1 2) (by simp) with h2252 | h2252
                                      · rcases p2240_3 (m.d 1 3) (by simp) with h2253 | h2253
                                        · linarith only [h2150, h2253, hlam]
                                        · linarith only [h2231, h2253, hlam]
                                      · linarith only [h2229, h2252, hlam]
                                    · linarith only [h2251, hlam, p2240_0]
                                  · have p2240_0 := h2240c.1
                                    have p2240_1 := h2240c.2.1
                                    have p2240_2 := h2240c.2.2.1
                                    have p2240_3 := h2240c.2.2.2
                                    linarith only [h2150, h2227, h2235, h2238, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2240_1]
                                  · have p2240_0 := h2240c.1
                                    have p2240_1 := h2240c.2.1
                                    have p2240_2 := h2240c.2.2.1
                                    have p2240_3 := h2240c.2.2.2
                                    linarith only [hlam, p2240_0]
                                  · have p2240_0 := h2240c.1
                                    have p2240_1 := h2240c.2.1
                                    have p2240_2 := h2240c.2.2.1
                                    have p2240_3 := h2240c.2.2.2
                                    rcases p2240_3 (m.d 0 1) (by simp) with h2260 | h2260
                                    · linarith only [h0, h2260, hlam]
                                    · linarith only [h2150, h2260, hlam]
                                  · have p2240_0 := h2240c.1
                                    have p2240_1 := h2240c.2.1
                                    have p2240_2 := h2240c.2.2.1
                                    have p2240_3 := h2240c.2.2.2
                                    rcases p2240_3 (m.d 0 1) (by simp) with h2263 | h2263
                                    · linarith only [h0, h2263, hlam]
                                    · linarith only [h2151, h2263, hlam]
                                  · have p2240_0 := h2240c.1
                                    have p2240_1 := h2240c.2.1
                                    have p2240_2 := h2240c.2.2.1
                                    have p2240_3 := h2240c.2.2.2
                                    rcases p2240_3 (m.d 0 1) (by simp) with h2266 | h2266
                                    · linarith only [h0, h2266, hlam]
                                    · linarith only [h2152, h2266, hlam]
                                  · have p2240_0 := h2240c.1
                                    have p2240_1 := h2240c.2.1
                                    have p2240_2 := h2240c.2.2.1
                                    have p2240_3 := h2240c.2.2.2
                                    linarith only [h2150, hlam, p2240_0]
                                  · have p2240_0 := h2240c.1
                                    have p2240_1 := h2240c.2.1
                                    have p2240_2 := h2240c.2.2.1
                                    have p2240_3 := h2240c.2.2.2
                                    linarith only [h2227, hlam, p2240_1]
                                  · have p2240_0 := h2240c.1
                                    have p2240_1 := h2240c.2.1
                                    have p2240_2 := h2240c.2.2.1
                                    have p2240_3 := h2240c.2.2.2
                                    linarith only [hlam, p2240_0]
                                  · have p2240_0 := h2240c.1
                                    have p2240_1 := h2240c.2.1
                                    have p2240_2 := h2240c.2.2.1
                                    have p2240_3 := h2240c.2.2.2
                                    linarith only [h0, h2150, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2240_1]
                                  · have p2240_0 := h2240c.1
                                    have p2240_1 := h2240c.2.1
                                    have p2240_2 := h2240c.2.2.1
                                    have p2240_3 := h2240c.2.2.2
                                    linarith only [h0, h2150, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p2240_1]
                                  · have p2240_0 := h2240c.1
                                    have p2240_1 := h2240c.2.1
                                    have p2240_2 := h2240c.2.2.1
                                    have p2240_3 := h2240c.2.2.2
                                    linarith only [h2151, hlam, p2240_0]
                                  · have p2240_0 := h2240c.1
                                    have p2240_1 := h2240c.2.1
                                    have p2240_2 := h2240c.2.2.1
                                    have p2240_3 := h2240c.2.2.2
                                    linarith only [h2228, hlam, p2240_1]
                                  · have p2240_0 := h2240c.1
                                    have p2240_1 := h2240c.2.1
                                    have p2240_2 := h2240c.2.2.1
                                    have p2240_3 := h2240c.2.2.2
                                    linarith only [h2230, hlam, p2240_0]
                                  · have p2240_0 := h2240c.1
                                    have p2240_1 := h2240c.2.1
                                    have p2240_2 := h2240c.2.2.1
                                    have p2240_3 := h2240c.2.2.2
                                    linarith only [hlam, p2240_0]
                                  · have p2240_0 := h2240c.1
                                    have p2240_1 := h2240c.2.1
                                    have p2240_2 := h2240c.2.2.1
                                    have p2240_3 := h2240c.2.2.2
                                    linarith only [h2232, hlam, p2240_1]
                                  · have p2240_0 := h2240c.1
                                    have p2240_1 := h2240c.2.1
                                    have p2240_2 := h2240c.2.2.1
                                    have p2240_3 := h2240c.2.2.2
                                    linarith only [h2152, hlam, p2240_0]
                                  · have p2240_0 := h2240c.1
                                    have p2240_1 := h2240c.2.1
                                    have p2240_2 := h2240c.2.2.1
                                    have p2240_3 := h2240c.2.2.2
                                    linarith only [h2229, hlam, p2240_1]
                                  · have p2240_0 := h2240c.1
                                    have p2240_1 := h2240c.2.1
                                    have p2240_2 := h2240c.2.2.1
                                    have p2240_3 := h2240c.2.2.2
                                    linarith only [h2231, hlam, p2240_0]
                                  · have p2240_0 := h2240c.1
                                    have p2240_1 := h2240c.2.1
                                    have p2240_2 := h2240c.2.2.1
                                    have p2240_3 := h2240c.2.2.2
                                    linarith only [h0, h2152, h2228, h2234, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2240_1]
                                  · have p2240_0 := h2240c.1
                                    have p2240_1 := h2240c.2.1
                                    have p2240_2 := h2240c.2.2.1
                                    have p2240_3 := h2240c.2.2.2
                                    linarith only [hlam, p2240_0]
                            · linarith only [h2155, h2235, hc23, hlam, hphi, u3elo0]
                          · linarith only [h2154, h2234, hc23, hlam, hphi, u3elo0]
                      · linarith only [h0, h2150, h2155, h2230, h2231, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h2154, h2230, hc13, hlam, hphi, u3elo0]
                  · linarith only [h0, h2150, h2153, h2155, h2229, hc02, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h2150, h2151, h2156, h2227, h2228, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h0, h2227, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2291 | h2291
            · linarith only [h2154, h2155, h2291, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2293 | h2293
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2294 | h2294
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2295 | h2295
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2296 | h2296
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2297 | h2297
                      · linarith only [h0, h2150, h2155, h2297, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2299 | h2299
                        · linarith only [h0, h2150, h2151, h2155, h2291, h2296, h2299, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2301 | h2301
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2302 | h2302
                            · linarith only [h2150, h2155, h2293, h2302, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2304 | h2304
                              · linarith only [h2151, h2291, h2294, h2304, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2306 | h2306
                                · linarith only [h2150, h2155, h2291, h2293, h2301, h2306, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                                · rcases h1bigk with h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c | h2308c
                                  · have p2308_0 := h2308c.1
                                    have p2308_1 := h2308c.2.1
                                    have p2308_2 := h2308c.2.2.1
                                    have p2308_3 := h2308c.2.2.2
                                    linarith only [hlam, p2308_0]
                                  · have p2308_0 := h2308c.1
                                    have p2308_1 := h2308c.2.1
                                    have p2308_2 := h2308c.2.2.1
                                    have p2308_3 := h2308c.2.2.2
                                    linarith only [h0, hlam, p2308_0]
                                  · have p2308_0 := h2308c.1
                                    have p2308_1 := h2308c.2.1
                                    have p2308_2 := h2308c.2.2.1
                                    have p2308_3 := h2308c.2.2.2
                                    linarith only [h0, h2296, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2308_1]
                                  · have p2308_0 := h2308c.1
                                    have p2308_1 := h2308c.2.1
                                    have p2308_2 := h2308c.2.2.1
                                    have p2308_3 := h2308c.2.2.2
                                    rcases p2308_3 (m.d 0 1) (by simp) with h2312 | h2312
                                    · rcases p2308_3 (m.d 1 2) (by simp) with h2313 | h2313
                                      · rcases p2308_3 (m.d 1 3) (by simp) with h2314 | h2314
                                        · linarith only [h2150, h2314, hlam]
                                        · linarith only [h2296, h2314, hlam]
                                      · linarith only [h2294, h2313, hlam]
                                    · linarith only [h2312, hlam, p2308_0]
                                  · have p2308_0 := h2308c.1
                                    have p2308_1 := h2308c.2.1
                                    have p2308_2 := h2308c.2.2.1
                                    have p2308_3 := h2308c.2.2.2
                                    linarith only [h0, h2293, h2297, h2301, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2308_1]
                                  · have p2308_0 := h2308c.1
                                    have p2308_1 := h2308c.2.1
                                    have p2308_2 := h2308c.2.2.1
                                    have p2308_3 := h2308c.2.2.2
                                    linarith only [h2150, h2293, h2301, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2308_1]
                                  · have p2308_0 := h2308c.1
                                    have p2308_1 := h2308c.2.1
                                    have p2308_2 := h2308c.2.2.1
                                    have p2308_3 := h2308c.2.2.2
                                    linarith only [hlam, p2308_0]
                                  · have p2308_0 := h2308c.1
                                    have p2308_1 := h2308c.2.1
                                    have p2308_2 := h2308c.2.2.1
                                    have p2308_3 := h2308c.2.2.2
                                    rcases p2308_3 (m.d 0 1) (by simp) with h2322 | h2322
                                    · linarith only [h0, h2322, hlam]
                                    · linarith only [h2150, h2322, hlam]
                                  · have p2308_0 := h2308c.1
                                    have p2308_1 := h2308c.2.1
                                    have p2308_2 := h2308c.2.2.1
                                    have p2308_3 := h2308c.2.2.2
                                    rcases p2308_3 (m.d 0 1) (by simp) with h2325 | h2325
                                    · linarith only [h0, h2325, hlam]
                                    · linarith only [h2151, h2325, hlam]
                                  · have p2308_0 := h2308c.1
                                    have p2308_1 := h2308c.2.1
                                    have p2308_2 := h2308c.2.2.1
                                    have p2308_3 := h2308c.2.2.2
                                    rcases p2308_3 (m.d 0 1) (by simp) with h2328 | h2328
                                    · linarith only [h0, h2328, hlam]
                                    · linarith only [h2152, h2328, hlam]
                                  · have p2308_0 := h2308c.1
                                    have p2308_1 := h2308c.2.1
                                    have p2308_2 := h2308c.2.2.1
                                    have p2308_3 := h2308c.2.2.2
                                    linarith only [h2150, hlam, p2308_0]
                                  · have p2308_0 := h2308c.1
                                    have p2308_1 := h2308c.2.1
                                    have p2308_2 := h2308c.2.2.1
                                    have p2308_3 := h2308c.2.2.2
                                    linarith only [h2293, hlam, p2308_1]
                                  · have p2308_0 := h2308c.1
                                    have p2308_1 := h2308c.2.1
                                    have p2308_2 := h2308c.2.2.1
                                    have p2308_3 := h2308c.2.2.2
                                    linarith only [hlam, p2308_0]
                                  · have p2308_0 := h2308c.1
                                    have p2308_1 := h2308c.2.1
                                    have p2308_2 := h2308c.2.2.1
                                    have p2308_3 := h2308c.2.2.2
                                    linarith only [h0, h2152, h2297, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2308_1]
                                  · have p2308_0 := h2308c.1
                                    have p2308_1 := h2308c.2.1
                                    have p2308_2 := h2308c.2.2.1
                                    have p2308_3 := h2308c.2.2.2
                                    linarith only [h2297, hlam, p2308_1]
                                  · have p2308_0 := h2308c.1
                                    have p2308_1 := h2308c.2.1
                                    have p2308_2 := h2308c.2.2.1
                                    have p2308_3 := h2308c.2.2.2
                                    linarith only [h2151, hlam, p2308_0]
                                  · have p2308_0 := h2308c.1
                                    have p2308_1 := h2308c.2.1
                                    have p2308_2 := h2308c.2.2.1
                                    have p2308_3 := h2308c.2.2.2
                                    linarith only [h2294, hlam, p2308_1]
                                  · have p2308_0 := h2308c.1
                                    have p2308_1 := h2308c.2.1
                                    have p2308_2 := h2308c.2.2.1
                                    have p2308_3 := h2308c.2.2.2
                                    linarith only [h2296, hlam, p2308_0]
                                  · have p2308_0 := h2308c.1
                                    have p2308_1 := h2308c.2.1
                                    have p2308_2 := h2308c.2.2.1
                                    have p2308_3 := h2308c.2.2.2
                                    linarith only [hlam, p2308_0]
                                  · have p2308_0 := h2308c.1
                                    have p2308_1 := h2308c.2.1
                                    have p2308_2 := h2308c.2.2.1
                                    have p2308_3 := h2308c.2.2.2
                                    linarith only [h2299, hlam, p2308_1]
                                  · have p2308_0 := h2308c.1
                                    have p2308_1 := h2308c.2.1
                                    have p2308_2 := h2308c.2.2.1
                                    have p2308_3 := h2308c.2.2.2
                                    linarith only [h2152, hlam, p2308_0]
                                  · have p2308_0 := h2308c.1
                                    have p2308_1 := h2308c.2.1
                                    have p2308_2 := h2308c.2.2.1
                                    have p2308_3 := h2308c.2.2.2
                                    linarith only [h2295, hlam, p2308_1]
                                  · have p2308_0 := h2308c.1
                                    have p2308_1 := h2308c.2.1
                                    have p2308_2 := h2308c.2.2.1
                                    have p2308_3 := h2308c.2.2.2
                                    linarith only [h0, h2152, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2308_1]
                                  · have p2308_0 := h2308c.1
                                    have p2308_1 := h2308c.2.1
                                    have p2308_2 := h2308c.2.2.1
                                    have p2308_3 := h2308c.2.2.2
                                    linarith only [h0, h2152, h2294, h2301, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2308_1]
                                  · have p2308_0 := h2308c.1
                                    have p2308_1 := h2308c.2.1
                                    have p2308_2 := h2308c.2.2.1
                                    have p2308_3 := h2308c.2.2.2
                                    linarith only [hlam, p2308_0]
                          · linarith only [h2154, h2155, h2301, hc23, hlam, hphi, u3elo4]
                    · linarith only [h2154, h2155, h2296, hc13, hlam, hphi, u3elo4]
                  · linarith only [h0, h2153, h2295, hlam]
                · linarith only [h0, h2151, h2294, hlam]
              · linarith only [h0, h2293, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2351 | h2351
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2352 | h2352
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2353 | h2353
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2354 | h2354
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2355 | h2355
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2356 | h2356
                    · linarith only [h0, h2150, h2154, h2356, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2358 | h2358
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2359 | h2359
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2360 | h2360
                          · linarith only [h2150, h2154, h2358, h2360, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2362 | h2362
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2363 | h2363
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2364 | h2364
                                · rcases h1bigk with h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c | h2365c
                                  · have p2365_0 := h2365c.1
                                    have p2365_1 := h2365c.2.1
                                    have p2365_2 := h2365c.2.2.1
                                    have p2365_3 := h2365c.2.2.2
                                    linarith only [hlam, p2365_0]
                                  · have p2365_0 := h2365c.1
                                    have p2365_1 := h2365c.2.1
                                    have p2365_2 := h2365c.2.2.1
                                    have p2365_3 := h2365c.2.2.2
                                    linarith only [h0, hlam, p2365_0]
                                  · have p2365_0 := h2365c.1
                                    have p2365_1 := h2365c.2.1
                                    have p2365_2 := h2365c.2.2.1
                                    have p2365_3 := h2365c.2.2.2
                                    linarith only [h0, h2353, h2362, h2364, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2365_1]
                                  · have p2365_0 := h2365c.1
                                    have p2365_1 := h2365c.2.1
                                    have p2365_2 := h2365c.2.2.1
                                    have p2365_3 := h2365c.2.2.2
                                    linarith only [h0, h2353, h2356, h2362, h2364, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2365_1]
                                  · have p2365_0 := h2365c.1
                                    have p2365_1 := h2365c.2.1
                                    have p2365_2 := h2365c.2.2.1
                                    have p2365_3 := h2365c.2.2.2
                                    rcases p2365_3 (m.d 0 1) (by simp) with h2370 | h2370
                                    · rcases p2365_3 (m.d 1 2) (by simp) with h2371 | h2371
                                      · rcases p2365_3 (m.d 1 3) (by simp) with h2372 | h2372
                                        · linarith only [h2150, h2372, hlam]
                                        · linarith only [h2358, h2372, hlam]
                                      · linarith only [h2355, h2371, hlam]
                                    · linarith only [h2370, hlam, p2365_0]
                                  · have p2365_0 := h2365c.1
                                    have p2365_1 := h2365c.2.1
                                    have p2365_2 := h2365c.2.2.1
                                    have p2365_3 := h2365c.2.2.2
                                    linarith only [h2150, h2353, h2362, h2364, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2365_1]
                                  · have p2365_0 := h2365c.1
                                    have p2365_1 := h2365c.2.1
                                    have p2365_2 := h2365c.2.2.1
                                    have p2365_3 := h2365c.2.2.2
                                    linarith only [hlam, p2365_0]
                                  · have p2365_0 := h2365c.1
                                    have p2365_1 := h2365c.2.1
                                    have p2365_2 := h2365c.2.2.1
                                    have p2365_3 := h2365c.2.2.2
                                    rcases p2365_3 (m.d 0 1) (by simp) with h2379 | h2379
                                    · linarith only [h0, h2379, hlam]
                                    · linarith only [h2150, h2379, hlam]
                                  · have p2365_0 := h2365c.1
                                    have p2365_1 := h2365c.2.1
                                    have p2365_2 := h2365c.2.2.1
                                    have p2365_3 := h2365c.2.2.2
                                    rcases p2365_3 (m.d 0 1) (by simp) with h2382 | h2382
                                    · linarith only [h0, h2382, hlam]
                                    · linarith only [h2151, h2382, hlam]
                                  · have p2365_0 := h2365c.1
                                    have p2365_1 := h2365c.2.1
                                    have p2365_2 := h2365c.2.2.1
                                    have p2365_3 := h2365c.2.2.2
                                    rcases p2365_3 (m.d 0 1) (by simp) with h2385 | h2385
                                    · linarith only [h0, h2385, hlam]
                                    · linarith only [h2152, h2385, hlam]
                                  · have p2365_0 := h2365c.1
                                    have p2365_1 := h2365c.2.1
                                    have p2365_2 := h2365c.2.2.1
                                    have p2365_3 := h2365c.2.2.2
                                    linarith only [h2150, hlam, p2365_0]
                                  · have p2365_0 := h2365c.1
                                    have p2365_1 := h2365c.2.1
                                    have p2365_2 := h2365c.2.2.1
                                    have p2365_3 := h2365c.2.2.2
                                    linarith only [h2353, hlam, p2365_1]
                                  · have p2365_0 := h2365c.1
                                    have p2365_1 := h2365c.2.1
                                    have p2365_2 := h2365c.2.2.1
                                    have p2365_3 := h2365c.2.2.2
                                    linarith only [hlam, p2365_0]
                                  · have p2365_0 := h2365c.1
                                    have p2365_1 := h2365c.2.1
                                    have p2365_2 := h2365c.2.2.1
                                    have p2365_3 := h2365c.2.2.2
                                    linarith only [h2356, hlam, p2365_1]
                                  · have p2365_0 := h2365c.1
                                    have p2365_1 := h2365c.2.1
                                    have p2365_2 := h2365c.2.2.1
                                    have p2365_3 := h2365c.2.2.2
                                    linarith only [h2150, h2154, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2365_1, u3elo3]
                                  · have p2365_0 := h2365c.1
                                    have p2365_1 := h2365c.2.1
                                    have p2365_2 := h2365c.2.2.1
                                    have p2365_3 := h2365c.2.2.2
                                    linarith only [h2151, hlam, p2365_0]
                                  · have p2365_0 := h2365c.1
                                    have p2365_1 := h2365c.2.1
                                    have p2365_2 := h2365c.2.2.1
                                    have p2365_3 := h2365c.2.2.2
                                    linarith only [h2354, hlam, p2365_1]
                                  · have p2365_0 := h2365c.1
                                    have p2365_1 := h2365c.2.1
                                    have p2365_2 := h2365c.2.2.1
                                    have p2365_3 := h2365c.2.2.2
                                    linarith only [h2151, h2353, h2362, hc01, hc35, hlam, hphi, ht0b, ht5b, p2365_1]
                                  · have p2365_0 := h2365c.1
                                    have p2365_1 := h2365c.2.1
                                    have p2365_2 := h2365c.2.2.1
                                    have p2365_3 := h2365c.2.2.2
                                    linarith only [hlam, p2365_0]
                                  · have p2365_0 := h2365c.1
                                    have p2365_1 := h2365c.2.1
                                    have p2365_2 := h2365c.2.2.1
                                    have p2365_3 := h2365c.2.2.2
                                    linarith only [h0, h2151, h2358, h2364, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2365_1]
                                  · have p2365_0 := h2365c.1
                                    have p2365_1 := h2365c.2.1
                                    have p2365_2 := h2365c.2.2.1
                                    have p2365_3 := h2365c.2.2.2
                                    linarith only [h2152, hlam, p2365_0]
                                  · have p2365_0 := h2365c.1
                                    have p2365_1 := h2365c.2.1
                                    have p2365_2 := h2365c.2.2.1
                                    have p2365_3 := h2365c.2.2.2
                                    linarith only [h2355, hlam, p2365_1]
                                  · have p2365_0 := h2365c.1
                                    have p2365_1 := h2365c.2.1
                                    have p2365_2 := h2365c.2.2.1
                                    have p2365_3 := h2365c.2.2.2
                                    linarith only [h2358, hlam, p2365_0]
                                  · have p2365_0 := h2365c.1
                                    have p2365_1 := h2365c.2.1
                                    have p2365_2 := h2365c.2.2.1
                                    have p2365_3 := h2365c.2.2.2
                                    linarith only [h2359, hlam, p2365_0]
                                  · have p2365_0 := h2365c.1
                                    have p2365_1 := h2365c.2.1
                                    have p2365_2 := h2365c.2.2.1
                                    have p2365_3 := h2365c.2.2.2
                                    linarith only [hlam, p2365_0]
                                · linarith only [h2150, h2154, h2352, h2353, h2362, h2364, hc04, hc35, hlam, hphi, ht0b, ht5b]
                              · linarith only [h0, h2151, h2359, h2363, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h2351, h2362, hc23, hlam, hphi, u3elo0]
                        · linarith only [h2154, h2351, h2352, h2356, h2359, hc13, hlam, hphi, u3elo3]
                      · linarith only [h2154, h2351, h2353, h2358, hc23, hlam, hphi, u3elo3]
                  · linarith only [h0, h2153, h2355, hlam]
                · linarith only [h0, h2151, h2354, hlam]
              · linarith only [h0, h2353, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h2154, h2351, h2352, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2412 | h2412
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2413 | h2413
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2414 | h2414
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2415 | h2415
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2416 | h2416
                    · linarith only [h0, h2150, h2154, h2416, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2418 | h2418
                      · linarith only [h2150, h2351, h2418, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2420 | h2420
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2421 | h2421
                          · linarith only [h2154, h2421, hc03, hlam, hphi, u3elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2423 | h2423
                            · linarith only [h2150, h2351, h2413, h2423, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2425 | h2425
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2426 | h2426
                                · rcases h1bigk with h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c | h2427c
                                  · have p2427_0 := h2427c.1
                                    have p2427_1 := h2427c.2.1
                                    have p2427_2 := h2427c.2.2.1
                                    have p2427_3 := h2427c.2.2.2
                                    linarith only [hlam, p2427_0]
                                  · have p2427_0 := h2427c.1
                                    have p2427_1 := h2427c.2.1
                                    have p2427_2 := h2427c.2.2.1
                                    have p2427_3 := h2427c.2.2.2
                                    linarith only [h0, hlam, p2427_0]
                                  · have p2427_0 := h2427c.1
                                    have p2427_1 := h2427c.2.1
                                    have p2427_2 := h2427c.2.2.1
                                    have p2427_3 := h2427c.2.2.2
                                    rcases p2427_3 (m.d 0 1) (by simp) with h2430 | h2430
                                    · rcases p2427_3 (m.d 1 2) (by simp) with h2431 | h2431
                                      · rcases p2427_3 (m.d 1 3) (by simp) with h2432 | h2432
                                        · linarith only [h2432, hlam, p2427_0]
                                        · rcases p2427_3 (m.d 1 4) (by simp) with h2434 | h2434
                                          · linarith only [h2151, h2434, hlam]
                                          · linarith only [h2416, h2434, hlam]
                                      · linarith only [h2413, h2431, hlam]
                                    · linarith only [h2430, hlam, p2427_0]
                                  · have p2427_0 := h2427c.1
                                    have p2427_1 := h2427c.2.1
                                    have p2427_2 := h2427c.2.2.1
                                    have p2427_3 := h2427c.2.2.2
                                    linarith only [h0, h2414, h2425, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2427_1]
                                  · have p2427_0 := h2427c.1
                                    have p2427_1 := h2427c.2.1
                                    have p2427_2 := h2427c.2.2.1
                                    have p2427_3 := h2427c.2.2.2
                                    rcases p2427_3 (m.d 0 1) (by simp) with h2440 | h2440
                                    · rcases p2427_3 (m.d 1 2) (by simp) with h2441 | h2441
                                      · rcases p2427_3 (m.d 1 3) (by simp) with h2442 | h2442
                                        · linarith only [h2150, h2442, hlam]
                                        · rcases p2427_3 (m.d 1 4) (by simp) with h2444 | h2444
                                          · linarith only [h2151, h2444, hlam]
                                          · linarith only [h2420, h2444, hlam]
                                      · linarith only [h2415, h2441, hlam]
                                    · linarith only [h2440, hlam, p2427_0]
                                  · have p2427_0 := h2427c.1
                                    have p2427_1 := h2427c.2.1
                                    have p2427_2 := h2427c.2.2.1
                                    have p2427_3 := h2427c.2.2.2
                                    linarith only [h2151, h2414, h2425, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2427_1]
                                  · have p2427_0 := h2427c.1
                                    have p2427_1 := h2427c.2.1
                                    have p2427_2 := h2427c.2.2.1
                                    have p2427_3 := h2427c.2.2.2
                                    linarith only [hlam, p2427_0]
                                  · have p2427_0 := h2427c.1
                                    have p2427_1 := h2427c.2.1
                                    have p2427_2 := h2427c.2.2.1
                                    have p2427_3 := h2427c.2.2.2
                                    rcases p2427_3 (m.d 0 1) (by simp) with h2451 | h2451
                                    · linarith only [h0, h2451, hlam]
                                    · linarith only [h2150, h2451, hlam]
                                  · have p2427_0 := h2427c.1
                                    have p2427_1 := h2427c.2.1
                                    have p2427_2 := h2427c.2.2.1
                                    have p2427_3 := h2427c.2.2.2
                                    rcases p2427_3 (m.d 0 1) (by simp) with h2454 | h2454
                                    · linarith only [h0, h2454, hlam]
                                    · linarith only [h2151, h2454, hlam]
                                  · have p2427_0 := h2427c.1
                                    have p2427_1 := h2427c.2.1
                                    have p2427_2 := h2427c.2.2.1
                                    have p2427_3 := h2427c.2.2.2
                                    rcases p2427_3 (m.d 0 1) (by simp) with h2457 | h2457
                                    · linarith only [h0, h2457, hlam]
                                    · linarith only [h2152, h2457, hlam]
                                  · have p2427_0 := h2427c.1
                                    have p2427_1 := h2427c.2.1
                                    have p2427_2 := h2427c.2.2.1
                                    have p2427_3 := h2427c.2.2.2
                                    linarith only [h2150, hlam, p2427_0]
                                  · have p2427_0 := h2427c.1
                                    have p2427_1 := h2427c.2.1
                                    have p2427_2 := h2427c.2.2.1
                                    have p2427_3 := h2427c.2.2.2
                                    linarith only [h2413, hlam, p2427_1]
                                  · have p2427_0 := h2427c.1
                                    have p2427_1 := h2427c.2.1
                                    have p2427_2 := h2427c.2.2.1
                                    have p2427_3 := h2427c.2.2.2
                                    linarith only [hlam, p2427_0]
                                  · have p2427_0 := h2427c.1
                                    have p2427_1 := h2427c.2.1
                                    have p2427_2 := h2427c.2.2.1
                                    have p2427_3 := h2427c.2.2.2
                                    linarith only [h2416, hlam, p2427_1]
                                  · have p2427_0 := h2427c.1
                                    have p2427_1 := h2427c.2.1
                                    have p2427_2 := h2427c.2.2.1
                                    have p2427_3 := h2427c.2.2.2
                                    linarith only [h2418, hlam, p2427_1]
                                  · have p2427_0 := h2427c.1
                                    have p2427_1 := h2427c.2.1
                                    have p2427_2 := h2427c.2.2.1
                                    have p2427_3 := h2427c.2.2.2
                                    linarith only [h2151, hlam, p2427_0]
                                  · have p2427_0 := h2427c.1
                                    have p2427_1 := h2427c.2.1
                                    have p2427_2 := h2427c.2.2.1
                                    have p2427_3 := h2427c.2.2.2
                                    linarith only [h2414, hlam, p2427_1]
                                  · have p2427_0 := h2427c.1
                                    have p2427_1 := h2427c.2.1
                                    have p2427_2 := h2427c.2.2.1
                                    have p2427_3 := h2427c.2.2.2
                                    linarith only [h0, h2151, h2413, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2427_1]
                                  · have p2427_0 := h2427c.1
                                    have p2427_1 := h2427c.2.1
                                    have p2427_2 := h2427c.2.2.1
                                    have p2427_3 := h2427c.2.2.2
                                    linarith only [hlam, p2427_0]
                                  · have p2427_0 := h2427c.1
                                    have p2427_1 := h2427c.2.1
                                    have p2427_2 := h2427c.2.2.1
                                    have p2427_3 := h2427c.2.2.2
                                    linarith only [h2151, h2154, h2413, h2418, hc23, hlam, hphi, p2427_1, u3elo3]
                                  · have p2427_0 := h2427c.1
                                    have p2427_1 := h2427c.2.1
                                    have p2427_2 := h2427c.2.2.1
                                    have p2427_3 := h2427c.2.2.2
                                    linarith only [h2152, hlam, p2427_0]
                                  · have p2427_0 := h2427c.1
                                    have p2427_1 := h2427c.2.1
                                    have p2427_2 := h2427c.2.2.1
                                    have p2427_3 := h2427c.2.2.2
                                    linarith only [h2415, hlam, p2427_1]
                                  · have p2427_0 := h2427c.1
                                    have p2427_1 := h2427c.2.1
                                    have p2427_2 := h2427c.2.2.1
                                    have p2427_3 := h2427c.2.2.2
                                    linarith only [h0, h2152, h2413, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2427_1]
                                  · have p2427_0 := h2427c.1
                                    have p2427_1 := h2427c.2.1
                                    have p2427_2 := h2427c.2.2.1
                                    have p2427_3 := h2427c.2.2.2
                                    linarith only [h2420, hlam, p2427_0]
                                  · have p2427_0 := h2427c.1
                                    have p2427_1 := h2427c.2.1
                                    have p2427_2 := h2427c.2.2.1
                                    have p2427_3 := h2427c.2.2.2
                                    linarith only [hlam, p2427_0]
                                · linarith only [h2154, h2412, h2426, hlam]
                              · linarith only [h0, h2151, h2420, h2425, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h2154, h2412, h2413, h2416, h2420, hc23, hlam, hphi, u3elo3]
                  · linarith only [h0, h2153, h2415, hlam]
                · linarith only [h0, h2151, h2414, hlam]
              · linarith only [h0, h2413, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2481 | h2481
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2482 | h2482
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2483 | h2483
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2484 | h2484
                    · linarith only [h2150, h2154, h2484, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2486 | h2486
                      · linarith only [h2150, h2351, h2486, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2488 | h2488
                        · linarith only [h0, h2151, h2412, h2488, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2490 | h2490
                          · linarith only [h2150, h2154, h2481, h2490, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2492 | h2492
                            · linarith only [h2150, h2351, h2481, h2492, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2494 | h2494
                              · linarith only [h0, h2151, h2154, h2412, h2482, h2494, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2496 | h2496
                                · linarith only [h2150, h2154, h2412, h2481, h2496, hc23, hlam, hphi, u3elo3]
                                · rcases h1bigk with h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c | h2498c
                                  · have p2498_0 := h2498c.1
                                    have p2498_1 := h2498c.2.1
                                    have p2498_2 := h2498c.2.2.1
                                    have p2498_3 := h2498c.2.2.2
                                    linarith only [hlam, p2498_0]
                                  · have p2498_0 := h2498c.1
                                    have p2498_1 := h2498c.2.1
                                    have p2498_2 := h2498c.2.2.1
                                    have p2498_3 := h2498c.2.2.2
                                    linarith only [h0, hlam, p2498_0]
                                  · have p2498_0 := h2498c.1
                                    have p2498_1 := h2498c.2.1
                                    have p2498_2 := h2498c.2.2.1
                                    have p2498_3 := h2498c.2.2.2
                                    rcases p2498_3 (m.d 0 1) (by simp) with h2501 | h2501
                                    · rcases p2498_3 (m.d 1 2) (by simp) with h2502 | h2502
                                      · rcases p2498_3 (m.d 1 3) (by simp) with h2503 | h2503
                                        · linarith only [h2503, hlam, p2498_0]
                                        · rcases p2498_3 (m.d 1 4) (by simp) with h2505 | h2505
                                          · linarith only [h2151, h2505, hlam]
                                          · linarith only [h2484, h2505, hlam]
                                      · linarith only [h2481, h2502, hlam]
                                    · linarith only [h2501, hlam, p2498_0]
                                  · have p2498_0 := h2498c.1
                                    have p2498_1 := h2498c.2.1
                                    have p2498_2 := h2498c.2.2.1
                                    have p2498_3 := h2498c.2.2.2
                                    rcases p2498_3 (m.d 0 1) (by simp) with h2510 | h2510
                                    · rcases p2498_3 (m.d 1 2) (by simp) with h2511 | h2511
                                      · rcases p2498_3 (m.d 1 3) (by simp) with h2512 | h2512
                                        · linarith only [h2150, h2512, hlam]
                                        · rcases p2498_3 (m.d 1 4) (by simp) with h2514 | h2514
                                          · linarith only [h2514, hlam, p2498_0]
                                          · rcases p2498_3 (m.d 1 5) (by simp) with h2516 | h2516
                                            · linarith only [h2152, h2516, hlam]
                                            · linarith only [h2488, h2516, hlam]
                                      · linarith only [h2482, h2511, hlam]
                                    · linarith only [h2510, hlam, p2498_0]
                                  · have p2498_0 := h2498c.1
                                    have p2498_1 := h2498c.2.1
                                    have p2498_2 := h2498c.2.2.1
                                    have p2498_3 := h2498c.2.2.2
                                    rcases p2498_3 (m.d 0 1) (by simp) with h2521 | h2521
                                    · rcases p2498_3 (m.d 1 2) (by simp) with h2522 | h2522
                                      · rcases p2498_3 (m.d 1 3) (by simp) with h2523 | h2523
                                        · linarith only [h2150, h2523, hlam]
                                        · rcases p2498_3 (m.d 1 4) (by simp) with h2525 | h2525
                                          · linarith only [h2151, h2525, hlam]
                                          · rcases p2498_3 (m.d 1 5) (by simp) with h2527 | h2527
                                            · linarith only [h2527, hlam, p2498_0]
                                            · rcases h1emin with h2529 | h2529 | h2529 | h2529 | h2529
                                              · linarith only [h0, h2529, hc12, hlam]
                                              · rcases h5bigk with h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c | h2531c
                                                · have p2531_0 := h2531c.1
                                                  have p2531_1 := h2531c.2.1
                                                  have p2531_2 := h2531c.2.2.1
                                                  have p2531_3 := h2531c.2.2.2
                                                  linarith only [hlam, p2531_0]
                                                · have p2531_0 := h2531c.1
                                                  have p2531_1 := h2531c.2.1
                                                  have p2531_2 := h2531c.2.2.1
                                                  have p2531_3 := h2531c.2.2.2
                                                  linarith only [h0, h2152, h2482, h2488, h2490, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2531_1]
                                                · have p2531_0 := h2531c.1
                                                  have p2531_1 := h2531c.2.1
                                                  have p2531_2 := h2531c.2.2.1
                                                  have p2531_3 := h2531c.2.2.2
                                                  linarith only [h0, h2152, h2490, h2494, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2531_1]
                                                · have p2531_0 := h2531c.1
                                                  have p2531_1 := h2531c.2.1
                                                  have p2531_2 := h2531c.2.2.1
                                                  have p2531_3 := h2531c.2.2.2
                                                  linarith only [h2351, hlam, p2531_1]
                                                · have p2531_0 := h2531c.1
                                                  have p2531_1 := h2531c.2.1
                                                  have p2531_2 := h2531c.2.2.1
                                                  have p2531_3 := h2531c.2.2.2
                                                  linarith only [h2412, hlam, p2531_1]
                                                · have p2531_0 := h2531c.1
                                                  have p2531_1 := h2531c.2.1
                                                  have p2531_2 := h2531c.2.2.1
                                                  have p2531_3 := h2531c.2.2.2
                                                  linarith only [h2152, hlam, p2531_0]
                                                · have p2531_0 := h2531c.1
                                                  have p2531_1 := h2531c.2.1
                                                  have p2531_2 := h2531c.2.2.1
                                                  have p2531_3 := h2531c.2.2.2
                                                  linarith only [hlam, p2531_0]
                                                · have p2531_0 := h2531c.1
                                                  have p2531_1 := h2531c.2.1
                                                  have p2531_2 := h2531c.2.2.1
                                                  have p2531_3 := h2531c.2.2.2
                                                  linarith only [h0, h2490, h2494, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2498_1, p2531_1]
                                                · have p2531_0 := h2531c.1
                                                  have p2531_1 := h2531c.2.1
                                                  have p2531_2 := h2531c.2.2.1
                                                  have p2531_3 := h2531c.2.2.2
                                                  linarith only [h2486, hlam, p2531_1]
                                                · have p2531_0 := h2531c.1
                                                  have p2531_1 := h2531c.2.1
                                                  have p2531_2 := h2531c.2.2.1
                                                  have p2531_3 := h2531c.2.2.2
                                                  linarith only [h2488, hlam, p2531_1]
                                                · have p2531_0 := h2531c.1
                                                  have p2531_1 := h2531c.2.1
                                                  have p2531_2 := h2531c.2.2.1
                                                  have p2531_3 := h2531c.2.2.2
                                                  linarith only [h2153, hlam, p2531_1]
                                                · have p2531_0 := h2531c.1
                                                  have p2531_1 := h2531c.2.1
                                                  have p2531_2 := h2531c.2.2.1
                                                  have p2531_3 := h2531c.2.2.2
                                                  linarith only [h2483, hlam, p2531_1]
                                                · have p2531_0 := h2531c.1
                                                  have p2531_1 := h2531c.2.1
                                                  have p2531_2 := h2531c.2.2.1
                                                  have p2531_3 := h2531c.2.2.2
                                                  linarith only [hlam, p2531_0]
                                                · have p2531_0 := h2531c.1
                                                  have p2531_1 := h2531c.2.1
                                                  have p2531_2 := h2531c.2.2.1
                                                  have p2531_3 := h2531c.2.2.2
                                                  linarith only [h2492, hlam, p2531_1]
                                                · have p2531_0 := h2531c.1
                                                  have p2531_1 := h2531c.2.1
                                                  have p2531_2 := h2531c.2.2.1
                                                  have p2531_3 := h2531c.2.2.2
                                                  linarith only [h2494, hlam, p2531_1]
                                                · have p2531_0 := h2531c.1
                                                  have p2531_1 := h2531c.2.1
                                                  have p2531_2 := h2531c.2.2.1
                                                  have p2531_3 := h2531c.2.2.2
                                                  linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2531_1, u3elo4]
                                                · have p2531_0 := h2531c.1
                                                  have p2531_1 := h2531c.2.1
                                                  have p2531_2 := h2531c.2.2.1
                                                  have p2531_3 := h2531c.2.2.2
                                                  linarith only [h2483, h2490, h2494, hc23, hlam, hphi, p2531_1, u3elo4]
                                                · have p2531_0 := h2531c.1
                                                  have p2531_1 := h2531c.2.1
                                                  have p2531_2 := h2531c.2.2.1
                                                  have p2531_3 := h2531c.2.2.2
                                                  linarith only [h2490, h2494, hc23, hlam, hphi, p2531_1, u3elo4]
                                                · have p2531_0 := h2531c.1
                                                  have p2531_1 := h2531c.2.1
                                                  have p2531_2 := h2531c.2.2.1
                                                  have p2531_3 := h2531c.2.2.2
                                                  linarith only [hlam, p2531_0]
                                                · have p2531_0 := h2531c.1
                                                  have p2531_1 := h2531c.2.1
                                                  have p2531_2 := h2531c.2.2.1
                                                  have p2531_3 := h2531c.2.2.2
                                                  linarith only [h2496, hlam, p2531_1]
                                                · have p2531_0 := h2531c.1
                                                  have p2531_1 := h2531c.2.1
                                                  have p2531_2 := h2531c.2.2.1
                                                  have p2531_3 := h2531c.2.2.2
                                                  linarith only [h2150, h2154, h2412, h2481, hc23, hc45, hlam, hphi, ht34, p2531_1]
                                                · have p2531_0 := h2531c.1
                                                  have p2531_1 := h2531c.2.1
                                                  have p2531_2 := h2531c.2.2.1
                                                  have p2531_3 := h2531c.2.2.2
                                                  linarith only [h2483, h2490, h2494, hc23, hc45, hlam, hphi, ht34, p2531_1]
                                                · have p2531_0 := h2531c.1
                                                  have p2531_1 := h2531c.2.1
                                                  have p2531_2 := h2531c.2.2.1
                                                  have p2531_3 := h2531c.2.2.2
                                                  linarith only [h2490, h2494, hc23, hc45, hlam, hphi, ht34, p2531_1]
                                                · have p2531_0 := h2531c.1
                                                  have p2531_1 := h2531c.2.1
                                                  have p2531_2 := h2531c.2.2.1
                                                  have p2531_3 := h2531c.2.2.2
                                                  linarith only [h2150, h2351, h2481, hc23, hc45, hlam, hphi, ht34, p2531_1]
                                                · have p2531_0 := h2531c.1
                                                  have p2531_1 := h2531c.2.1
                                                  have p2531_2 := h2531c.2.2.1
                                                  have p2531_3 := h2531c.2.2.2
                                                  linarith only [hlam, p2531_0]
                                              · linarith only [h0, h2150, h2154, h2483, h2490, h2494, h2529, hc12, hc23, hlam, hphi, p2498_1, u3elo3]
                                              · linarith only [h0, h2151, h2529, hc12, hlam]
                                              · linarith only [h0, h2529, hc12, hlam, p2498_1]
                                      · linarith only [h2483, h2522, hlam]
                                    · linarith only [h2521, hlam, p2498_0]
                                  · have p2498_0 := h2498c.1
                                    have p2498_1 := h2498c.2.1
                                    have p2498_2 := h2498c.2.2.1
                                    have p2498_3 := h2498c.2.2.2
                                    rcases p2498_3 (m.d 0 1) (by simp) with h2562 | h2562
                                    · linarith only [h2562, hlam, p2498_0]
                                    · rcases p2498_3 (m.d 1 2) (by simp) with h2564 | h2564
                                      · rcases p2498_3 (m.d 1 3) (by simp) with h2565 | h2565
                                        · linarith only [h2481, h2565, hlam]
                                        · rcases p2498_3 (m.d 1 4) (by simp) with h2567 | h2567
                                          · linarith only [h2482, h2567, hlam]
                                          · rcases p2498_3 (m.d 1 5) (by simp) with h2569 | h2569
                                            · linarith only [h2483, h2569, hlam]
                                            · rcases h1emin with h2571 | h2571 | h2571 | h2571 | h2571
                                              · linarith only [h2571, hc12, hlam, p2498_1]
                                              · rcases h5bigk with h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c | h2573c
                                                · have p2573_0 := h2573c.1
                                                  have p2573_1 := h2573c.2.1
                                                  have p2573_2 := h2573c.2.2.1
                                                  have p2573_3 := h2573c.2.2.2
                                                  linarith only [hlam, p2573_0]
                                                · have p2573_0 := h2573c.1
                                                  have p2573_1 := h2573c.2.1
                                                  have p2573_2 := h2573c.2.2.1
                                                  have p2573_3 := h2573c.2.2.2
                                                  linarith only [h2152, h2484, h2488, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2498_1, p2573_1]
                                                · have p2573_0 := h2573c.1
                                                  have p2573_1 := h2573c.2.1
                                                  have p2573_2 := h2573c.2.2.1
                                                  have p2573_3 := h2573c.2.2.2
                                                  linarith only [h2152, h2490, h2494, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2498_1, p2573_1]
                                                · have p2573_0 := h2573c.1
                                                  have p2573_1 := h2573c.2.1
                                                  have p2573_2 := h2573c.2.2.1
                                                  have p2573_3 := h2573c.2.2.2
                                                  linarith only [h2351, hlam, p2573_1]
                                                · have p2573_0 := h2573c.1
                                                  have p2573_1 := h2573c.2.1
                                                  have p2573_2 := h2573c.2.2.1
                                                  have p2573_3 := h2573c.2.2.2
                                                  linarith only [h2412, hlam, p2573_1]
                                                · have p2573_0 := h2573c.1
                                                  have p2573_1 := h2573c.2.1
                                                  have p2573_2 := h2573c.2.2.1
                                                  have p2573_3 := h2573c.2.2.2
                                                  linarith only [h2152, hlam, p2573_0]
                                                · have p2573_0 := h2573c.1
                                                  have p2573_1 := h2573c.2.1
                                                  have p2573_2 := h2573c.2.2.1
                                                  have p2573_3 := h2573c.2.2.2
                                                  linarith only [hlam, p2573_0]
                                                · have p2573_0 := h2573c.1
                                                  have p2573_1 := h2573c.2.1
                                                  have p2573_2 := h2573c.2.2.1
                                                  have p2573_3 := h2573c.2.2.2
                                                  linarith only [h2152, h2490, h2494, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2498_1, p2573_1]
                                                · have p2573_0 := h2573c.1
                                                  have p2573_1 := h2573c.2.1
                                                  have p2573_2 := h2573c.2.2.1
                                                  have p2573_3 := h2573c.2.2.2
                                                  linarith only [h2486, hlam, p2573_1]
                                                · have p2573_0 := h2573c.1
                                                  have p2573_1 := h2573c.2.1
                                                  have p2573_2 := h2573c.2.2.1
                                                  have p2573_3 := h2573c.2.2.2
                                                  linarith only [h2488, hlam, p2573_1]
                                                · have p2573_0 := h2573c.1
                                                  have p2573_1 := h2573c.2.1
                                                  have p2573_2 := h2573c.2.2.1
                                                  have p2573_3 := h2573c.2.2.2
                                                  linarith only [h2153, hlam, p2573_1]
                                                · have p2573_0 := h2573c.1
                                                  have p2573_1 := h2573c.2.1
                                                  have p2573_2 := h2573c.2.2.1
                                                  have p2573_3 := h2573c.2.2.2
                                                  linarith only [h2483, hlam, p2573_1]
                                                · have p2573_0 := h2573c.1
                                                  have p2573_1 := h2573c.2.1
                                                  have p2573_2 := h2573c.2.2.1
                                                  have p2573_3 := h2573c.2.2.2
                                                  linarith only [hlam, p2573_0]
                                                · have p2573_0 := h2573c.1
                                                  have p2573_1 := h2573c.2.1
                                                  have p2573_2 := h2573c.2.2.1
                                                  have p2573_3 := h2573c.2.2.2
                                                  linarith only [h2492, hlam, p2573_1]
                                                · have p2573_0 := h2573c.1
                                                  have p2573_1 := h2573c.2.1
                                                  have p2573_2 := h2573c.2.2.1
                                                  have p2573_3 := h2573c.2.2.2
                                                  linarith only [h2494, hlam, p2573_1]
                                                · have p2573_0 := h2573c.1
                                                  have p2573_1 := h2573c.2.1
                                                  have p2573_2 := h2573c.2.2.1
                                                  have p2573_3 := h2573c.2.2.2
                                                  linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2573_1, u3elo4]
                                                · have p2573_0 := h2573c.1
                                                  have p2573_1 := h2573c.2.1
                                                  have p2573_2 := h2573c.2.2.1
                                                  have p2573_3 := h2573c.2.2.2
                                                  linarith only [h2483, h2490, h2494, hc23, hlam, hphi, p2573_1, u3elo4]
                                                · have p2573_0 := h2573c.1
                                                  have p2573_1 := h2573c.2.1
                                                  have p2573_2 := h2573c.2.2.1
                                                  have p2573_3 := h2573c.2.2.2
                                                  linarith only [h2490, h2494, hc23, hlam, hphi, p2573_1, u3elo4]
                                                · have p2573_0 := h2573c.1
                                                  have p2573_1 := h2573c.2.1
                                                  have p2573_2 := h2573c.2.2.1
                                                  have p2573_3 := h2573c.2.2.2
                                                  linarith only [hlam, p2573_0]
                                                · have p2573_0 := h2573c.1
                                                  have p2573_1 := h2573c.2.1
                                                  have p2573_2 := h2573c.2.2.1
                                                  have p2573_3 := h2573c.2.2.2
                                                  linarith only [h2496, hlam, p2573_1]
                                                · have p2573_0 := h2573c.1
                                                  have p2573_1 := h2573c.2.1
                                                  have p2573_2 := h2573c.2.2.1
                                                  have p2573_3 := h2573c.2.2.2
                                                  linarith only [h2154, h2412, hc03, hc45, hlam, hphi, ht34, p2573_1]
                                                · have p2573_0 := h2573c.1
                                                  have p2573_1 := h2573c.2.1
                                                  have p2573_2 := h2573c.2.2.1
                                                  have p2573_3 := h2573c.2.2.2
                                                  linarith only [h2483, h2490, h2494, hc23, hc45, hlam, hphi, ht34, p2573_1]
                                                · have p2573_0 := h2573c.1
                                                  have p2573_1 := h2573c.2.1
                                                  have p2573_2 := h2573c.2.2.1
                                                  have p2573_3 := h2573c.2.2.2
                                                  linarith only [h2490, h2494, hc23, hc45, hlam, hphi, ht34, p2573_1]
                                                · have p2573_0 := h2573c.1
                                                  have p2573_1 := h2573c.2.1
                                                  have p2573_2 := h2573c.2.2.1
                                                  have p2573_3 := h2573c.2.2.2
                                                  linarith only [h2150, h2351, h2481, hc23, hc45, hlam, hphi, ht34, p2573_1]
                                                · have p2573_0 := h2573c.1
                                                  have p2573_1 := h2573c.2.1
                                                  have p2573_2 := h2573c.2.2.1
                                                  have p2573_3 := h2573c.2.2.2
                                                  linarith only [hlam, p2573_0]
                                              · linarith only [h2150, h2152, h2483, h2490, h2494, h2571, hc12, hc23, hlam, hphi, p2498_1, u3elo0]
                                              · linarith only [h2151, h2571, hc12, hlam, p2498_1]
                                              · linarith only [h2152, h2571, hc12, hlam, p2498_1]
                                      · linarith only [h2564, hlam, p2498_0]
                                  · have p2498_0 := h2498c.1
                                    have p2498_1 := h2498c.2.1
                                    have p2498_2 := h2498c.2.2.1
                                    have p2498_3 := h2498c.2.2.2
                                    linarith only [hlam, p2498_0]
                                  · have p2498_0 := h2498c.1
                                    have p2498_1 := h2498c.2.1
                                    have p2498_2 := h2498c.2.2.1
                                    have p2498_3 := h2498c.2.2.2
                                    rcases p2498_3 (m.d 0 1) (by simp) with h2604 | h2604
                                    · linarith only [h0, h2604, hlam]
                                    · linarith only [h2150, h2604, hlam]
                                  · have p2498_0 := h2498c.1
                                    have p2498_1 := h2498c.2.1
                                    have p2498_2 := h2498c.2.2.1
                                    have p2498_3 := h2498c.2.2.2
                                    rcases p2498_3 (m.d 0 1) (by simp) with h2607 | h2607
                                    · linarith only [h0, h2607, hlam]
                                    · linarith only [h2151, h2607, hlam]
                                  · have p2498_0 := h2498c.1
                                    have p2498_1 := h2498c.2.1
                                    have p2498_2 := h2498c.2.2.1
                                    have p2498_3 := h2498c.2.2.2
                                    rcases p2498_3 (m.d 0 1) (by simp) with h2610 | h2610
                                    · linarith only [h0, h2610, hlam]
                                    · linarith only [h2152, h2610, hlam]
                                  · have p2498_0 := h2498c.1
                                    have p2498_1 := h2498c.2.1
                                    have p2498_2 := h2498c.2.2.1
                                    have p2498_3 := h2498c.2.2.2
                                    linarith only [h2150, hlam, p2498_0]
                                  · have p2498_0 := h2498c.1
                                    have p2498_1 := h2498c.2.1
                                    have p2498_2 := h2498c.2.2.1
                                    have p2498_3 := h2498c.2.2.2
                                    linarith only [h2481, hlam, p2498_1]
                                  · have p2498_0 := h2498c.1
                                    have p2498_1 := h2498c.2.1
                                    have p2498_2 := h2498c.2.2.1
                                    have p2498_3 := h2498c.2.2.2
                                    linarith only [hlam, p2498_0]
                                  · have p2498_0 := h2498c.1
                                    have p2498_1 := h2498c.2.1
                                    have p2498_2 := h2498c.2.2.1
                                    have p2498_3 := h2498c.2.2.2
                                    linarith only [h2484, hlam, p2498_1]
                                  · have p2498_0 := h2498c.1
                                    have p2498_1 := h2498c.2.1
                                    have p2498_2 := h2498c.2.2.1
                                    have p2498_3 := h2498c.2.2.2
                                    linarith only [h2486, hlam, p2498_1]
                                  · have p2498_0 := h2498c.1
                                    have p2498_1 := h2498c.2.1
                                    have p2498_2 := h2498c.2.2.1
                                    have p2498_3 := h2498c.2.2.2
                                    linarith only [h2151, hlam, p2498_0]
                                  · have p2498_0 := h2498c.1
                                    have p2498_1 := h2498c.2.1
                                    have p2498_2 := h2498c.2.2.1
                                    have p2498_3 := h2498c.2.2.2
                                    linarith only [h2482, hlam, p2498_1]
                                  · have p2498_0 := h2498c.1
                                    have p2498_1 := h2498c.2.1
                                    have p2498_2 := h2498c.2.2.1
                                    have p2498_3 := h2498c.2.2.2
                                    linarith only [h0, h2152, h2488, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2498_1]
                                  · have p2498_0 := h2498c.1
                                    have p2498_1 := h2498c.2.1
                                    have p2498_2 := h2498c.2.2.1
                                    have p2498_3 := h2498c.2.2.2
                                    linarith only [hlam, p2498_0]
                                  · have p2498_0 := h2498c.1
                                    have p2498_1 := h2498c.2.1
                                    have p2498_2 := h2498c.2.2.1
                                    have p2498_3 := h2498c.2.2.2
                                    linarith only [h2488, hlam, p2498_1]
                                  · have p2498_0 := h2498c.1
                                    have p2498_1 := h2498c.2.1
                                    have p2498_2 := h2498c.2.2.1
                                    have p2498_3 := h2498c.2.2.2
                                    linarith only [h2152, hlam, p2498_0]
                                  · have p2498_0 := h2498c.1
                                    have p2498_1 := h2498c.2.1
                                    have p2498_2 := h2498c.2.2.1
                                    have p2498_3 := h2498c.2.2.2
                                    linarith only [h2483, hlam, p2498_1]
                                  · have p2498_0 := h2498c.1
                                    have p2498_1 := h2498c.2.1
                                    have p2498_2 := h2498c.2.2.1
                                    have p2498_3 := h2498c.2.2.2
                                    linarith only [h0, h2152, h2481, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2498_1]
                                  · have p2498_0 := h2498c.1
                                    have p2498_1 := h2498c.2.1
                                    have p2498_2 := h2498c.2.2.1
                                    have p2498_3 := h2498c.2.2.2
                                    linarith only [h0, h2152, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2498_1]
                                  · have p2498_0 := h2498c.1
                                    have p2498_1 := h2498c.2.1
                                    have p2498_2 := h2498c.2.2.1
                                    have p2498_3 := h2498c.2.2.2
                                    linarith only [hlam, p2498_0]
                  · linarith only [h0, h2153, h2483, hlam]
                · linarith only [h0, h2151, h2482, hlam]
              · linarith only [h0, h2481, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · linarith only [h0, h2152, h2153, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2632 | h2632
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2633 | h2633
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2634 | h2634
          · linarith only [h2150, h2152, h2634, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2636 | h2636
            · linarith only [h2150, h2152, h2633, h2634, h2636, hc13, hlam, hphi, u3elo4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2638 | h2638
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2639 | h2639
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2640 | h2640
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2641 | h2641
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2642 | h2642
                      · linarith only [h2150, h2152, h2634, h2640, h2642, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h2150, h2152, h2642, hc13, hlam, hphi, u3elo4]
                    · linarith only [h2633, h2638, h2641, hc23, hlam, hphi, u3elo0]
                  · linarith only [h0, h2150, h2632, h2638, h2640, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h2151, h2639, hlam]
              · linarith only [h0, h2638, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2649 | h2649
          · linarith only [h2151, h2152, h2633, h2649, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2651 | h2651
            · linarith only [h2151, h2152, h2651, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2653 | h2653
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2654 | h2654
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2655 | h2655
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2656 | h2656
                    · linarith only [h2150, h2152, h2633, h2655, h2656, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2658 | h2658
                      · linarith only [h2150, h2152, h2649, h2658, hlam]
                      · linarith only [h2151, h2152, h2656, h2658, hc13, hlam, hphi, u3elo4]
                  · linarith only [h0, h2150, h2632, h2653, h2655, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h2151, h2654, hlam]
              · linarith only [h0, h2653, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2664 | h2664
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2665 | h2665
          · linarith only [h0, h2150, h2632, h2665, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2667 | h2667
            · linarith only [h0, h2150, h2632, h2664, h2667, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2669 | h2669
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2670 | h2670
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2671 | h2671
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2672 | h2672
                    · linarith only [h0, h2150, h2632, h2671, h2672, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h2664, h2665, h2672, hc13, hlam, hphi, u3elo4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2675 | h2675
                    · linarith only [h0, h2150, h2671, h2675, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h2664, h2665, h2669, h2675, hc23, hlam, hphi, u3elo4]
                · linarith only [h0, h2151, h2670, hlam]
              · linarith only [h0, h2150, h2669, hc13, hlam, hphi, u3elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2680 | h2680
          · linarith only [h0, h2151, h2632, h2664, h2680, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2682 | h2682
            · linarith only [h0, h2151, h2632, h2682, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2684 | h2684
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2685 | h2685
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2686 | h2686
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2687 | h2687
                    · linarith only [h0, h2150, h2632, h2664, h2686, h2687, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2689 | h2689
                      · linarith only [h0, h2150, h2632, h2680, h2689, hlam]
                      · linarith only [h0, h2151, h2632, h2684, h2686, h2687, h2689, hc23, hlam, hphi, u3elo4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2692 | h2692
                    · linarith only [h2664, h2692, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2694 | h2694
                      · linarith only [h0, h2150, h2686, h2694, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h2151, h2152, h2684, h2692, h2694, hc23, hlam, hphi, u3elo4]
                · linarith only [h0, h2151, h2685, hlam]
              · linarith only [h0, h2684, hc01, hlam, hphi, ht12, ht23, u3elo2]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2699 | h2699
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2700 | h2700
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2701 | h2701
        · linarith only [h2150, h2151, h2701, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2703 | h2703
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2704 | h2704
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2705 | h2705
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2706 | h2706
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2707 | h2707
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2708 | h2708
                    · linarith only [h2150, h2151, h2701, h2706, h2708, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h2150, h2151, h2708, hc13, hlam, hphi, u3elo3]
                  · linarith only [h0, h2700, h2707, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2712 | h2712
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2713 | h2713
                    · linarith only [h0, h2150, h2701, h2706, h2713, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h2150, h2706, h2713, hc13, hlam, hphi, u3elo3]
                  · linarith only [h0, h2700, h2712, hlam]
              · linarith only [h0, h2150, h2705, hc13, hlam, hphi, u3elo2]
            · linarith only [h2150, h2151, h2703, h2704, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2719 | h2719
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2720 | h2720
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2721 | h2721
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2722 | h2722
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2723 | h2723
                    · linarith only [h2701, h2723, hc03, hlam, hphi, u3elo1]
                    · linarith only [h2150, h2151, h2720, h2723, hc23, hlam, hphi, u3elo3]
                  · linarith only [h0, h2700, h2722, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2727 | h2727
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2728 | h2728
                    · linarith only [h0, h2150, h2701, h2719, h2728, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h0, h2150, h2721, h2728, hc13, hlam, hphi, u3elo3]
                  · linarith only [h0, h2700, h2727, hlam]
              · linarith only [h0, h2720, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h2151, h2699, h2719, hlam]
      · linarith only [h0, h2699, h2700, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2735 | h2735
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2736 | h2736
        · linarith only [h2150, h2151, h2736, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2738 | h2738
          · linarith only [h2150, h2699, h2738, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2740 | h2740
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2741 | h2741
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2742 | h2742
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2743 | h2743
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2744 | h2744
                    · linarith only [h2150, h2151, h2736, h2742, h2744, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h2150, h2151, h2741, h2744, hc23, hlam, hphi, u3elo3]
                  · linarith only [h0, h2150, h2735, h2741, h2743, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2748 | h2748
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2749 | h2749
                    · linarith only [h2150, h2699, h2736, h2740, h2749, hc15, hc45, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h2150, h2699, h2741, h2742, h2748, h2749, hc23, hlam, hphi, u3elo3]
                  · linarith only [h0, h2735, h2748, hlam]
              · linarith only [h0, h2150, h2741, hc13, hlam, hphi, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2754 | h2754
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2755 | h2755
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2756 | h2756
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2757 | h2757
                    · linarith only [h2150, h2151, h2740, h2757, hc34, hc45, hlam, hphi]
                    · linarith only [h2150, h2151, h2757, hc13, hlam, hphi, u3elo3]
                  · linarith only [h2150, h2151, h2735, h2754, h2755, h2756, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2761 | h2761
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2762 | h2762
                    · linarith only [h2150, h2151, h2740, h2762, hc34, hc45, hlam, hphi]
                    · linarith only [h2150, h2699, h2755, h2761, h2762, hc13, hlam, hphi, u3elo3]
                  · linarith only [h0, h2735, h2761, hlam]
              · linarith only [h0, h2754, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2767 | h2767
        · linarith only [h2150, h2151, h2767, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2769 | h2769
          · linarith only [h0, h2150, h2735, h2769, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2771 | h2771
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2772 | h2772
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2773 | h2773
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2774 | h2774
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2775 | h2775
                    · linarith only [h0, h2150, h2735, h2767, h2774, h2775, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h2150, h2151, h2772, h2775, hc23, hlam, hphi, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2778 | h2778
                    · linarith only [h0, h2150, h2774, h2778, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h2150, h2151, h2778, hc13, hlam, hphi, u3elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2781 | h2781
                  · linarith only [h0, h2150, h2735, h2772, h2773, h2781, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2783 | h2783
                    · linarith only [h0, h2150, h2773, h2783, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h2150, h2773, h2783, hc13, hlam, hphi, u3elo3]
              · linarith only [h0, h2150, h2772, hc13, hlam, hphi, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2787 | h2787
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2788 | h2788
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2789 | h2789
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2790 | h2790
                    · linarith only [h0, h2150, h2735, h2789, h2790, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h2150, h2151, h2787, h2790, hc23, hlam, hphi, u3elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2793 | h2793
                    · linarith only [h0, h2150, h2789, h2793, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h2150, h2151, h2793, hc13, hlam, hphi, u3elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2796 | h2796
                  · linarith only [h0, h2150, h2735, h2787, h2788, h2796, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2798 | h2798
                    · linarith only [h0, h2150, h2788, h2798, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h2150, h2788, h2798, hc13, hlam, hphi, u3elo3]
              · linarith only [h0, h2150, h2787, hc13, hlam, hphi, u3elo2]

end R2N4
