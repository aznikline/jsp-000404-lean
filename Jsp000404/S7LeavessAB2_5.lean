import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem n7l_sAB2_H_I_H_L_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h2ehi := hb2.1
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  linarith only [hlam, hphi, ht23, ht34, ht45, u2ehi4, u5elo2]

theorem n7l_sAB2_H_I_M_IR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h2elo := hb2.1
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 4) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h5 | h5
        · linarith only [h5, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h7 | h7
          · rcases p0_3 (m.d 4 5) (by simp) with h8 | h8
            · linarith only [h8, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h8, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h11 | h11
            · linarith only [h11, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h11, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h15 | h15
    · rcases p0_3 (m.d 1 4) (by simp) with h16 | h16
      · rcases p0_3 (m.d 2 4) (by simp) with h17 | h17
        · linarith only [h17, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h19 | h19
          · rcases p0_3 (m.d 4 5) (by simp) with h20 | h20
            · linarith only [h20, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h20, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h23 | h23
            · linarith only [h23, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h23, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · rcases p0_3 (m.d 2 4) (by simp) with h26 | h26
        · linarith only [h26, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h28 | h28
          · rcases p0_3 (m.d 4 5) (by simp) with h29 | h29
            · linarith only [h16, h29, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h29, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h32 | h32
            · linarith only [h16, h32, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h32, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h15, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h36 | h36
    · rcases p0_3 (m.d 1 4) (by simp) with h37 | h37
      · rcases p0_3 (m.d 2 4) (by simp) with h38 | h38
        · linarith only [h38, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h40 | h40
          · linarith only [h40, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h42 | h42
            · linarith only [h42, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h42, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · rcases p0_3 (m.d 2 4) (by simp) with h45 | h45
        · linarith only [h37, h45, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h47 | h47
          · linarith only [h47, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h49 | h49
            · linarith only [h37, h49, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h49, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h36, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h54 | h54
    · linarith only [h54, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h56 | h56
      · rcases p0_3 (m.d 2 4) (by simp) with h57 | h57
        · linarith only [h57, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h59 | h59
          · rcases p0_3 (m.d 4 5) (by simp) with h60 | h60
            · linarith only [h60, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h60, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h63 | h63
            · linarith only [h63, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h63, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h56, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h68 | h68
    · rcases p0_3 (m.d 1 4) (by simp) with h69 | h69
      · rcases p0_3 (m.d 2 4) (by simp) with h70 | h70
        · linarith only [h70, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h72 | h72
          · rcases p0_3 (m.d 4 5) (by simp) with h73 | h73
            · linarith only [h73, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h68, h73, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h76 | h76
            · linarith only [h76, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h76, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h69, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h80 | h80
      · rcases p0_3 (m.d 2 4) (by simp) with h81 | h81
        · linarith only [h81, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h83 | h83
          · rcases p0_3 (m.d 4 5) (by simp) with h84 | h84
            · linarith only [h68, h84, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h84, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h87 | h87
            · linarith only [h68, h87, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h87, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h80, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h91 | h91
    · rcases p0_3 (m.d 1 4) (by simp) with h92 | h92
      · rcases p0_3 (m.d 2 4) (by simp) with h93 | h93
        · linarith only [h93, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h95 | h95
          · linarith only [h95, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h97 | h97
            · linarith only [h97, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h91, h97, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h92, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h101 | h101
      · rcases p0_3 (m.d 2 4) (by simp) with h102 | h102
        · linarith only [h102, h91, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h104 | h104
          · linarith only [h104, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h106 | h106
            · linarith only [h106, h91, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h106, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h101, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo3, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h116 | h116
    · linarith only [h116, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h118 | h118
      · rcases p0_3 (m.d 2 4) (by simp) with h119 | h119
        · linarith only [h119, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h121 | h121
          · rcases p0_3 (m.d 4 5) (by simp) with h122 | h122
            · linarith only [h122, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h118, h122, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h121, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h126 | h126
        · linarith only [h126, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h128 | h128
          · rcases p0_3 (m.d 4 5) (by simp) with h129 | h129
            · linarith only [h129, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h129, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h128, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h133 | h133
    · rcases p0_3 (m.d 1 4) (by simp) with h134 | h134
      · linarith only [h134, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h136 | h136
        · linarith only [h136, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h138 | h138
          · rcases p0_3 (m.d 4 5) (by simp) with h139 | h139
            · linarith only [h139, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h133, h139, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h138, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h143 | h143
      · linarith only [h143, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h145 | h145
        · linarith only [h133, h145, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p0_1, u2elo3]
        · rcases p0_3 (m.d 3 4) (by simp) with h147 | h147
          · rcases p0_3 (m.d 4 5) (by simp) with h148 | h148
            · linarith only [h133, h148, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h148, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h147, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h152 | h152
    · rcases p0_3 (m.d 1 4) (by simp) with h153 | h153
      · rcases p0_3 (m.d 2 4) (by simp) with h154 | h154
        · linarith only [h154, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h156 | h156
          · rcases p0_3 (m.d 4 5) (by simp) with h157 | h157
            · linarith only [h157, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h152, h157, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h156, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h161 | h161
        · linarith only [h161, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h163 | h163
          · rcases p0_3 (m.d 4 5) (by simp) with h164 | h164
            · linarith only [h153, h164, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h164, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h163, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h168 | h168
      · rcases p0_3 (m.d 2 4) (by simp) with h169 | h169
        · linarith only [h169, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h171 | h171
          · rcases p0_3 (m.d 4 5) (by simp) with h172 | h172
            · linarith only [h152, h172, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h168, h172, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h171, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h176 | h176
        · linarith only [h176, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h178 | h178
          · rcases p0_3 (m.d 4 5) (by simp) with h179 | h179
            · linarith only [h152, h179, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h179, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h178, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAB2_H_I_M_IR_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h2ehi := hb2.1
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h2 | h2
    · rcases p0_3 (m.d 1 4) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h5 | h5
        · rcases p0_3 (m.d 3 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 4 5) (by simp) with h7 | h7
            · linarith only [h7, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h7, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h10 | h10
            · linarith only [h10, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h10, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h5, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h16 | h16
    · rcases p0_3 (m.d 1 4) (by simp) with h17 | h17
      · rcases p0_3 (m.d 2 4) (by simp) with h18 | h18
        · rcases p0_3 (m.d 3 4) (by simp) with h19 | h19
          · linarith only [h19, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h21 | h21
            · linarith only [h21, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h21, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h17, h18, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
      · rcases p0_3 (m.d 2 4) (by simp) with h25 | h25
        · rcases p0_3 (m.d 3 4) (by simp) with h26 | h26
          · linarith only [h26, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h28 | h28
            · linarith only [h17, h28, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h28, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h25, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
    · linarith only [h16, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h34 | h34
    · linarith only [h34, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h36 | h36
      · rcases p0_3 (m.d 2 4) (by simp) with h37 | h37
        · rcases p0_3 (m.d 3 4) (by simp) with h38 | h38
          · rcases p0_3 (m.d 4 5) (by simp) with h39 | h39
            · linarith only [h39, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h39, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h42 | h42
            · linarith only [h42, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h42, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h37, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
      · linarith only [h36, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h49 | h49
    · rcases p0_3 (m.d 1 4) (by simp) with h50 | h50
      · rcases p0_3 (m.d 2 4) (by simp) with h51 | h51
        · rcases p0_3 (m.d 3 4) (by simp) with h52 | h52
          · linarith only [h52, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h54 | h54
            · linarith only [h54, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h49, h54, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h51, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
      · linarith only [h50, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h59 | h59
      · rcases p0_3 (m.d 2 4) (by simp) with h60 | h60
        · rcases p0_3 (m.d 3 4) (by simp) with h61 | h61
          · linarith only [h61, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h63 | h63
            · linarith only [h49, h63, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h63, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h60, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p0_1, u2ehi3]
      · linarith only [h59, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h69 | h69
    · linarith only [h69, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h71 | h71
      · rcases p0_3 (m.d 2 4) (by simp) with h72 | h72
        · rcases p0_3 (m.d 3 4) (by simp) with h73 | h73
          · rcases p0_3 (m.d 4 5) (by simp) with h74 | h74
            · linarith only [h74, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h74, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h77 | h77
            · linarith only [h77, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h77, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h72, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h81 | h81
        · rcases p0_3 (m.d 3 4) (by simp) with h82 | h82
          · rcases p0_3 (m.d 4 5) (by simp) with h83 | h83
            · linarith only [h83, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h83, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h86 | h86
            · linarith only [h86, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h86, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h81, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h90 | h90
    · rcases p0_3 (m.d 1 4) (by simp) with h91 | h91
      · linarith only [h91, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h93 | h93
        · rcases p0_3 (m.d 3 4) (by simp) with h94 | h94
          · rcases p0_3 (m.d 4 5) (by simp) with h95 | h95
            · linarith only [h95, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h90, h95, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h98 | h98
            · linarith only [h98, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h98, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h93, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h102 | h102
      · linarith only [h102, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h104 | h104
        · rcases p0_3 (m.d 3 4) (by simp) with h105 | h105
          · rcases p0_3 (m.d 4 5) (by simp) with h106 | h106
            · linarith only [h106, h90, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h106, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h109 | h109
            · linarith only [h109, h90, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h109, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h104, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h114 | h114
    · rcases p0_3 (m.d 1 4) (by simp) with h115 | h115
      · rcases p0_3 (m.d 2 4) (by simp) with h116 | h116
        · rcases p0_3 (m.d 3 4) (by simp) with h117 | h117
          · linarith only [h117, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h119 | h119
            · linarith only [h119, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h114, h119, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h116, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h123 | h123
        · rcases p0_3 (m.d 3 4) (by simp) with h124 | h124
          · linarith only [h124, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h126 | h126
            · linarith only [h115, h126, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h114, h126, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h123, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h130 | h130
      · rcases p0_3 (m.d 2 4) (by simp) with h131 | h131
        · rcases p0_3 (m.d 3 4) (by simp) with h132 | h132
          · linarith only [h132, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h134 | h134
            · linarith only [h114, h134, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h130, h134, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h131, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h138 | h138
        · rcases p0_3 (m.d 3 4) (by simp) with h139 | h139
          · linarith only [h139, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h141 | h141
            · linarith only [h114, h141, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h141, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h138, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h146 | h146
    · linarith only [h146, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h148 | h148
      · rcases p0_3 (m.d 2 4) (by simp) with h149 | h149
        · rcases p0_3 (m.d 3 4) (by simp) with h150 | h150
          · rcases p0_3 (m.d 4 5) (by simp) with h151 | h151
            · linarith only [h151, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h148, h151, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h150, hlam, p0_0]
        · linarith only [h149, hc34, hlam, hphi, ht23, p0_1, u2ehi3]
      · rcases p0_3 (m.d 2 4) (by simp) with h156 | h156
        · rcases p0_3 (m.d 3 4) (by simp) with h157 | h157
          · rcases p0_3 (m.d 4 5) (by simp) with h158 | h158
            · linarith only [h158, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h156, h158, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h157, hlam, p0_0]
        · linarith only [h156, hc34, hlam, hphi, ht23, p0_1, u2ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h163 | h163
    · rcases p0_3 (m.d 1 4) (by simp) with h164 | h164
      · linarith only [h164, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h166 | h166
        · rcases p0_3 (m.d 3 4) (by simp) with h167 | h167
          · rcases p0_3 (m.d 4 5) (by simp) with h168 | h168
            · linarith only [h168, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h163, h168, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h167, hlam, p0_0]
        · linarith only [h166, hc34, hlam, hphi, ht23, p0_1, u2ehi3]
    · rcases p0_3 (m.d 1 4) (by simp) with h173 | h173
      · linarith only [h173, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h175 | h175
        · rcases p0_3 (m.d 3 4) (by simp) with h176 | h176
          · rcases p0_3 (m.d 4 5) (by simp) with h177 | h177
            · linarith only [h163, h177, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h175, h177, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h176, hlam, p0_0]
        · linarith only [h175, hc34, hlam, hphi, ht23, p0_1, u2ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht23, p0_1, u2ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht23, ht34, p0_1, u2ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAB2_H_I_M_LI_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAB2_H_L_H_I_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h2elo := hb2.1
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 3 4 5 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h2, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
        · linarith only [h3, hc34, hlam, hphi, u4elo4]
      · linarith only [h2, hc23, hlam, hphi, ht34, u4elo3]
    · linarith only [h1, hc02, hlam, hphi, ht23, ht34, u4elo2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h8 | h8
    · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
      · rcases m.htr 3 4 5 (by decide) (by decide) with h10 | h10
        · linarith only [h0, h10, h8, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
        · linarith only [h10, hc34, hlam, hphi, u4elo4]
      · linarith only [h0, h9, hc02, hlam, hphi, ht23, ht34, u4elo3]
    · linarith only [h8, hc02, hlam, hphi, ht23, ht34, u4elo2]

theorem n7l_sAB2_H_L_H_I_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5emin := hb5.2.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 3 4 5 (by decide) (by decide) with h5 | h5
            · rcases h5emin with h6 | h6 | h6 | h6 | h6
              · linarith only [h1, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
              · linarith only [h2, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1]
              · linarith only [h0, h4, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
              · linarith only [h0, h3, h4, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
              · linarith only [h0, h4, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
            · linarith only [h0, h4, h5, hc34, hlam, hphi, u4elo0]
          · linarith only [h4, hc24, hlam, hphi, u4elo4]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
          · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
            · linarith only [h15, h3, hc23, hlam, hphi, ht34, u4elo3]
            · linarith only [h0, h14, h15, hc34, hlam, hphi, u4elo0]
          · linarith only [h14, hc24, hlam, hphi, u4elo4]
      · linarith only [h1, h2, hc14, hlam, hphi, u4elo0]
    · linarith only [h1, hc04, hlam, hphi, u4elo4]
  · linarith only [h0, hc02, hlam, hphi, ht23, ht34, u4elo2]

theorem n7l_sAB2_H_L_H_I_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h2ehi := hb2.1
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  linarith only [hlam, hphi, ht23, ht34, u2ehi3, u4elo2]

theorem n7l_sAB2_H_L_H_L_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h2elo := hb2.1
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 3 4 5 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h2, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
        · linarith only [h3, hc34, hlam, hphi, u4elo4]
      · linarith only [h2, hc23, hlam, hphi, ht34, u4elo3]
    · linarith only [h1, hc12, hlam, hphi, ht23, ht34, u4elo2]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
    · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
      · rcases m.htr 3 4 5 (by decide) (by decide) with h10 | h10
        · linarith only [h0, h10, h8, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
        · linarith only [h10, hc34, hlam, hphi, u4elo4]
      · linarith only [h0, h9, hc12, hlam, hphi, ht23, ht34, u4elo3]
    · linarith only [h8, hc12, hlam, hphi, ht23, ht34, u4elo2]

theorem n7l_sAB2_H_L_H_L_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h4elo := hb4.1
  have h5elo := hb5.1
  have h2bigk := hb2.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h11, h5, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
                        · linarith only [h11, hc34, hlam, hphi, u4elo4]
                      · linarith only [h10, hc24, hlam, hphi, ht45, u5elo4]
                    · linarith only [h9, hc23, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h8, hc23, hlam, hphi, ht34, u4elo3]
                · linarith only [h7, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h5, h6, hc23, hlam, hphi, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h19 | h19
              · rcases m.htr 1 2 5 (by decide) (by decide) with h20 | h20
                · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h22 | h22
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h23 | h23
                      · linarith only [h0, h19, h23, h3, h5, hc01, hc45, hlam, hphi, ht0b, ht5b]
                      · linarith only [h23, hc24, hlam, hphi, u4elo4]
                    · linarith only [h22, h5, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · linarith only [h19, h21, h5, hc24, hlam, hphi, u4elo3]
                · linarith only [h19, h20, hc24, hlam, hphi, ht45, u5elo2]
              · linarith only [h19, hc12, hlam, hphi, ht23, ht34, u4elo2]
          · linarith only [h4, hc02, hlam, hphi, ht23, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h31 | h31
          · rcases m.htr 1 2 3 (by decide) (by decide) with h32 | h32
            · linarith only [h0, h3, h31, h32, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h34 | h34
              · rcases m.htr 1 2 5 (by decide) (by decide) with h35 | h35
                · rcases m.htr 2 3 4 (by decide) (by decide) with h36 | h36
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h37 | h37
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h38 | h38
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h39 | h39
                        · rcases h2bigk with h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c
                          · have p40_0 := h40c.1
                            have p40_1 := h40c.2.1
                            have p40_2 := h40c.2.2.1
                            have p40_3 := h40c.2.2.2
                            linarith only [hlam, p40_0]
                          · have p40_0 := h40c.1
                            have p40_1 := h40c.2.1
                            have p40_2 := h40c.2.2.1
                            have p40_3 := h40c.2.2.2
                            linarith only [h34, h36, h39, hc02, hc45, hlam, hphi, ht0b, ht5b, p40_1]
                          · have p40_0 := h40c.1
                            have p40_1 := h40c.2.1
                            have p40_2 := h40c.2.2.1
                            have p40_3 := h40c.2.2.2
                            linarith only [h3, hlam, p40_0]
                          · have p40_0 := h40c.1
                            have p40_1 := h40c.2.1
                            have p40_2 := h40c.2.2.1
                            have p40_3 := h40c.2.2.2
                            linarith only [h3, h36, h39, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p40_1]
                          · have p40_0 := h40c.1
                            have p40_1 := h40c.2.1
                            have p40_2 := h40c.2.2.1
                            have p40_3 := h40c.2.2.2
                            rcases p40_3 (m.d 0 2) (by simp) with h45 | h45
                            · rcases p40_3 (m.d 1 2) (by simp) with h46 | h46
                              · linarith only [h0, h46, hlam]
                              · linarith only [h35, h46, hlam]
                            · linarith only [h45, hlam, p40_0]
                          · have p40_0 := h40c.1
                            have p40_1 := h40c.2.1
                            have p40_2 := h40c.2.2.1
                            have p40_3 := h40c.2.2.2
                            linarith only [h0, hlam, p40_0]
                          · have p40_0 := h40c.1
                            have p40_1 := h40c.2.1
                            have p40_2 := h40c.2.2.1
                            have p40_3 := h40c.2.2.2
                            linarith only [hlam, p40_0]
                          · have p40_0 := h40c.1
                            have p40_1 := h40c.2.1
                            have p40_2 := h40c.2.2.1
                            have p40_3 := h40c.2.2.2
                            linarith only [h32, hlam, p40_0]
                          · have p40_0 := h40c.1
                            have p40_1 := h40c.2.1
                            have p40_2 := h40c.2.2.1
                            have p40_3 := h40c.2.2.2
                            linarith only [h0, h36, h39, hc01, hc45, hlam, hphi, ht0b, ht5b, p40_1]
                          · have p40_0 := h40c.1
                            have p40_1 := h40c.2.1
                            have p40_2 := h40c.2.2.1
                            have p40_3 := h40c.2.2.2
                            rcases p40_3 (m.d 0 2) (by simp) with h54 | h54
                            · rcases p40_3 (m.d 1 2) (by simp) with h55 | h55
                              · rcases p40_3 (m.d 2 3) (by simp) with h56 | h56
                                · rcases p40_3 (m.d 2 4) (by simp) with h57 | h57
                                  · linarith only [h34, h57, hlam]
                                  · linarith only [h38, h57, hlam]
                                · linarith only [h37, h56, hlam]
                              · linarith only [h55, hlam, p40_0]
                            · linarith only [h0, h54, hlam, p40_1]
                          · have p40_0 := h40c.1
                            have p40_1 := h40c.2.1
                            have p40_2 := h40c.2.2.1
                            have p40_3 := h40c.2.2.2
                            linarith only [h31, h36, h39, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p40_1]
                          · have p40_0 := h40c.1
                            have p40_1 := h40c.2.1
                            have p40_2 := h40c.2.2.1
                            have p40_3 := h40c.2.2.2
                            linarith only [h34, h36, h39, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p40_1]
                          · have p40_0 := h40c.1
                            have p40_1 := h40c.2.1
                            have p40_2 := h40c.2.2.1
                            have p40_3 := h40c.2.2.2
                            linarith only [hlam, p40_0]
                          · have p40_0 := h40c.1
                            have p40_1 := h40c.2.1
                            have p40_2 := h40c.2.2.1
                            have p40_3 := h40c.2.2.2
                            rcases p40_3 (m.d 0 2) (by simp) with h66 | h66
                            · linarith only [h3, h66, hlam]
                            · linarith only [h31, h66, hlam]
                          · have p40_0 := h40c.1
                            have p40_1 := h40c.2.1
                            have p40_2 := h40c.2.2.1
                            have p40_3 := h40c.2.2.2
                            rcases p40_3 (m.d 0 2) (by simp) with h69 | h69
                            · linarith only [h3, h69, hlam]
                            · linarith only [h0, h34, h36, h39, h69, hc45, hlam, hphi, u5elo2]
                          · have p40_0 := h40c.1
                            have p40_1 := h40c.2.1
                            have p40_2 := h40c.2.2.1
                            have p40_3 := h40c.2.2.2
                            linarith only [h31, hlam, p40_0]
                          · have p40_0 := h40c.1
                            have p40_1 := h40c.2.1
                            have p40_2 := h40c.2.2.1
                            have p40_3 := h40c.2.2.2
                            linarith only [h34, hlam, p40_0]
                          · have p40_0 := h40c.1
                            have p40_1 := h40c.2.1
                            have p40_2 := h40c.2.2.1
                            have p40_3 := h40c.2.2.2
                            linarith only [h36, hlam, p40_0]
                          · have p40_0 := h40c.1
                            have p40_1 := h40c.2.1
                            have p40_2 := h40c.2.2.1
                            have p40_3 := h40c.2.2.2
                            linarith only [hlam, p40_0]
                          · have p40_0 := h40c.1
                            have p40_1 := h40c.2.1
                            have p40_2 := h40c.2.2.1
                            have p40_3 := h40c.2.2.2
                            linarith only [h1, h34, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p40_1, u4elo0]
                          · have p40_0 := h40c.1
                            have p40_1 := h40c.2.1
                            have p40_2 := h40c.2.2.1
                            have p40_3 := h40c.2.2.2
                            linarith only [hc02, hlam, hphi, ht23, ht34, ht45, p40_1, u5elo2]
                          · have p40_0 := h40c.1
                            have p40_1 := h40c.2.1
                            have p40_2 := h40c.2.2.1
                            have p40_3 := h40c.2.2.2
                            linarith only [h35, hlam, p40_0]
                          · have p40_0 := h40c.1
                            have p40_1 := h40c.2.1
                            have p40_2 := h40c.2.2.1
                            have p40_3 := h40c.2.2.2
                            linarith only [h37, hlam, p40_1]
                          · have p40_0 := h40c.1
                            have p40_1 := h40c.2.1
                            have p40_2 := h40c.2.2.1
                            have p40_3 := h40c.2.2.2
                            linarith only [h38, hlam, p40_1]
                          · have p40_0 := h40c.1
                            have p40_1 := h40c.2.1
                            have p40_2 := h40c.2.2.1
                            have p40_3 := h40c.2.2.2
                            linarith only [hlam, p40_0]
                        · linarith only [h39, hc34, hlam, hphi, u4elo4]
                      · linarith only [h38, hc24, hlam, hphi, ht45, u5elo4]
                    · linarith only [h3, h37, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · linarith only [h0, h3, h34, h36, hc24, hlam, hphi, u4elo3]
                · linarith only [h34, h35, hc24, hlam, hphi, ht45, u5elo2]
              · linarith only [h34, hc12, hlam, hphi, ht23, ht34, u4elo2]
          · linarith only [h0, h31, hc12, hlam, hphi, ht23, ht34, u4elo2]
      · linarith only [h2, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h91 | h91
    · rcases m.htr 0 1 5 (by decide) (by decide) with h92 | h92
      · rcases m.htr 0 2 3 (by decide) (by decide) with h93 | h93
        · rcases m.htr 0 2 4 (by decide) (by decide) with h94 | h94
          · rcases m.htr 1 2 3 (by decide) (by decide) with h95 | h95
            · rcases m.htr 1 2 4 (by decide) (by decide) with h96 | h96
              · rcases m.htr 1 2 5 (by decide) (by decide) with h97 | h97
                · rcases m.htr 2 3 4 (by decide) (by decide) with h98 | h98
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h99 | h99
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h100 | h100
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h101 | h101
                        · rcases h2bigk with h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c | h102c
                          · have p102_0 := h102c.1
                            have p102_1 := h102c.2.1
                            have p102_2 := h102c.2.2.1
                            have p102_3 := h102c.2.2.2
                            linarith only [hlam, p102_0]
                          · have p102_0 := h102c.1
                            have p102_1 := h102c.2.1
                            have p102_2 := h102c.2.2.1
                            have p102_3 := h102c.2.2.2
                            linarith only [h0, hlam, p102_1]
                          · have p102_0 := h102c.1
                            have p102_1 := h102c.2.1
                            have p102_2 := h102c.2.2.1
                            have p102_3 := h102c.2.2.2
                            linarith only [h101, h98, hc02, hc45, hlam, hphi, ht0b, ht5b, p102_1]
                          · have p102_0 := h102c.1
                            have p102_1 := h102c.2.1
                            have p102_2 := h102c.2.2.1
                            have p102_3 := h102c.2.2.2
                            rcases p102_3 (m.d 0 2) (by simp) with h106 | h106
                            · rcases p102_3 (m.d 1 2) (by simp) with h107 | h107
                              · rcases p102_3 (m.d 2 3) (by simp) with h108 | h108
                                · linarith only [h108, h93, hlam]
                                · linarith only [h108, h98, hlam]
                              · linarith only [h107, h96, hlam]
                            · linarith only [h106, hlam, p102_0]
                          · have p102_0 := h102c.1
                            have p102_1 := h102c.2.1
                            have p102_2 := h102c.2.2.1
                            have p102_3 := h102c.2.2.2
                            rcases p102_3 (m.d 0 2) (by simp) with h113 | h113
                            · rcases p102_3 (m.d 1 2) (by simp) with h114 | h114
                              · rcases p102_3 (m.d 2 3) (by simp) with h115 | h115
                                · linarith only [h115, h93, hlam]
                                · linarith only [h115, h99, hlam]
                              · linarith only [h114, h97, hlam]
                            · linarith only [h113, hlam, p102_0]
                          · have p102_0 := h102c.1
                            have p102_1 := h102c.2.1
                            have p102_2 := h102c.2.2.1
                            have p102_3 := h102c.2.2.2
                            linarith only [h0, h101, h91, h96, h98, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p102_1]
                          · have p102_0 := h102c.1
                            have p102_1 := h102c.2.1
                            have p102_2 := h102c.2.2.1
                            have p102_3 := h102c.2.2.2
                            linarith only [hlam, p102_0]
                          · have p102_0 := h102c.1
                            have p102_1 := h102c.2.1
                            have p102_2 := h102c.2.2.1
                            have p102_3 := h102c.2.2.2
                            linarith only [h101, h98, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p102_1]
                          · have p102_0 := h102c.1
                            have p102_1 := h102c.2.1
                            have p102_2 := h102c.2.2.1
                            have p102_3 := h102c.2.2.2
                            rcases p102_3 (m.d 0 2) (by simp) with h123 | h123
                            · linarith only [h0, h123, hlam]
                            · linarith only [h123, h94, hlam]
                          · have p102_0 := h102c.1
                            have p102_1 := h102c.2.1
                            have p102_2 := h102c.2.2.1
                            have p102_3 := h102c.2.2.2
                            rcases p102_3 (m.d 0 2) (by simp) with h126 | h126
                            · linarith only [h0, h126, hlam]
                            · linarith only [h101, h126, h92, h93, h97, h98, hc45, hlam, hphi, u5elo0]
                          · have p102_0 := h102c.1
                            have p102_1 := h102c.2.1
                            have p102_2 := h102c.2.2.1
                            have p102_3 := h102c.2.2.2
                            linarith only [h93, hlam, p102_0]
                          · have p102_0 := h102c.1
                            have p102_1 := h102c.2.1
                            have p102_2 := h102c.2.2.1
                            have p102_3 := h102c.2.2.2
                            linarith only [h95, hlam, p102_0]
                          · have p102_0 := h102c.1
                            have p102_1 := h102c.2.1
                            have p102_2 := h102c.2.2.1
                            have p102_3 := h102c.2.2.2
                            linarith only [hlam, p102_0]
                          · have p102_0 := h102c.1
                            have p102_1 := h102c.2.1
                            have p102_2 := h102c.2.2.1
                            have p102_3 := h102c.2.2.2
                            linarith only [h101, h93, h98, hc02, hc45, hlam, hphi, ht0b, ht5b, p102_1]
                          · have p102_0 := h102c.1
                            have p102_1 := h102c.2.1
                            have p102_2 := h102c.2.2.1
                            have p102_3 := h102c.2.2.2
                            rcases p102_3 (m.d 0 2) (by simp) with h133 | h133
                            · rcases p102_3 (m.d 1 2) (by simp) with h134 | h134
                              · rcases p102_3 (m.d 2 3) (by simp) with h135 | h135
                                · rcases p102_3 (m.d 2 4) (by simp) with h136 | h136
                                  · linarith only [h136, h98, hlam]
                                  · linarith only [h100, h136, hlam]
                                · linarith only [h135, h99, hlam]
                              · linarith only [h134, h97, hlam]
                            · linarith only [h133, h93, hlam, p102_1]
                          · have p102_0 := h102c.1
                            have p102_1 := h102c.2.1
                            have p102_2 := h102c.2.2.1
                            have p102_3 := h102c.2.2.2
                            linarith only [h94, hlam, p102_0]
                          · have p102_0 := h102c.1
                            have p102_1 := h102c.2.1
                            have p102_2 := h102c.2.2.1
                            have p102_3 := h102c.2.2.2
                            linarith only [h96, hlam, p102_0]
                          · have p102_0 := h102c.1
                            have p102_1 := h102c.2.1
                            have p102_2 := h102c.2.2.1
                            have p102_3 := h102c.2.2.2
                            linarith only [h98, hlam, p102_0]
                          · have p102_0 := h102c.1
                            have p102_1 := h102c.2.1
                            have p102_2 := h102c.2.2.1
                            have p102_3 := h102c.2.2.2
                            linarith only [hlam, p102_0]
                          · have p102_0 := h102c.1
                            have p102_1 := h102c.2.1
                            have p102_2 := h102c.2.2.1
                            have p102_3 := h102c.2.2.2
                            linarith only [h96, h99, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p102_1, u4elo1]
                          · have p102_0 := h102c.1
                            have p102_1 := h102c.2.1
                            have p102_2 := h102c.2.2.1
                            have p102_3 := h102c.2.2.2
                            linarith only [hc02, hlam, hphi, ht23, ht34, ht45, p102_1, u5elo2]
                          · have p102_0 := h102c.1
                            have p102_1 := h102c.2.1
                            have p102_2 := h102c.2.2.1
                            have p102_3 := h102c.2.2.2
                            linarith only [h97, hlam, p102_0]
                          · have p102_0 := h102c.1
                            have p102_1 := h102c.2.1
                            have p102_2 := h102c.2.2.1
                            have p102_3 := h102c.2.2.2
                            linarith only [h99, hlam, p102_1]
                          · have p102_0 := h102c.1
                            have p102_1 := h102c.2.1
                            have p102_2 := h102c.2.2.1
                            have p102_3 := h102c.2.2.2
                            linarith only [h100, hlam, p102_1]
                          · have p102_0 := h102c.1
                            have p102_1 := h102c.2.1
                            have p102_2 := h102c.2.2.1
                            have p102_3 := h102c.2.2.2
                            linarith only [hlam, p102_0]
                        · linarith only [h100, h101, h91, h96, hc34, hlam, hphi, u4elo0]
                      · linarith only [h100, hc24, hlam, hphi, u4elo4]
                    · linarith only [h98, h99, hc34, hlam, hphi, ht45, u5elo3]
                  · linarith only [h98, hc23, hlam, hphi, ht34, u4elo3]
                · linarith only [h97, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h96, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · linarith only [h0, h91, h93, h95, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h94, hc02, hlam, hphi, ht23, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h160 | h160
          · rcases m.htr 1 2 3 (by decide) (by decide) with h161 | h161
            · rcases m.htr 1 2 4 (by decide) (by decide) with h162 | h162
              · rcases m.htr 1 2 5 (by decide) (by decide) with h163 | h163
                · rcases m.htr 2 3 4 (by decide) (by decide) with h164 | h164
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h165 | h165
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h166 | h166
                      · linarith only [h0, h161, h162, h166, h91, h93, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h166, hc24, hlam, hphi, u4elo4]
                    · linarith only [h0, h165, h93, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · linarith only [h0, h162, h164, h91, h93, hc24, hlam, hphi, u4elo3]
                · linarith only [h0, h161, h162, h163, h91, h93, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · linarith only [h0, h161, h162, h91, h93, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h173 | h173
              · rcases m.htr 1 2 5 (by decide) (by decide) with h174 | h174
                · rcases m.htr 2 3 4 (by decide) (by decide) with h175 | h175
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h176 | h176
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h177 | h177
                      · linarith only [h0, h161, h173, h177, h91, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h175, h177, hc34, hlam, hphi, u4elo4]
                    · linarith only [h0, h161, h173, h175, h176, h91, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h0, h161, h173, h175, h91, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h0, h173, h174, h91, hc24, hlam, hphi, ht45, u5elo2]
              · linarith only [h0, h173, h91, hc14, hlam, hphi, u4elo2]
          · linarith only [h160, hc02, hlam, hphi, ht23, ht34, u4elo2]
      · linarith only [h91, h92, hc14, hlam, hphi, ht45, u5elo1]
    · linarith only [h91, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]

theorem n7l_sAB2_H_L_H_L_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h2ehi := hb2.1
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  linarith only [hlam, hphi, ht23, ht34, u2ehi3, u4elo2]

theorem n7l_sAB2_H_L_H_R_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.1
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4, u5ehi4]

theorem n7l_sAB2_H_L_H_R_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.1
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4, u5ehi4]

theorem n7l_sAB2_H_L_H_R_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.1
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4, u5ehi4]

theorem n7l_sAB2_H_L_M_IR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi4]
  · linarith only [h0, hc34, hlam, hphi, u4elo4]

theorem n7l_sAB2_H_L_M_IR_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi4]
  · linarith only [h0, hc34, hlam, hphi, u4elo4]

theorem n7l_sAB2_H_L_M_IR_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h2ehi := hb2.1
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  linarith only [hlam, hphi, ht23, ht34, u2ehi3, u4elo2]

theorem n7l_sAB2_H_L_M_LI_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h2elo := hb2.1
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 3 4 5 (by decide) (by decide) with h3 | h3
        · linarith only [h0, h2, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
        · linarith only [h3, hc34, hlam, hphi, u4elo4]
      · linarith only [h2, hc23, hlam, hphi, ht34, u4elo3]
    · linarith only [h1, hc12, hlam, hphi, ht23, ht34, u4elo2]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
    · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
      · rcases m.htr 3 4 5 (by decide) (by decide) with h10 | h10
        · linarith only [h0, h10, h8, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
        · linarith only [h10, hc34, hlam, hphi, u4elo4]
      · linarith only [h0, h9, hc12, hlam, hphi, ht23, ht34, u4elo3]
    · linarith only [h8, hc12, hlam, hphi, ht23, ht34, u4elo2]

theorem n7l_sAB2_H_L_M_LI_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAB2_H_L_M_LI_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h2ehi := hb2.1
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  linarith only [hlam, hphi, ht23, ht34, u2ehi3, u4elo2]

theorem n7l_sAB2_H_L_M_LR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.2.2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi9]
  · linarith only [h0, hc34, hlam, hphi, u4elo4]

theorem n7l_sAB2_H_L_M_LR_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.2.2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi9]
  · linarith only [h0, hc34, hlam, hphi, u4elo4]

theorem n7l_sAB2_H_L_M_LR_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h2ehi := hb2.1
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  linarith only [hlam, hphi, ht23, ht34, u2ehi3, u4elo2]

theorem n7l_sAB2_H_R_H_I_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h2elo := hb2.1
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  rcases m.htr 2 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi4]
  · linarith only [h0, hc45, hlam, hphi, u4ehi2]

theorem n7l_sAB2_H_R_H_I_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5emax := hb5.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 4 5 (by decide) (by decide) with h4 | h4
          · linarith only [h1, h4, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
          · linarith only [h0, h4, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
        · linarith only [h0, h3, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
      · linarith only [h1, h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
      · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
        · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
          · linarith only [h1, h11, h9, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
          · linarith only [h10, h11, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
        · linarith only [h0, h10, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h15 | h15
        · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
          · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
            · rcases h5emax with h18 | h18 | h18 | h18 | h18
              · linarith only [h0, h18, hlam, ht45, u4ehi4]
              · linarith only [h15, h18, hlam, ht45, u4ehi4]
              · linarith only [h18, h9, hc12, hlam, ht23, ht34, ht45]
              · linarith only [h17, h18, hlam, ht45, u4ehi4]
              · linarith only [h18, hlam, ht45, u4ehi4]
            · linarith only [h15, h17, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
          · linarith only [h1, h15, h16, hlam]
        · linarith only [h15, hc45, hlam, hphi, u4ehi1]
  · linarith only [h0, hc45, hlam, hphi, u4ehi0]

theorem n7l_sAB2_H_R_H_I_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
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
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h2ehi := hb2.1
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 2 4 5 (by decide) (by decide) with h7 | h7
              · linarith only [h1, h7, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
              · linarith only [h7, hc45, hlam, hphi, u4ehi2]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
              · linarith only [h1, h10, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
              · linarith only [h10, hc45, hlam, hphi, u4ehi2]
        · linarith only [h3, hc45, hlam, hphi, u4ehi1]
      · linarith only [h0, h2, hc25, hlam, hphi, u2ehi2]
    · linarith only [h0, h1, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h16 | h16
    · linarith only [h0, h16, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h18 | h18
      · linarith only [h0, h18, hc23, hlam, hphi, u2ehi4]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h20 | h20
        · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
          · rcases m.htr 2 3 5 (by decide) (by decide) with h22 | h22
            · rcases m.htr 2 4 5 (by decide) (by decide) with h23 | h23
              · rcases m.htr 3 4 5 (by decide) (by decide) with h24 | h24
                · linarith only [h21, h24, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · linarith only [h20, h24, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
              · linarith only [h16, h20, h23, hlam]
            · linarith only [h16, h20, h21, h22, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
          · linarith only [h0, h21, hc34, hlam, hphi, ht23, u2ehi1]
        · linarith only [h20, hc45, hlam, hphi, u4ehi1]

theorem n7l_sAB2_H_R_H_L_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB2_H_R_H_L_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB2_H_R_H_L_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB2_H_R_H_R_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5ehi := hb5.1
  have h2elo := hb2.1
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  rcases m.htr 2 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
  · linarith only [h0, hc45, hlam, hphi, u4ehi2]

theorem n7l_sAB2_H_R_H_R_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5ehi := hb5.1
  have h2ehi := hb2.1
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h4 | h4
        · linarith only [h2, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h6 | h6
          · linarith only [h1, h6, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
          · linarith only [h6, hc45, hlam, hphi, u4ehi2]
    · linarith only [h0, h1, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
    · linarith only [h0, h10, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
      · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
        · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
          · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
            · linarith only [h12, h15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
            · linarith only [h15, hc45, hlam, hphi, u4ehi3]
          · linarith only [h10, h14, hc45, hlam, hphi, ht23, ht34, u2ehi1]
        · linarith only [h0, h13, hc35, hlam, hphi, ht23, u2ehi1]
      · linarith only [h0, h12, hc34, hlam, hphi, ht23, u2ehi1]

theorem n7l_sAB2_H_R_M_IR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h2elo := hb2.1
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  rcases m.htr 2 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi4]
  · linarith only [h0, hc45, hlam, hphi, u4ehi2]

theorem n7l_sAB2_H_R_M_IR_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5emax := hb5.2.2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 3 4 5 (by decide) (by decide) with h4 | h4
          · linarith only [h1, h4, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
          · linarith only [h0, h4, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
        · linarith only [h1, h2, h3, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
      · linarith only [h2, hc45, hlam, hphi, u4ehi1]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
      · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
        · rcases m.htr 3 4 5 (by decide) (by decide) with h11 | h11
          · rcases h5emax with h12 | h12 | h12 | h12 | h12
            · linarith only [h0, h12, hlam, ht45, u4ehi4]
            · linarith only [h12, h9, hlam, ht45, u4ehi4]
            · linarith only [h10, h12, hlam, ht45, u4ehi4]
            · linarith only [h11, h12, hlam, ht45, u4ehi4]
            · linarith only [h12, hlam, ht45, u4ehi4]
          · linarith only [h1, h11, h9, hlam]
        · linarith only [h10, h9, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
      · linarith only [h0, h9, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
  · linarith only [h0, hc45, hlam, hphi, u4ehi0]

theorem n7l_sAB2_H_R_M_IR_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h2ehi := hb2.1
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h6 | h6
            · linarith only [h1, h6, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
            · linarith only [h6, hc45, hlam, hphi, u4ehi2]
        · linarith only [h3, hc45, hlam, hphi, u4ehi1]
      · linarith only [h0, h2, hc25, hlam, hphi, u2ehi2]
    · linarith only [h0, h1, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h12 | h12
    · linarith only [h0, h12, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h14 | h14
      · linarith only [h0, h14, hc23, hlam, hphi, u2ehi4]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h16 | h16
        · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
          · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
            · rcases m.htr 3 4 5 (by decide) (by decide) with h19 | h19
              · linarith only [h17, h19, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · linarith only [h16, h19, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
            · linarith only [h12, h16, h18, hlam]
          · linarith only [h0, h17, hc34, hlam, hphi, ht23, u2ehi1]
        · linarith only [h16, hc45, hlam, hphi, u4ehi1]

theorem n7l_sAB2_H_R_M_LI_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB2_H_R_M_LI_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB2_H_R_M_LI_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB2_H_R_M_LR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB2_H_R_M_LR_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB2_H_R_M_LR_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB2_M_IR_H_I_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5emax := hb5.2.2
  have h2ehi := hb2.1
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases h5emax with h0 | h0 | h0 | h0 | h0
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
    · linarith only [h0, h1, hlam, ht23, ht34, ht45, u2ehi4]
    · linarith only [h0, h1, hlam, ht23, ht34, ht45, u2ehi0]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
    · rcases m.htr 1 4 5 (by decide) (by decide) with h5 | h5
      · linarith only [h0, h5, hlam, ht45, u4ehi4]
      · linarith only [h0, h5, hlam, ht45, u4ehi1]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h8 | h8
      · linarith only [h0, h8, hlam, ht45, u4ehi4]
      · linarith only [h0, h8, hlam, ht45, u4ehi1]
  · linarith only [h0, hlam, ht23, ht34, ht45, u2ehi4]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h12 | h12
    · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
      · rcases m.htr 3 4 5 (by decide) (by decide) with h14 | h14
        · linarith only [h0, h14, hlam, ht45, u4ehi4]
        · linarith only [h0, h14, hlam, ht45, u4ehi3]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
        · linarith only [h0, h13, h17, hlam, ht45, u4ehi1]
        · linarith only [h0, h17, hlam, ht45, u4ehi3]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h20 | h20
      · rcases m.htr 3 4 5 (by decide) (by decide) with h21 | h21
        · linarith only [h0, h21, hlam, ht45, u4ehi4]
        · linarith only [h0, h21, hlam, ht45, u4ehi3]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h24 | h24
        · linarith only [h0, h20, h24, hlam, ht45, u4ehi1]
        · linarith only [h0, h24, hlam, ht45, u4ehi3]
  · linarith only [h0, hlam, ht45, u4ehi4]

theorem n7l_sAB2_M_IR_H_L_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB2_M_IR_H_L_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB2_M_IR_H_L_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB2_M_IR_H_R_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5ehi := hb5.1
  have h2elo := hb2.1
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi2]
      · linarith only [h1, h2, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi2]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
      · linarith only [h1, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
        · linarith only [h0, h1, h7, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
          · linarith only [h0, h1, h9, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
            · linarith only [h11, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
            · linarith only [h0, h1, h11, hc23, hc45, hlam, hphi, ht34]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h14 | h14
    · linarith only [h0, h14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h16 | h16
      · linarith only [h0, h16, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
        · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
          · linarith only [h19, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h21 | h21
            · linarith only [h18, h19, h21, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h23 | h23
              · linarith only [h14, h18, h19, h21, h23, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h18, h19, h23, hc45, hlam, hphi, u4ehi3]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h26 | h26
          · linarith only [h26, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h28 | h28
            · linarith only [h28, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi4]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h30 | h30
              · linarith only [h0, h18, h28, h30, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h0, h18, h30, hc12, hc45, hlam, hphi, ht23, ht34]

theorem n7l_sAB2_M_IR_M_LI_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht45, p0_1, u4ehi4, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht45, p0_1, u4ehi4, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht45, p0_1, u4ehi4, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAB2_M_IR_M_LI_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5elo := hb5.1
  have h5emax := hb5.2.2.1
  have h2ehi := hb2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 3 4 5 (by decide) (by decide) with h6 | h6
              · linarith only [h1, h4, h6, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
              · linarith only [h6, hlam, hphi, ht45, u4ehi3, u5elo4]
            · linarith only [h4, h5, hlam, hphi, ht45, u4ehi2, u5elo3]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
            · rcases m.htr 3 4 5 (by decide) (by decide) with h11 | h11
              · linarith only [h1, h10, h11, h3, h4, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
              · linarith only [h10, h11, h4, hc45, hlam, hphi, ht23, ht34, u2ehi4]
            · linarith only [h10, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
          · linarith only [h1, h15, h3, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
            · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
              · rcases h5emax with h19 | h19 | h19 | h19 | h19
                · linarith only [h0, h19, hlam, ht45, u4ehi4]
                · linarith only [h19, h2, hlam, ht23, ht34, ht45, u2ehi4]
                · linarith only [h19, hlam, ht23, ht34, ht45, u2ehi4]
                · linarith only [h18, h19, hlam, ht45, u4ehi4]
                · linarith only [h19, hlam, ht45, u4ehi4]
              · linarith only [h18, h3, hc13, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h17, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
      · linarith only [h2, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h28 | h28
      · linarith only [h1, h28, hc23, hlam, hphi, u2ehi4]
      · linarith only [h28, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
  · linarith only [h0, hlam, hphi, ht45, u4ehi0, u5elo4]

theorem n7l_sAB2_M_IR_M_LR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h2elo := hb2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 4 5 (by decide) (by decide) with h6 | h6
              · linarith only [h3, h6, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi4]
              · linarith only [h6, hlam, hphi, ht45, u4ehi2, u5elo4]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h9 | h9
              · linarith only [h3, h9, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi9]
              · linarith only [h9, hlam, hphi, ht45, u4ehi2, u5elo4]
          · linarith only [h2, h4, hlam, hphi, ht45, u4ehi1, u5elo0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
          · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
            · rcases m.htr 2 4 5 (by decide) (by decide) with h15 | h15
              · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                · linarith only [h14, h16, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
                · linarith only [h16, hlam, hphi, ht45, u4ehi3, u5elo4]
              · linarith only [h13, h15, h3, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h20 | h20
              · rcases m.htr 3 4 5 (by decide) (by decide) with h21 | h21
                · rcases h4bigk with h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c | h22c
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [hlam, p22_0]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h0, h13, hc01, hlam, hphi, ht0b, ht5b, p22_1, u5ehi9]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h0, h13, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p22_1, u4ehi4]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h0, h13, h14, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p22_1, u4ehi4]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    rcases p22_3 (m.d 0 4) (by simp) with h27 | h27
                    · rcases p22_3 (m.d 1 4) (by simp) with h28 | h28
                      · linarith only [h0, h28, hlam]
                      · linarith only [h13, h28, hlam]
                    · linarith only [h27, hlam, p22_0]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h0, hlam, p22_0]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [hlam, p22_0]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h3, hlam, p22_1]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h14, h3, hlam, p22_1]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h3, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p22_1, u2elo3, u4ehi4]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p22_1, u2elo3, u4ehi0]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p22_1, u2elo3, u4ehi1]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [hlam, p22_0]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h14, hlam, p22_1]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p22_1, u2elo3, u4ehi4]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h1, hlam, p22_0]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h1, h13, hc04, hlam, hphi, ht0b, ht45, ht5b, p22_1, u4ehi4]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h3, hc12, hc34, hlam, hphi, ht23, p22_1]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [hlam, p22_0]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h1, hc03, hlam, hphi, ht0b, ht45, ht5b, p22_1, u4ehi4]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h2, hlam, p22_0]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h13, hlam, p22_0]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h20, hlam, p22_0]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [h21, hlam, p22_0]
                  · have p22_0 := h22c.1
                    have p22_1 := h22c.2.1
                    have p22_2 := h22c.2.2.1
                    have p22_3 := h22c.2.2.2
                    linarith only [hlam, p22_0]
                · linarith only [h13, h21, h3, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
              · linarith only [h13, h20, h3, hlam]
          · linarith only [h13, hlam, hphi, ht45, u4ehi1, u5elo4]
      · linarith only [h2, hlam, hphi, ht45, u4ehi0, u5elo4]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h56 | h56
      · rcases m.htr 1 2 4 (by decide) (by decide) with h57 | h57
        · rcases m.htr 1 4 5 (by decide) (by decide) with h58 | h58
          · rcases m.htr 2 3 4 (by decide) (by decide) with h59 | h59
            · linarith only [h0, h1, h58, h59, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h61 | h61
              · linarith only [h57, h61, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi4]
              · linarith only [h61, hlam, hphi, ht45, u4ehi2, u5elo4]
          · linarith only [h58, hlam, hphi, ht45, u4ehi1, u5elo4]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h65 | h65
          · rcases m.htr 2 3 4 (by decide) (by decide) with h66 | h66
            · linarith only [h0, h1, h65, h66, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h68 | h68
              · rcases m.htr 3 4 5 (by decide) (by decide) with h69 | h69
                · rcases h4bigk with h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c
                  · have p70_0 := h70c.1
                    have p70_1 := h70c.2.1
                    have p70_2 := h70c.2.2.1
                    have p70_3 := h70c.2.2.2
                    linarith only [hlam, p70_0]
                  · have p70_0 := h70c.1
                    have p70_1 := h70c.2.1
                    have p70_2 := h70c.2.2.1
                    have p70_3 := h70c.2.2.2
                    linarith only [h65, hc04, hlam, hphi, ht0b, ht45, ht5b, p70_1, u4ehi4]
                  · have p70_0 := h70c.1
                    have p70_1 := h70c.2.1
                    have p70_2 := h70c.2.2.1
                    have p70_3 := h70c.2.2.2
                    linarith only [h1, h57, hc12, hc34, hlam, hphi, ht23, p70_1]
                  · have p70_0 := h70c.1
                    have p70_1 := h70c.2.1
                    have p70_2 := h70c.2.2.1
                    have p70_3 := h70c.2.2.2
                    linarith only [h1, hlam, p70_1]
                  · have p70_0 := h70c.1
                    have p70_1 := h70c.2.1
                    have p70_2 := h70c.2.2.1
                    have p70_3 := h70c.2.2.2
                    rcases p70_3 (m.d 0 4) (by simp) with h75 | h75
                    · rcases p70_3 (m.d 1 4) (by simp) with h76 | h76
                      · linarith only [h0, h76, hlam]
                      · linarith only [h65, h76, hlam]
                    · linarith only [h75, hlam, p70_0]
                  · have p70_0 := h70c.1
                    have p70_1 := h70c.2.1
                    have p70_2 := h70c.2.2.1
                    have p70_3 := h70c.2.2.2
                    linarith only [h0, hlam, p70_0]
                  · have p70_0 := h70c.1
                    have p70_1 := h70c.2.1
                    have p70_2 := h70c.2.2.1
                    have p70_3 := h70c.2.2.2
                    linarith only [hlam, p70_0]
                  · have p70_0 := h70c.1
                    have p70_1 := h70c.2.1
                    have p70_2 := h70c.2.2.1
                    have p70_3 := h70c.2.2.2
                    linarith only [h57, hlam, p70_1]
                  · have p70_0 := h70c.1
                    have p70_1 := h70c.2.1
                    have p70_2 := h70c.2.2.1
                    have p70_3 := h70c.2.2.2
                    linarith only [h1, h57, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p70_1, u2elo3, u4ehi0]
                  · have p70_0 := h70c.1
                    have p70_1 := h70c.2.1
                    have p70_2 := h70c.2.2.1
                    have p70_3 := h70c.2.2.2
                    linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p70_1, u4ehi4]
                  · have p70_0 := h70c.1
                    have p70_1 := h70c.2.1
                    have p70_2 := h70c.2.2.1
                    have p70_3 := h70c.2.2.2
                    linarith only [h0, h65, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p70_1, u2elo3, u4ehi4]
                  · have p70_0 := h70c.1
                    have p70_1 := h70c.2.1
                    have p70_2 := h70c.2.2.1
                    have p70_3 := h70c.2.2.2
                    linarith only [h65, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p70_1, u2elo3, u4ehi4]
                  · have p70_0 := h70c.1
                    have p70_1 := h70c.2.1
                    have p70_2 := h70c.2.2.1
                    have p70_3 := h70c.2.2.2
                    linarith only [hlam, p70_0]
                  · have p70_0 := h70c.1
                    have p70_1 := h70c.2.1
                    have p70_2 := h70c.2.2.1
                    have p70_3 := h70c.2.2.2
                    linarith only [h66, hlam, p70_1]
                  · have p70_0 := h70c.1
                    have p70_1 := h70c.2.1
                    have p70_2 := h70c.2.2.1
                    have p70_3 := h70c.2.2.2
                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p70_1, u2elo3, u4ehi4]
                  · have p70_0 := h70c.1
                    have p70_1 := h70c.2.1
                    have p70_2 := h70c.2.2.1
                    have p70_3 := h70c.2.2.2
                    linarith only [h0, h65, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p70_1, u4ehi4]
                  · have p70_0 := h70c.1
                    have p70_1 := h70c.2.1
                    have p70_2 := h70c.2.2.1
                    have p70_3 := h70c.2.2.2
                    linarith only [h65, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p70_1, u4ehi4]
                  · have p70_0 := h70c.1
                    have p70_1 := h70c.2.1
                    have p70_2 := h70c.2.2.1
                    have p70_3 := h70c.2.2.2
                    linarith only [h57, hc12, hc34, hlam, hphi, ht23, p70_1]
                  · have p70_0 := h70c.1
                    have p70_1 := h70c.2.1
                    have p70_2 := h70c.2.2.1
                    have p70_3 := h70c.2.2.2
                    linarith only [hlam, p70_0]
                  · have p70_0 := h70c.1
                    have p70_1 := h70c.2.1
                    have p70_2 := h70c.2.2.1
                    have p70_3 := h70c.2.2.2
                    rcases p70_3 (m.d 0 4) (by simp) with h94 | h94
                    · linarith only [h1, h94, hlam]
                    · linarith only [h56, h94, hlam]
                  · have p70_0 := h70c.1
                    have p70_1 := h70c.2.1
                    have p70_2 := h70c.2.2.1
                    have p70_3 := h70c.2.2.2
                    linarith only [h56, hlam, p70_0]
                  · have p70_0 := h70c.1
                    have p70_1 := h70c.2.1
                    have p70_2 := h70c.2.2.1
                    have p70_3 := h70c.2.2.2
                    linarith only [h65, hlam, p70_0]
                  · have p70_0 := h70c.1
                    have p70_1 := h70c.2.1
                    have p70_2 := h70c.2.2.1
                    have p70_3 := h70c.2.2.2
                    linarith only [h68, hlam, p70_0]
                  · have p70_0 := h70c.1
                    have p70_1 := h70c.2.1
                    have p70_2 := h70c.2.2.1
                    have p70_3 := h70c.2.2.2
                    linarith only [h69, hlam, p70_0]
                  · have p70_0 := h70c.1
                    have p70_1 := h70c.2.1
                    have p70_2 := h70c.2.2.1
                    have p70_3 := h70c.2.2.2
                    linarith only [hlam, p70_0]
                · linarith only [h57, h65, h69, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
              · linarith only [h57, h65, h68, hlam]
          · linarith only [h65, hlam, hphi, ht45, u4ehi1, u5elo4]
      · linarith only [h0, h56, hlam, hphi, ht45, u4ehi1, u5elo4]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h106 | h106
    · rcases m.htr 0 4 5 (by decide) (by decide) with h107 | h107
      · rcases m.htr 1 2 4 (by decide) (by decide) with h108 | h108
        · rcases m.htr 1 4 5 (by decide) (by decide) with h109 | h109
          · rcases m.htr 2 3 4 (by decide) (by decide) with h110 | h110
            · rcases m.htr 2 4 5 (by decide) (by decide) with h111 | h111
              · linarith only [h108, h111, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi4]
              · linarith only [h111, hlam, hphi, ht45, u4ehi2, u5elo4]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h114 | h114
              · linarith only [h108, h114, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi9]
              · linarith only [h114, hlam, hphi, ht45, u4ehi2, u5elo4]
          · linarith only [h0, h107, h109, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h118 | h118
          · rcases m.htr 2 3 4 (by decide) (by decide) with h119 | h119
            · rcases m.htr 2 4 5 (by decide) (by decide) with h120 | h120
              · rcases m.htr 3 4 5 (by decide) (by decide) with h121 | h121
                · linarith only [h119, h121, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi9]
                · linarith only [h121, hlam, hphi, ht45, u4ehi3, u5elo4]
              · linarith only [h0, h107, h108, h120, hlam]
            · linarith only [h0, h106, h108, h119, hlam]
          · linarith only [h0, h107, h118, hlam]
      · linarith only [h107, hlam, hphi, ht45, u4ehi0, u5elo4]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h128 | h128
      · rcases m.htr 1 2 4 (by decide) (by decide) with h129 | h129
        · rcases m.htr 1 4 5 (by decide) (by decide) with h130 | h130
          · rcases m.htr 2 3 4 (by decide) (by decide) with h131 | h131
            · linarith only [h106, h128, h131, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h133 | h133
              · linarith only [h129, h133, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi4]
              · linarith only [h133, hlam, hphi, ht45, u4ehi2, u5elo4]
          · linarith only [h0, h128, h130, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h137 | h137
          · rcases m.htr 2 3 4 (by decide) (by decide) with h138 | h138
            · linarith only [h106, h128, h138, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi9]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h140 | h140
              · rcases m.htr 3 4 5 (by decide) (by decide) with h141 | h141
                · rcases h4bigk with h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [hlam, p142_0]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h0, hlam, p142_1]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h106, h129, hc12, hc34, hlam, hphi, ht23, p142_1]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h106, hlam, p142_1]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h0, h129, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p142_1, u2elo3, u4ehi4]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h129, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p142_1, u2elo3, u4ehi0]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [hlam, p142_0]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h129, hlam, p142_1]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h129, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p142_1, u2elo3, u4ehi3]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h129, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p142_1, u2elo3, u4ehi4]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h128, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p142_1, u2elo3, u4ehi4]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p142_1, u2elo3, u4ehi1]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [hlam, p142_0]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h138, hlam, p142_1]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p142_1, u2elo3, u4ehi4]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h128, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p142_1, u4ehi4]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h0, h128, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p142_1, u4ehi4]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h129, hc12, hc34, hlam, hphi, ht23, p142_1]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [hlam, p142_0]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    rcases p142_3 (m.d 0 4) (by simp) with h162 | h162
                    · linarith only [h106, h162, hlam]
                    · linarith only [h128, h162, hlam]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h128, hlam, p142_0]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h137, hlam, p142_0]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h140, hlam, p142_0]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [h141, hlam, p142_0]
                  · have p142_0 := h142c.1
                    have p142_1 := h142c.2.1
                    have p142_2 := h142c.2.2.1
                    have p142_3 := h142c.2.2.2
                    linarith only [hlam, p142_0]
                · linarith only [h0, h128, h129, h141, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
              · linarith only [h0, h128, h129, h140, hlam]
          · linarith only [h0, h128, h137, hlam]
      · linarith only [h128, hlam, hphi, ht45, u4ehi0, u5elo4]

theorem n7l_sAB2_M_IR_M_LR_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h2ehi := hb2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h5, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                      · linarith only [h0, h11, h6, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                      · linarith only [h11, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                  · linarith only [h8, hlam, hphi, ht45, u4ehi1, u5elo4]
                · linarith only [h3, h7, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo0]
              · linarith only [h5, h6, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h17 | h17
              · linarith only [h17, h5, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h19 | h19
                · linarith only [h0, h17, h19, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi7]
                · linarith only [h19, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo2]
          · linarith only [h4, hlam, hphi, ht45, u4ehi0, u5elo4]
        · linarith only [h3, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h24 | h24
        · linarith only [h2, h24, hc24, hlam, hphi, u2ehi4]
        · linarith only [h24, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h27 | h27
      · linarith only [h0, h1, h27, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h29 | h29
        · linarith only [h27, h29, hc24, hlam, hphi, u2ehi4]
        · linarith only [h29, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h32 | h32
    · rcases m.htr 0 2 4 (by decide) (by decide) with h33 | h33
      · rcases m.htr 0 2 5 (by decide) (by decide) with h34 | h34
        · rcases m.htr 0 4 5 (by decide) (by decide) with h35 | h35
          · rcases m.htr 1 2 3 (by decide) (by decide) with h36 | h36
            · rcases m.htr 1 2 4 (by decide) (by decide) with h37 | h37
              · rcases m.htr 1 2 5 (by decide) (by decide) with h38 | h38
                · rcases m.htr 1 4 5 (by decide) (by decide) with h39 | h39
                  · linarith only [h0, h32, h39, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                  · linarith only [h39, hlam, hphi, ht45, u4ehi1, u5elo4]
                · linarith only [h0, h32, h34, h38, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
              · linarith only [h0, h32, h35, h37, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
            · linarith only [h0, h32, h35, h36, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
          · linarith only [h35, hlam, hphi, ht45, u4ehi0, u5elo4]
        · linarith only [h34, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
      · linarith only [h0, h32, h33, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h48 | h48
      · rcases m.htr 0 2 5 (by decide) (by decide) with h49 | h49
        · rcases m.htr 0 4 5 (by decide) (by decide) with h50 | h50
          · rcases m.htr 1 2 3 (by decide) (by decide) with h51 | h51
            · rcases m.htr 1 2 4 (by decide) (by decide) with h52 | h52
              · rcases m.htr 1 2 5 (by decide) (by decide) with h53 | h53
                · rcases m.htr 1 4 5 (by decide) (by decide) with h54 | h54
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h55 | h55
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h56 | h56
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h57 | h57
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h58 | h58
                          · linarith only [h51, h55, h58, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h48, h57, h58, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · linarith only [h57, hlam, hphi, ht45, u4ehi2, u5elo4]
                      · linarith only [h56, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h63 | h63
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h64 | h64
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h65 | h65
                          · rcases h4bigk with h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c | h66c
                            · have p66_0 := h66c.1
                              have p66_1 := h66c.2.1
                              have p66_2 := h66c.2.2.1
                              have p66_3 := h66c.2.2.2
                              linarith only [hlam, p66_0]
                            · have p66_0 := h66c.1
                              have p66_1 := h66c.2.1
                              have p66_2 := h66c.2.2.1
                              have p66_3 := h66c.2.2.2
                              linarith only [h32, hlam, p66_1]
                            · have p66_0 := h66c.1
                              have p66_1 := h66c.2.1
                              have p66_2 := h66c.2.2.1
                              have p66_3 := h66c.2.2.2
                              linarith only [h55, h63, h65, hc04, hlam, hphi, ht0b, ht45, ht5b, p66_1, u4ehi4]
                            · have p66_0 := h66c.1
                              have p66_1 := h66c.2.1
                              have p66_2 := h66c.2.2.1
                              have p66_3 := h66c.2.2.2
                              linarith only [h0, h48, h55, h63, h65, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p66_1, u4ehi4]
                            · have p66_0 := h66c.1
                              have p66_1 := h66c.2.1
                              have p66_2 := h66c.2.2.1
                              have p66_3 := h66c.2.2.2
                              rcases p66_3 (m.d 0 4) (by simp) with h71 | h71
                              · rcases p66_3 (m.d 1 4) (by simp) with h72 | h72
                                · rcases p66_3 (m.d 2 4) (by simp) with h73 | h73
                                  · linarith only [h48, h73, hlam]
                                  · linarith only [h64, h73, hlam]
                                · linarith only [h54, h72, hlam]
                              · linarith only [h71, hlam, p66_0]
                            · have p66_0 := h66c.1
                              have p66_1 := h66c.2.1
                              have p66_2 := h66c.2.2.1
                              have p66_3 := h66c.2.2.2
                              linarith only [h48, h52, h55, h63, h65, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p66_1, u4ehi4]
                            · have p66_0 := h66c.1
                              have p66_1 := h66c.2.1
                              have p66_2 := h66c.2.2.1
                              have p66_3 := h66c.2.2.2
                              linarith only [hlam, p66_0]
                            · have p66_0 := h66c.1
                              have p66_1 := h66c.2.1
                              have p66_2 := h66c.2.2.1
                              have p66_3 := h66c.2.2.2
                              linarith only [h52, h55, h63, h65, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p66_1, u4ehi4]
                            · have p66_0 := h66c.1
                              have p66_1 := h66c.2.1
                              have p66_2 := h66c.2.2.1
                              have p66_3 := h66c.2.2.2
                              linarith only [h52, h55, h63, h65, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p66_1, u4ehi4]
                            · have p66_0 := h66c.1
                              have p66_1 := h66c.2.1
                              have p66_2 := h66c.2.2.1
                              have p66_3 := h66c.2.2.2
                              rcases p66_3 (m.d 0 4) (by simp) with h82 | h82
                              · linarith only [h32, h82, hlam]
                              · linarith only [h50, h82, hlam]
                            · have p66_0 := h66c.1
                              have p66_1 := h66c.2.1
                              have p66_2 := h66c.2.2.1
                              have p66_3 := h66c.2.2.2
                              linarith only [h48, hlam, p66_0]
                            · have p66_0 := h66c.1
                              have p66_1 := h66c.2.1
                              have p66_2 := h66c.2.2.1
                              have p66_3 := h66c.2.2.2
                              linarith only [h52, hlam, p66_0]
                            · have p66_0 := h66c.1
                              have p66_1 := h66c.2.1
                              have p66_2 := h66c.2.2.1
                              have p66_3 := h66c.2.2.2
                              linarith only [hlam, p66_0]
                            · have p66_0 := h66c.1
                              have p66_1 := h66c.2.1
                              have p66_2 := h66c.2.2.1
                              have p66_3 := h66c.2.2.2
                              linarith only [h55, hlam, p66_1]
                            · have p66_0 := h66c.1
                              have p66_1 := h66c.2.1
                              have p66_2 := h66c.2.2.1
                              have p66_3 := h66c.2.2.2
                              linarith only [h0, h48, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p66_1, u4ehi4]
                            · have p66_0 := h66c.1
                              have p66_1 := h66c.2.1
                              have p66_2 := h66c.2.2.1
                              have p66_3 := h66c.2.2.2
                              linarith only [h48, hc34, hlam, hphi, ht23, p66_1, u2ehi3]
                            · have p66_0 := h66c.1
                              have p66_1 := h66c.2.1
                              have p66_2 := h66c.2.2.1
                              have p66_3 := h66c.2.2.2
                              linarith only [h32, hc01, hc34, hlam, hphi, ht12, ht23, p66_1]
                            · have p66_0 := h66c.1
                              have p66_1 := h66c.2.1
                              have p66_2 := h66c.2.2.1
                              have p66_3 := h66c.2.2.2
                              linarith only [h55, h63, h65, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p66_1, u4ehi4]
                            · have p66_0 := h66c.1
                              have p66_1 := h66c.2.1
                              have p66_2 := h66c.2.2.1
                              have p66_3 := h66c.2.2.2
                              linarith only [hlam, p66_0]
                            · have p66_0 := h66c.1
                              have p66_1 := h66c.2.1
                              have p66_2 := h66c.2.2.1
                              have p66_3 := h66c.2.2.2
                              rcases p66_3 (m.d 0 4) (by simp) with h94 | h94
                              · rcases p66_3 (m.d 1 4) (by simp) with h95 | h95
                                · rcases p66_3 (m.d 2 4) (by simp) with h96 | h96
                                  · linarith only [h55, h96, hlam]
                                  · linarith only [h64, h96, hlam]
                                · linarith only [h54, h95, hlam]
                              · linarith only [h50, h94, hlam]
                            · have p66_0 := h66c.1
                              have p66_1 := h66c.2.1
                              have p66_2 := h66c.2.2.1
                              have p66_3 := h66c.2.2.2
                              linarith only [h50, hlam, p66_0]
                            · have p66_0 := h66c.1
                              have p66_1 := h66c.2.1
                              have p66_2 := h66c.2.2.1
                              have p66_3 := h66c.2.2.2
                              linarith only [h54, hlam, p66_0]
                            · have p66_0 := h66c.1
                              have p66_1 := h66c.2.1
                              have p66_2 := h66c.2.2.1
                              have p66_3 := h66c.2.2.2
                              linarith only [h64, hlam, p66_0]
                            · have p66_0 := h66c.1
                              have p66_1 := h66c.2.1
                              have p66_2 := h66c.2.2.1
                              have p66_3 := h66c.2.2.2
                              linarith only [h65, hlam, p66_0]
                            · have p66_0 := h66c.1
                              have p66_1 := h66c.2.1
                              have p66_2 := h66c.2.2.1
                              have p66_3 := h66c.2.2.2
                              linarith only [hlam, p66_0]
                          · linarith only [h55, h63, h65, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi8]
                        · linarith only [h50, h64, hlam, hphi, ht45, u4ehi2, u5elo0]
                      · linarith only [h63, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                  · linarith only [h32, h50, h54, hlam]
                · linarith only [h0, h49, h53, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo0]
              · linarith only [h0, h48, h52, hlam]
            · linarith only [h0, h48, h51, hc23, hlam, hphi, u2ehi3]
          · linarith only [h50, hlam, hphi, ht45, u4ehi0, u5elo4]
        · linarith only [h48, h49, hc25, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h115 | h115
        · linarith only [h115, h48, hc24, hlam, hphi, u2ehi4]
        · linarith only [h115, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]

theorem n7l_sAB2_M_LI_H_I_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have h2elo := hb2.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u4elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, p0_1, u4elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, p0_1, u4elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h5 | h5
    · rcases p0_3 (m.d 1 4) (by simp) with h6 | h6
      · rcases p0_3 (m.d 2 4) (by simp) with h7 | h7
        · rcases p0_3 (m.d 3 4) (by simp) with h8 | h8
          · rcases p0_3 (m.d 4 5) (by simp) with h9 | h9
            · linarith only [h9, hlam, p0_0]
            · rcases m.htr 0 2 3 (by decide) (by decide) with h11 | h11
              · rcases m.htr 0 2 4 (by decide) (by decide) with h12 | h12
                · linarith only [h12, h7, hlam]
                · linarith only [h11, h12, hc23, hlam, hphi, ht34, u4elo2]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h15 | h15
                · linarith only [h15, h7, hlam]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h17 | h17
                  · linarith only [h17, h8, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h19 | h19
                    · linarith only [h15, h19, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h21 | h21
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                        · linarith only [h17, h22, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo2]
                        · linarith only [h11, h19, h21, h22, hc02, hlam, hphi, ht23, ht34, u4elo2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h25 | h25
                        · linarith only [h21, h25, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo2]
                        · linarith only [h11, h25, hc02, hlam, hphi, ht23, ht34, u4elo3]
          · linarith only [h8, hc34, hlam, hphi, p0_1, u4elo0]
        · linarith only [h6, h7, hc24, hlam, hphi, p0_1, u4elo1]
      · linarith only [h6, hc14, hlam, hphi, p0_1, u4elo0]
    · linarith only [h5, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h36 | h36
    · rcases p0_3 (m.d 1 4) (by simp) with h37 | h37
      · rcases p0_3 (m.d 2 4) (by simp) with h38 | h38
        · rcases p0_3 (m.d 3 4) (by simp) with h39 | h39
          · rcases p0_3 (m.d 4 5) (by simp) with h40 | h40
            · linarith only [h40, hlam, p0_0]
            · rcases m.htr 0 2 3 (by decide) (by decide) with h42 | h42
              · rcases m.htr 0 2 4 (by decide) (by decide) with h43 | h43
                · linarith only [h38, h43, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo0]
                · linarith only [h42, h43, hc23, hlam, hphi, ht34, u4elo2]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h46 | h46
                · linarith only [h38, h42, h46, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo2]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h48 | h48
                  · linarith only [h39, h42, h48, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h50 | h50
                    · linarith only [h38, h50, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h52 | h52
                      · linarith only [h39, h52, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h54 | h54
                        · linarith only [h36, h48, h54, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo2]
                        · linarith only [h42, h54, hc02, hlam, hphi, ht23, ht34, u4elo3]
          · linarith only [h36, h39, hc34, hlam, hphi, p0_1, u4elo0]
        · linarith only [h36, h38, hc24, hlam, hphi, p0_1, u4elo0]
      · linarith only [h37, hlam, p0_0]
    · linarith only [h36, hc04, hlam, hphi, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u4elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u4elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, p0_1, u4elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h65 | h65
    · rcases p0_3 (m.d 1 4) (by simp) with h66 | h66
      · rcases p0_3 (m.d 2 4) (by simp) with h67 | h67
        · rcases p0_3 (m.d 3 4) (by simp) with h68 | h68
          · rcases p0_3 (m.d 4 5) (by simp) with h69 | h69
            · linarith only [h69, hlam, p0_0]
            · rcases m.htr 0 2 3 (by decide) (by decide) with h71 | h71
              · rcases m.htr 0 2 4 (by decide) (by decide) with h72 | h72
                · linarith only [h72, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo0]
                · linarith only [h65, h72, hlam]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h75 | h75
                · linarith only [h71, h75, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo2]
                · linarith only [h65, h75, hlam]
          · linarith only [h66, h68, hc34, hlam, hphi, p0_1, u4elo1]
        · linarith only [h67, hlam, p0_0]
      · linarith only [h65, h66, hc14, hlam, hphi, p0_1, u4elo0]
    · linarith only [h65, hc04, hlam, hphi, p0_1, u4elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u4elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u4elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, p0_1, u4elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h86 | h86
    · rcases p0_3 (m.d 1 4) (by simp) with h87 | h87
      · rcases p0_3 (m.d 2 4) (by simp) with h88 | h88
        · rcases p0_3 (m.d 3 4) (by simp) with h89 | h89
          · rcases p0_3 (m.d 4 5) (by simp) with h90 | h90
            · linarith only [h90, hlam, p0_0]
            · rcases m.htr 0 2 3 (by decide) (by decide) with h92 | h92
              · rcases m.htr 0 2 4 (by decide) (by decide) with h93 | h93
                · linarith only [h88, h93, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo0]
                · linarith only [h92, h93, hc23, hlam, hphi, ht34, u4elo2]
              · rcases m.htr 0 2 4 (by decide) (by decide) with h96 | h96
                · linarith only [h88, h92, h96, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo2]
                · rcases m.htr 0 3 4 (by decide) (by decide) with h98 | h98
                  · linarith only [h92, h98, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo2]
                  · linarith only [h86, h98, hlam]
          · linarith only [h89, hlam, p0_0]
        · linarith only [h87, h88, hc24, hlam, hphi, p0_1, u4elo1]
      · linarith only [h87, hc14, hlam, hphi, p0_1, u4elo3]
    · linarith only [h86, hc04, hlam, hphi, p0_1, u4elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u4elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u4elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, p0_1, u4elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, p0_1, u4elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAB2_M_LI_H_I_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have h2ehi := hb2.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 3 4 5 (by decide) (by decide) with h7 | h7
                · rcases h4bigk with h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c | h8c
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hc14, hlam, hphi, p8_1, u4elo0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hc24, hlam, hphi, p8_1, u4elo0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hc34, hlam, hphi, p8_1, u4elo0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    rcases p8_3 (m.d 0 4) (by simp) with h13 | h13
                    · rcases p8_3 (m.d 1 4) (by simp) with h14 | h14
                      · rcases p8_3 (m.d 2 4) (by simp) with h15 | h15
                        · linarith only [h0, h15, hlam]
                        · linarith only [h15, h6, hlam]
                      · linarith only [h14, h3, h6, h7, hlam, hphi, ht23, ht34, u2ehi4, u4elo3]
                    · linarith only [h13, hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hc04, hlam, hphi, p8_1, u4elo1]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h6, hlam, hphi, ht23, ht34, p8_1, u2ehi4, u4elo1]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hc34, hlam, hphi, p8_1, u4elo1]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    rcases p8_3 (m.d 0 4) (by simp) with h24 | h24
                    · rcases p8_3 (m.d 1 4) (by simp) with h25 | h25
                      · rcases p8_3 (m.d 2 4) (by simp) with h26 | h26
                        · linarith only [h26, h3, hlam]
                        · linarith only [h26, h6, hlam]
                      · linarith only [h25, hlam, p8_0]
                    · linarith only [h24, hc04, hlam, hphi, p8_1, u4elo1]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h0, hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h3, hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h0, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p8_1, u4elo0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    rcases p8_3 (m.d 0 4) (by simp) with h35 | h35
                    · rcases p8_3 (m.d 1 4) (by simp) with h36 | h36
                      · rcases p8_3 (m.d 2 4) (by simp) with h37 | h37
                        · rcases p8_3 (m.d 3 4) (by simp) with h38 | h38
                          · linarith only [h38, h5, hlam]
                          · linarith only [h38, h7, hlam]
                        · linarith only [h37, hlam, p8_0]
                      · linarith only [h3, h36, h7, hlam, hphi, ht23, ht34, u2ehi3, u4elo3]
                    · linarith only [h3, h35, hc04, hlam, hphi, p8_1, u4elo1]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h1, hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h2, h5, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p8_1]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h5, hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h2, h5, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p8_1]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hc04, hlam, hphi, p8_1, u4elo4]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h3, h5, h7, hlam, p8_1]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h6, hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [h7, hlam, p8_0]
                  · have p8_0 := h8c.1
                    have p8_1 := h8c.2.1
                    have p8_2 := h8c.2.2.1
                    have p8_3 := h8c.2.2.2
                    linarith only [hlam, p8_0]
                · linarith only [h0, h6, h7, hc34, hlam, hphi, u4elo0]
              · linarith only [h6, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
            · linarith only [h5, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
          · linarith only [h2, h4, hc25, hlam, hphi, u2ehi2]
        · linarith only [h2, h3, hc24, hlam, hphi, u2ehi2]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h59 | h59
        · linarith only [h2, h59, hc23, hlam, hphi, u2ehi3]
        · linarith only [h59, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h62 | h62
      · rcases m.htr 1 2 4 (by decide) (by decide) with h63 | h63
        · rcases m.htr 1 2 5 (by decide) (by decide) with h64 | h64
          · rcases m.htr 2 3 4 (by decide) (by decide) with h65 | h65
            · linarith only [h0, h1, h65, hlam]
            · linarith only [h65, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
          · linarith only [h62, h64, hc25, hlam, hphi, u2ehi2]
        · linarith only [h0, h1, h62, h63, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h70 | h70
        · linarith only [h62, h70, hc23, hlam, hphi, u2ehi3]
        · linarith only [h70, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]
  · linarith only [h0, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]

theorem n7l_sAB2_M_LI_H_L_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have h5elo := hb5.1
  have h2elo := hb2.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u4elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, p0_1, u4elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, p0_1, u4elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h5 | h5
    · rcases p0_3 (m.d 1 4) (by simp) with h6 | h6
      · rcases p0_3 (m.d 2 4) (by simp) with h7 | h7
        · rcases p0_3 (m.d 3 4) (by simp) with h8 | h8
          · rcases p0_3 (m.d 4 5) (by simp) with h9 | h9
            · linarith only [h9, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h11 | h11
              · linarith only [h11, h6, hlam]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h13 | h13
                · rcases m.htr 0 2 4 (by decide) (by decide) with h14 | h14
                  · linarith only [h14, h7, hlam]
                  · linarith only [h13, h14, hc23, hlam, hphi, ht34, u4elo2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h17 | h17
                  · linarith only [h17, h7, hlam]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h19 | h19
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h20 | h20
                      · linarith only [h20, h8, hlam]
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h22 | h22
                        · linarith only [h13, h22, hc02, hlam, hphi, u2elo1]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
                          · linarith only [h17, h22, h24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo2]
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h26 | h26
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h27 | h27
                              · linarith only [h20, h22, h27, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo2]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h29 | h29
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h30 | h30
                                  · linarith only [h11, h27, h30, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo2]
                                  · linarith only [h13, h19, h30, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                                · linarith only [h11, h29, hlam, p0_1]
                            · linarith only [h11, h26, hc12, hc45, hlam, hphi, ht23, ht34, p0_1, u4elo1, u5elo2]
                    · linarith only [h11, h19, hc02, hc45, hlam, hphi, ht23, ht34, p0_1, u4elo1, u5elo2]
          · linarith only [h8, hc34, hlam, hphi, p0_1, u4elo0]
        · linarith only [h7, hc24, hlam, hphi, p0_1, u4elo0]
      · linarith only [h6, hc14, hlam, hphi, p0_1, u4elo0]
    · linarith only [h5, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h44 | h44
    · rcases p0_3 (m.d 1 4) (by simp) with h45 | h45
      · rcases p0_3 (m.d 2 4) (by simp) with h46 | h46
        · rcases p0_3 (m.d 3 4) (by simp) with h47 | h47
          · rcases p0_3 (m.d 4 5) (by simp) with h48 | h48
            · linarith only [h48, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h50 | h50
              · rcases m.htr 0 2 3 (by decide) (by decide) with h51 | h51
                · rcases m.htr 0 2 4 (by decide) (by decide) with h52 | h52
                  · linarith only [h46, h52, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo0]
                  · linarith only [h51, h52, hc23, hlam, hphi, ht34, u4elo2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h55 | h55
                  · linarith only [h46, h51, h55, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo2]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h57 | h57
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h58 | h58
                      · linarith only [h47, h51, h58, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo2]
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h60 | h60
                        · linarith only [h51, h60, hc02, hlam, hphi, u2elo1]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h62 | h62
                          · linarith only [h46, h62, hlam]
                          · rcases m.htr 1 2 5 (by decide) (by decide) with h64 | h64
                            · rcases m.htr 1 3 4 (by decide) (by decide) with h65 | h65
                              · linarith only [h47, h65, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h67 | h67
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h68 | h68
                                  · linarith only [h65, h68, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo2]
                                  · linarith only [h51, h57, h68, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                                · linarith only [h67, hlam, p0_0]
                            · linarith only [h64, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                    · linarith only [h50, h55, h57, hc02, hc45, hlam, hphi, ht23, ht34, p0_1, u4elo2, u5elo2]
              · linarith only [h44, h50, hlam]
          · linarith only [h47, hc34, hlam, hphi, p0_1, u4elo1]
        · linarith only [h44, h46, hc24, hlam, hphi, p0_1, u4elo0]
      · linarith only [h45, hlam, p0_0]
    · linarith only [h44, hc04, hlam, hphi, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u4elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u4elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, p0_1, u4elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h83 | h83
    · rcases p0_3 (m.d 1 4) (by simp) with h84 | h84
      · rcases p0_3 (m.d 2 4) (by simp) with h85 | h85
        · rcases p0_3 (m.d 3 4) (by simp) with h86 | h86
          · rcases p0_3 (m.d 4 5) (by simp) with h87 | h87
            · linarith only [h87, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h89 | h89
              · rcases m.htr 0 2 3 (by decide) (by decide) with h90 | h90
                · rcases m.htr 0 2 4 (by decide) (by decide) with h91 | h91
                  · linarith only [h91, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo0]
                  · linarith only [h83, h91, hlam]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h94 | h94
                  · linarith only [h90, h94, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo2]
                  · linarith only [h83, h94, hlam]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h97 | h97
                · rcases m.htr 0 2 4 (by decide) (by decide) with h98 | h98
                  · linarith only [h98, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo0]
                  · linarith only [h83, h98, hlam]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h101 | h101
                  · linarith only [h101, h97, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo2]
                  · linarith only [h101, h83, hlam]
          · linarith only [h86, hc34, hlam, hphi, p0_1, u4elo2]
        · linarith only [h85, hlam, p0_0]
      · linarith only [h84, hc14, hlam, hphi, p0_1, u4elo2]
    · linarith only [h83, hc04, hlam, hphi, p0_1, u4elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u4elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u4elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, p0_1, u4elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h112 | h112
    · rcases p0_3 (m.d 1 4) (by simp) with h113 | h113
      · rcases p0_3 (m.d 2 4) (by simp) with h114 | h114
        · rcases p0_3 (m.d 3 4) (by simp) with h115 | h115
          · rcases p0_3 (m.d 4 5) (by simp) with h116 | h116
            · linarith only [h116, hlam, p0_0]
            · rcases m.htr 0 1 4 (by decide) (by decide) with h118 | h118
              · rcases m.htr 0 2 3 (by decide) (by decide) with h119 | h119
                · rcases m.htr 0 2 4 (by decide) (by decide) with h120 | h120
                  · linarith only [h114, h120, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo0]
                  · linarith only [h119, h120, hc23, hlam, hphi, ht34, u4elo2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h123 | h123
                  · linarith only [h114, h119, h123, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo2]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h125 | h125
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h126 | h126
                      · linarith only [h119, h126, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo2]
                      · linarith only [h112, h126, hlam]
                    · linarith only [h125, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · rcases m.htr 0 2 3 (by decide) (by decide) with h130 | h130
                · rcases m.htr 0 2 4 (by decide) (by decide) with h131 | h131
                  · linarith only [h114, h131, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo0]
                  · linarith only [h130, h131, hc23, hlam, hphi, ht34, u4elo2]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h134 | h134
                  · linarith only [h114, h130, h134, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo2]
                  · rcases m.htr 0 2 5 (by decide) (by decide) with h136 | h136
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h137 | h137
                      · linarith only [h130, h137, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u2elo2]
                      · linarith only [h112, h137, hlam]
                    · linarith only [h136, hc02, hlam, hphi, ht23, ht34, ht45, u5elo2]
          · linarith only [h115, hlam, p0_0]
        · linarith only [h112, h114, hc24, hlam, hphi, p0_1, u4elo0]
      · linarith only [h112, h113, hc14, hlam, hphi, p0_1, u4elo0]
    · linarith only [h112, hc04, hlam, hphi, p0_1, u4elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u4elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht45, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht45, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht45, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAB2_M_LI_H_L_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h2ehi := hb2.1
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  linarith only [hlam, hphi, ht23, ht34, ht45, u2ehi4, u5elo2]

theorem n7l_sAB2_M_LI_H_R_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.1
  have h2elo := hb2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  rcases m.htr 2 3 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 2 3 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h3 | h3
      · linarith only [h0, h1, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
      · linarith only [h0, h1, h3, hc34, hlam, hphi, u4elo4]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h6 | h6
    · linarith only [h6, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi3]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
      · linarith only [h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi4]
      · linarith only [h0, h8, hc23, hlam, hphi, ht34, u4elo4]

theorem n7l_sAB2_M_LI_H_R_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h6 | h6
            · linarith only [h1, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0, u5ehi4]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
              · linarith only [h3, h4, h6, h8, hlam]
              · linarith only [h3, h4, h8, hc34, hlam, hphi, u4elo4]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
          · linarith only [h11, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
            · linarith only [h13, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi4]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
              · linarith only [h13, h15, h3, hc23, hlam, hphi, ht34, u4elo3]
              · linarith only [h15, h3, hc23, hlam, hphi, ht34, u4elo4]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
        · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
          · linarith only [h0, h19, h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h21 | h21
            · linarith only [h0, h18, h19, h2, h21, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u4elo2, u5ehi4]
            · linarith only [h0, h18, h2, h21, hc34, hlam, hphi, u4elo4]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
          · linarith only [h18, h24, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
            · linarith only [h1, h26, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
            · linarith only [h0, h2, h26, hc23, hlam, hphi, ht34, u4elo4]
    · linarith only [h0, h1, hc23, hlam, hphi, ht34, u4elo2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h30 | h30
    · rcases m.htr 0 2 5 (by decide) (by decide) with h31 | h31
      · linarith only [h0, h31, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
        · rcases m.htr 2 3 5 (by decide) (by decide) with h34 | h34
          · rcases m.htr 2 4 5 (by decide) (by decide) with h35 | h35
            · linarith only [h35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi4]
            · linarith only [h30, h31, h35, hc24, hlam, hphi, u4elo4]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h38 | h38
            · linarith only [h30, h38, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
            · linarith only [h0, h30, h34, h38, hc24, hlam, hphi, u4elo4]
        · linarith only [h0, h30, h33, hc24, hlam, hphi, u4elo3]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h42 | h42
      · linarith only [h30, h42, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h44 | h44
        · rcases m.htr 2 3 5 (by decide) (by decide) with h45 | h45
          · rcases m.htr 2 4 5 (by decide) (by decide) with h46 | h46
            · linarith only [h46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi4]
            · linarith only [h30, h46, hc02, hlam, hphi, ht23, ht34, u4elo4]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h49 | h49
            · linarith only [h49, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi4]
            · linarith only [h30, h49, hc02, hlam, hphi, ht23, ht34, u4elo4]
        · linarith only [h0, h44, hc02, hlam, hphi, ht23, ht34, u4elo3]

theorem n7l_sAB2_M_LI_H_R_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.1
  have h2ehi := hb2.1
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  rcases m.htr 2 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi4]
  · linarith only [h0, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]

theorem n7l_sAB2_M_LI_M_IR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have h5ehi := hb5.2.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u4elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, p0_1, u4elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, p0_1, u4elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo0, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u4elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u4elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, p0_1, u4elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo2, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u4elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u4elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, p0_1, u4elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo3, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u4elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u4elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, p0_1, u4elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, p0_1, u4elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAB2_M_LI_M_IR_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have h5ehi := hb5.2.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u4elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, p0_1, u4elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, p0_1, u4elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo0, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u4elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u4elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, p0_1, u4elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo2, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u4elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u4elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, p0_1, u4elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo3, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u4elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u4elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, p0_1, u4elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, p0_1, u4elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAB2_M_LI_M_IR_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.2.1
  have h2ehi := hb2.1
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 3 4 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h2, h4, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
          · linarith only [h1, h3, h4, hc34, hlam, hphi, u4elo1]
        · linarith only [h3, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
      · linarith only [h2, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
    · linarith only [h1, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
    · linarith only [h0, h10, hc23, hlam, hphi, u2ehi3]
    · linarith only [h10, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]

theorem n7l_sAB2_M_LI_M_LI_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAB2_M_LI_M_LI_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases h5bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u5elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc05, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc15, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc25, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc35, hlam, hphi, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAB2_M_LI_M_LI_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have h5elo := hb5.1
  have h2ehi := hb2.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12 | h12
                          · linarith only [h0, h10, h12, h5, hc01, hc45, hlam, hphi, ht0b, ht5b]
                          · linarith only [h12, h4, hc34, hlam, hphi, u4elo0]
                        · linarith only [h11, h4, hc24, hlam, hphi, u4elo0]
                      · linarith only [h10, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
                    · linarith only [h4, h9, hc14, hlam, hphi, u4elo0]
                  · linarith only [h5, h8, hlam, hphi, ht23, ht34, ht45, u2ehi2, u5elo3]
                · linarith only [h5, h7, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
              · linarith only [h6, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h21 | h21
              · linarith only [h21, h5, hc23, hlam, hphi, u2ehi3]
              · linarith only [h21, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]
          · linarith only [h2, h4, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
        · linarith only [h3, hlam, hphi, ht23, ht34, ht45, u2ehi0, u5elo2]
      · linarith only [h0, h2, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]
    · linarith only [h0, h1, hlam, hphi, ht23, ht34, ht45, u2ehi1, u5elo1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h28 | h28
    · rcases m.htr 0 2 4 (by decide) (by decide) with h29 | h29
      · rcases m.htr 0 2 5 (by decide) (by decide) with h30 | h30
        · rcases m.htr 0 4 5 (by decide) (by decide) with h31 | h31
          · rcases m.htr 1 2 3 (by decide) (by decide) with h32 | h32
            · rcases m.htr 1 2 4 (by decide) (by decide) with h33 | h33
              · rcases m.htr 1 3 4 (by decide) (by decide) with h34 | h34
                · rcases m.htr 1 3 5 (by decide) (by decide) with h35 | h35
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h36 | h36
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h37 | h37
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h38 | h38
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h39 | h39
                          · rcases h4bigk with h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [hlam, p40_0]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [hc14, hlam, hphi, p40_1, u4elo0]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [hlam, hphi, ht23, ht34, p40_1, u2ehi3, u4elo0]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h39, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p40_1, u4elo0]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              rcases p40_3 (m.d 0 4) (by simp) with h45 | h45
                              · rcases p40_3 (m.d 1 4) (by simp) with h46 | h46
                                · rcases p40_3 (m.d 2 4) (by simp) with h47 | h47
                                  · linarith only [h29, h47, hlam]
                                  · linarith only [h38, h47, hlam]
                                · linarith only [h36, h46, hlam]
                              · linarith only [h45, hlam, p40_0]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [hc04, hlam, hphi, p40_1, u4elo1]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [hlam, p40_0]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h38, hlam, hphi, ht23, ht34, p40_1, u2ehi4, u4elo1]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h39, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p40_1, u4elo1]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              rcases p40_3 (m.d 0 4) (by simp) with h56 | h56
                              · rcases p40_3 (m.d 1 4) (by simp) with h57 | h57
                                · rcases p40_3 (m.d 2 4) (by simp) with h58 | h58
                                  · linarith only [h33, h58, hlam]
                                  · linarith only [h38, h58, hlam]
                                · linarith only [h57, hlam, p40_0]
                              · linarith only [h31, h56, hlam]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h29, hlam, p40_0]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h33, hlam, p40_0]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [hlam, p40_0]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h29, h39, hc02, hc45, hlam, hphi, ht0b, ht5b, p40_1]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              rcases p40_3 (m.d 0 4) (by simp) with h67 | h67
                              · rcases p40_3 (m.d 1 4) (by simp) with h68 | h68
                                · rcases p40_3 (m.d 2 4) (by simp) with h69 | h69
                                  · rcases p40_3 (m.d 3 4) (by simp) with h70 | h70
                                    · linarith only [h37, h70, hlam]
                                    · linarith only [h39, h70, hlam]
                                  · linarith only [h69, hlam, p40_0]
                                · linarith only [h36, h68, hlam]
                              · linarith only [h31, h67, hlam]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [hc04, hlam, hphi, p40_1, u4elo3]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h34, hlam, p40_0]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h37, hlam, p40_0]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [hlam, p40_0]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h32, h37, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40_1]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h31, hlam, p40_0]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h36, hlam, p40_0]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h38, hlam, p40_0]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [h39, hlam, p40_0]
                            · have p40_0 := h40c.1
                              have p40_1 := h40c.2.1
                              have p40_2 := h40c.2.2.1
                              have p40_3 := h40c.2.2.2
                              linarith only [hlam, p40_0]
                          · linarith only [h31, h39, hc34, hlam, hphi, u4elo0]
                        · linarith only [h31, h38, hlam, hphi, ht23, ht34, u2ehi3, u4elo0]
                      · linarith only [h37, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
                    · linarith only [h31, h33, h36, hlam, hphi, ht23, ht34, u2ehi3, u4elo0]
                  · linarith only [h33, h34, h35, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo3]
                · linarith only [h32, h34, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
              · linarith only [h0, h33, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · linarith only [h0, h28, h30, h32, hc23, hlam, hphi, u2ehi4]
          · linarith only [h29, h31, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
        · linarith only [h29, h30, hc25, hlam, hphi, u2ehi3]
      · linarith only [h29, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h97 | h97
      · rcases m.htr 0 2 5 (by decide) (by decide) with h98 | h98
        · rcases m.htr 0 4 5 (by decide) (by decide) with h99 | h99
          · rcases m.htr 1 2 3 (by decide) (by decide) with h100 | h100
            · rcases m.htr 1 2 4 (by decide) (by decide) with h101 | h101
              · rcases m.htr 1 3 4 (by decide) (by decide) with h102 | h102
                · rcases m.htr 1 3 5 (by decide) (by decide) with h103 | h103
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h104 | h104
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h105 | h105
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h106 | h106
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h107 | h107
                          · rcases h4bigk with h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [hlam, p108_0]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [hc14, hlam, hphi, p108_1, u4elo0]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [hlam, hphi, ht23, ht34, p108_1, u2ehi3, u4elo0]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [h107, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p108_1, u4elo0]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              rcases p108_3 (m.d 0 4) (by simp) with h113 | h113
                              · rcases p108_3 (m.d 1 4) (by simp) with h114 | h114
                                · rcases p108_3 (m.d 2 4) (by simp) with h115 | h115
                                  · linarith only [h115, h97, hlam]
                                  · linarith only [h106, h115, hlam]
                                · linarith only [h104, h114, hlam]
                              · linarith only [h113, hlam, p108_0]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [hc04, hlam, hphi, p108_1, u4elo1]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [hlam, p108_0]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [h106, hlam, hphi, ht23, ht34, p108_1, u2ehi4, u4elo1]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [h107, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p108_1, u4elo1]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              rcases p108_3 (m.d 0 4) (by simp) with h124 | h124
                              · rcases p108_3 (m.d 1 4) (by simp) with h125 | h125
                                · rcases p108_3 (m.d 2 4) (by simp) with h126 | h126
                                  · linarith only [h101, h126, hlam]
                                  · linarith only [h106, h126, hlam]
                                · linarith only [h125, hlam, p108_0]
                              · linarith only [h124, h99, hlam]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [h97, hlam, p108_0]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [h101, hlam, p108_0]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [hlam, p108_0]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [h107, h97, hc02, hc45, hlam, hphi, ht0b, ht5b, p108_1]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              rcases p108_3 (m.d 0 4) (by simp) with h135 | h135
                              · rcases p108_3 (m.d 1 4) (by simp) with h136 | h136
                                · rcases p108_3 (m.d 2 4) (by simp) with h137 | h137
                                  · rcases p108_3 (m.d 3 4) (by simp) with h138 | h138
                                    · linarith only [h105, h138, hlam]
                                    · linarith only [h107, h138, hlam]
                                  · linarith only [h137, hlam, p108_0]
                                · linarith only [h104, h136, hlam]
                              · linarith only [h135, h99, hlam]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [hc04, hlam, hphi, p108_1, u4elo3]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [h102, hlam, p108_0]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [h105, hlam, p108_0]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [hlam, p108_0]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [h100, h105, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p108_1]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [h99, hlam, p108_0]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [h104, hlam, p108_0]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [h106, hlam, p108_0]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [h107, hlam, p108_0]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [hlam, p108_0]
                          · linarith only [h107, h99, hc34, hlam, hphi, u4elo0]
                        · linarith only [h106, h99, hc24, hlam, hphi, u4elo0]
                      · linarith only [h105, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
                    · linarith only [h101, h104, h99, hlam, hphi, ht23, ht34, u2ehi3, u4elo0]
                  · linarith only [h102, h103, hc34, hlam, hphi, ht45, u5elo3]
                · linarith only [h100, h102, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
              · linarith only [h0, h101, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]
            · linarith only [h0, h100, h97, hc23, hlam, hphi, u2ehi3]
          · linarith only [h97, h99, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
        · linarith only [h97, h98, hc25, hlam, hphi, u2ehi3]
      · linarith only [h97, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]

theorem n7l_sAB2_M_LI_M_LR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4elo := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h2elo := hb2.1
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5 | h5
            · linarith only [h2, h5, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi8]
            · linarith only [h4, h5, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h8 | h8
            · linarith only [h4, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi8]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
              · linarith only [h0, h10, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi9]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h12 | h12
                · linarith only [h10, h12, hc24, hlam, hphi, u4elo3]
                · linarith only [h12, h4, hc23, hlam, hphi, ht34, u4elo4]
        · linarith only [h1, h3, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h16 | h16
        · linarith only [h16, h2, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi7]
        · linarith only [h1, h16, hc12, hlam, hphi, u2elo0]
    · linarith only [h0, h1, hc24, hlam, hphi, ht45, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h20 | h20
    · linarith only [h0, h20, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi7]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h22 | h22
      · rcases m.htr 1 2 5 (by decide) (by decide) with h23 | h23
        · linarith only [h20, h23, hc02, hlam, hphi, u2elo1]
        · linarith only [h22, h23, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h26 | h26
        · linarith only [h20, h22, h26, hc02, hlam, hphi, u2elo2]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h28 | h28
          · rcases m.htr 2 3 5 (by decide) (by decide) with h29 | h29
            · rcases m.htr 2 4 5 (by decide) (by decide) with h30 | h30
              · rcases m.htr 3 4 5 (by decide) (by decide) with h31 | h31
                · linarith only [h28, h31, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi9]
                · linarith only [h30, h31, hc34, hlam, hphi, u4elo2]
              · linarith only [h0, h30, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
            · linarith only [h22, h29, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
          · linarith only [h22, h28, hc12, hlam, hphi, ht23, ht34, u4elo3]

theorem n7l_sAB2_M_LI_M_LR_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases h4bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u4elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, p0_1, u4elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, p0_1, u4elo0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo0, u5ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, p0_1, u4elo1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo1, u5ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u4elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u4elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, p0_1, u4elo2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo2, u5ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u4elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, p0_1, u4elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, p0_1, u4elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p0_1, u4elo3, u5ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, p0_1, u4elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht45, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht45, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht45, p0_1, u5elo4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAB2_M_LI_M_LR_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4elo := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h2ehi := hb2.1
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 3 4 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h2, h4, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
          · linarith only [h1, h3, h4, hc34, hlam, hphi, u4elo1]
        · linarith only [h3, hlam, hphi, ht23, ht34, ht45, u2ehi3, u5elo4]
      · linarith only [h2, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
    · linarith only [h1, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
    · linarith only [h0, h10, hc23, hlam, hphi, u2ehi3]
    · linarith only [h10, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]

theorem n7l_sAB2_M_LR_H_I_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi8 := h4ehi (m.d 3 4) (by simp)
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u4ehi9, u4elo3]
  · linarith only [h0, hlam, hphi, u4ehi8, u4elo4]

theorem n7l_sAB2_M_LR_H_I_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi8 := h4ehi (m.d 3 4) (by simp)
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u4ehi9, u4elo3]
  · linarith only [h0, hlam, hphi, u4ehi8, u4elo4]

theorem n7l_sAB2_M_LR_H_I_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi8 := h4ehi (m.d 3 4) (by simp)
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u4ehi9, u4elo3]
  · linarith only [h0, hlam, hphi, u4ehi8, u4elo4]

theorem n7l_sAB2_M_LR_H_L_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.2.1
  have h5elo := hb5.1
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi9, u5elo4]

theorem n7l_sAB2_M_LR_H_L_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.2.1
  have h5elo := hb5.1
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi9, u5elo4]

theorem n7l_sAB2_M_LR_H_L_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.2.1
  have h5elo := hb5.1
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi9, u5elo4]

theorem n7l_sAB2_M_LR_H_R_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have h5ehi := hb5.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi8 := h4ehi (m.d 3 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi4]
  · linarith only [h0, hlam, hphi, u4ehi8, u4elo4]

theorem n7l_sAB2_M_LR_H_R_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have h5ehi := hb5.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi5 := h4ehi (m.d 0 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0, u5ehi4]
  · linarith only [h0, hlam, hphi, u4ehi5, u4elo4]

theorem n7l_sAB2_M_LR_H_R_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have h5ehi := hb5.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi8 := h4ehi (m.d 3 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi4]
  · linarith only [h0, hlam, hphi, u4ehi8, u4elo4]

theorem n7l_sAB2_M_LR_M_IR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi8 := h4ehi (m.d 3 4) (by simp)
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u4ehi9, u4elo3]
  · linarith only [h0, hlam, hphi, u4ehi8, u4elo4]

theorem n7l_sAB2_M_LR_M_IR_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi7 := h4ehi (m.d 2 4) (by simp)
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 2 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u4ehi9, u4elo2]
  · linarith only [h0, hlam, hphi, u4ehi7, u4elo4]

theorem n7l_sAB2_M_LR_M_IR_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi8 := h4ehi (m.d 3 4) (by simp)
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u4ehi9, u4elo3]
  · linarith only [h0, hlam, hphi, u4ehi8, u4elo4]

theorem n7l_sAB2_M_LR_M_LI_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi8 := h4ehi (m.d 3 4) (by simp)
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u4ehi9, u4elo3]
  · linarith only [h0, hlam, hphi, u4ehi8, u4elo4]

theorem n7l_sAB2_M_LR_M_LI_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi8 := h4ehi (m.d 3 4) (by simp)
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u4ehi9, u4elo3]
  · linarith only [h0, hlam, hphi, u4ehi8, u4elo4]

theorem n7l_sAB2_M_LR_M_LI_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi8 := h4ehi (m.d 3 4) (by simp)
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u4ehi9, u4elo3]
  · linarith only [h0, hlam, hphi, u4ehi8, u4elo4]

theorem n7l_sAB2_M_LR_M_LR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi8 := h4ehi (m.d 3 4) (by simp)
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u4ehi9, u4elo3]
  · linarith only [h0, hlam, hphi, u4ehi8, u4elo4]

theorem n7l_sAB2_M_LR_M_LR_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi8 := h4ehi (m.d 3 4) (by simp)
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u4ehi9, u4elo3]
  · linarith only [h0, hlam, hphi, u4ehi8, u4elo4]

theorem n7l_sAB2_M_LR_M_LR_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have h4elo := hb4.1
  have h4ehi := hb4.2.2.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u4ehi8 := h4ehi (m.d 3 4) (by simp)
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 3 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, u4ehi9, u4elo3]
  · linarith only [h0, hlam, hphi, u4ehi8, u4elo4]

end R2N4
