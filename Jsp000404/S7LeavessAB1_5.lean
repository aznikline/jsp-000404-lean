import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem n7l_sAB1_H_I_H_L_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h1ehi := hb1.1
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  linarith only [hlam, hphi, ht12, ht23, ht34, ht45, u1ehi4, u5elo1]

theorem n7l_sAB1_H_I_H_R_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h5ehi := hb5.1
  have h1elo := hb1.1
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
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
        · rcases p0_3 (m.d 3 4) (by simp) with h13 | h13
          · rcases p0_3 (m.d 4 5) (by simp) with h14 | h14
            · linarith only [h14, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h14, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h17 | h17
            · linarith only [h17, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h17, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h21 | h21
    · rcases p0_3 (m.d 1 4) (by simp) with h22 | h22
      · linarith only [h22, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h24 | h24
        · linarith only [h24, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h26 | h26
          · rcases p0_3 (m.d 4 5) (by simp) with h27 | h27
            · linarith only [h27, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h27, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h30 | h30
            · linarith only [h22, h30, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h30, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h21, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h34 | h34
    · rcases p0_3 (m.d 1 4) (by simp) with h35 | h35
      · linarith only [h35, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h37 | h37
        · rcases p0_3 (m.d 3 4) (by simp) with h38 | h38
          · linarith only [h38, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h40 | h40
            · linarith only [h40, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h40, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h43 | h43
          · linarith only [h43, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h45 | h45
            · linarith only [h35, h45, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h45, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h34, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo3, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h55 | h55
    · linarith only [h55, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h57 | h57
      · linarith only [h57, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h59 | h59
        · rcases p0_3 (m.d 3 4) (by simp) with h60 | h60
          · rcases p0_3 (m.d 4 5) (by simp) with h61 | h61
            · linarith only [h61, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h61, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h64 | h64
            · linarith only [h64, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h64, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h59, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h68 | h68
    · rcases p0_3 (m.d 1 4) (by simp) with h69 | h69
      · linarith only [h69, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h71 | h71
        · rcases p0_3 (m.d 3 4) (by simp) with h72 | h72
          · rcases p0_3 (m.d 4 5) (by simp) with h73 | h73
            · linarith only [h73, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h68, h73, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h76 | h76
            · linarith only [h76, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h76, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h71, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h80 | h80
      · linarith only [h80, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h82 | h82
        · rcases p0_3 (m.d 3 4) (by simp) with h83 | h83
          · rcases p0_3 (m.d 4 5) (by simp) with h84 | h84
            · linarith only [h68, h84, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h84, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h87 | h87
            · linarith only [h68, h87, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h87, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h82, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h92 | h92
    · rcases p0_3 (m.d 1 4) (by simp) with h93 | h93
      · linarith only [h93, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h95 | h95
        · rcases p0_3 (m.d 3 4) (by simp) with h96 | h96
          · linarith only [h96, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h98 | h98
            · linarith only [h98, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h92, h98, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h95, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h102 | h102
      · linarith only [h102, h92, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h104 | h104
        · rcases p0_3 (m.d 3 4) (by simp) with h105 | h105
          · linarith only [h105, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h107 | h107
            · linarith only [h107, h92, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h107, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h104, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h112 | h112
    · linarith only [h112, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h114 | h114
      · linarith only [h114, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h116 | h116
        · rcases p0_3 (m.d 3 4) (by simp) with h117 | h117
          · rcases p0_3 (m.d 4 5) (by simp) with h118 | h118
            · linarith only [h118, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h118, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h117, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h122 | h122
          · rcases p0_3 (m.d 4 5) (by simp) with h123 | h123
            · linarith only [h123, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h123, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h122, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h127 | h127
    · rcases p0_3 (m.d 1 4) (by simp) with h128 | h128
      · linarith only [h128, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h130 | h130
        · rcases p0_3 (m.d 3 4) (by simp) with h131 | h131
          · rcases p0_3 (m.d 4 5) (by simp) with h132 | h132
            · linarith only [h132, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h127, h132, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h131, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h136 | h136
          · rcases p0_3 (m.d 4 5) (by simp) with h137 | h137
            · linarith only [h137, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h137, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h136, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h141 | h141
      · linarith only [h141, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h143 | h143
        · rcases p0_3 (m.d 3 4) (by simp) with h144 | h144
          · rcases p0_3 (m.d 4 5) (by simp) with h145 | h145
            · linarith only [h127, h145, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h143, h145, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h144, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h149 | h149
          · rcases p0_3 (m.d 4 5) (by simp) with h150 | h150
            · linarith only [h127, h150, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h150, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h149, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h154 | h154
    · rcases p0_3 (m.d 1 4) (by simp) with h155 | h155
      · linarith only [h155, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h157 | h157
        · linarith only [h157, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h159 | h159
          · rcases p0_3 (m.d 4 5) (by simp) with h160 | h160
            · linarith only [h160, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h154, h160, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h159, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h164 | h164
      · linarith only [h154, h164, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h166 | h166
        · linarith only [h166, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h168 | h168
          · rcases p0_3 (m.d 4 5) (by simp) with h169 | h169
            · linarith only [h154, h169, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h169, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h168, hlam, p0_0]
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

theorem n7l_sAB1_H_I_H_R_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h5ehi := hb5.1
  have h1ehi := hb1.1
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
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
    linarith only [hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h3 | h3
    · rcases p0_3 (m.d 1 4) (by simp) with h4 | h4
      · rcases p0_3 (m.d 2 4) (by simp) with h5 | h5
        · linarith only [h5, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h7 | h7
          · rcases p0_3 (m.d 4 5) (by simp) with h8 | h8
            · linarith only [h8, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h8, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h11 | h11
            · linarith only [h11, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h11, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h4, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi3]
    · linarith only [h3, hlam, p0_0]
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
        · rcases p0_3 (m.d 3 4) (by simp) with h24 | h24
          · linarith only [h24, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h26 | h26
            · linarith only [h18, h26, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h26, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h17, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi3]
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
    rcases p0_3 (m.d 0 4) (by simp) with h32 | h32
    · linarith only [h32, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h34 | h34
      · rcases p0_3 (m.d 2 4) (by simp) with h35 | h35
        · rcases p0_3 (m.d 3 4) (by simp) with h36 | h36
          · rcases p0_3 (m.d 4 5) (by simp) with h37 | h37
            · linarith only [h37, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h37, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h40 | h40
            · linarith only [h40, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h40, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h43 | h43
          · rcases p0_3 (m.d 4 5) (by simp) with h44 | h44
            · linarith only [h44, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h44, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h47 | h47
            · linarith only [h47, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h47, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h34, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h52 | h52
    · rcases p0_3 (m.d 1 4) (by simp) with h53 | h53
      · rcases p0_3 (m.d 2 4) (by simp) with h54 | h54
        · linarith only [h54, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h56 | h56
          · rcases p0_3 (m.d 4 5) (by simp) with h57 | h57
            · linarith only [h57, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h52, h57, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h60 | h60
            · linarith only [h60, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h60, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h53, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h64 | h64
      · rcases p0_3 (m.d 2 4) (by simp) with h65 | h65
        · linarith only [h65, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h67 | h67
          · rcases p0_3 (m.d 4 5) (by simp) with h68 | h68
            · linarith only [h52, h68, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h68, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h71 | h71
            · linarith only [h52, h71, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h71, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h64, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h75 | h75
    · rcases p0_3 (m.d 1 4) (by simp) with h76 | h76
      · rcases p0_3 (m.d 2 4) (by simp) with h77 | h77
        · rcases p0_3 (m.d 3 4) (by simp) with h78 | h78
          · linarith only [h78, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h80 | h80
            · linarith only [h80, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h75, h80, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h83 | h83
          · linarith only [h83, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h85 | h85
            · linarith only [h77, h85, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h85, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h76, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h89 | h89
      · rcases p0_3 (m.d 2 4) (by simp) with h90 | h90
        · rcases p0_3 (m.d 3 4) (by simp) with h91 | h91
          · linarith only [h91, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h93 | h93
            · linarith only [h75, h93, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h93, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h96 | h96
          · linarith only [h96, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h98 | h98
            · linarith only [h75, h98, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h98, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h89, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h103 | h103
    · linarith only [h103, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h105 | h105
      · rcases p0_3 (m.d 2 4) (by simp) with h106 | h106
        · rcases p0_3 (m.d 3 4) (by simp) with h107 | h107
          · rcases p0_3 (m.d 4 5) (by simp) with h108 | h108
            · linarith only [h108, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h108, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h111 | h111
            · linarith only [h111, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h111, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h106, hlam, p0_0]
      · linarith only [h105, hc24, hlam, hphi, ht12, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht12, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h118 | h118
    · rcases p0_3 (m.d 1 4) (by simp) with h119 | h119
      · rcases p0_3 (m.d 2 4) (by simp) with h120 | h120
        · rcases p0_3 (m.d 3 4) (by simp) with h121 | h121
          · linarith only [h121, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h123 | h123
            · linarith only [h123, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h118, h123, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h120, hlam, p0_0]
      · linarith only [h119, hc24, hlam, hphi, ht12, p0_1, u1ehi3]
    · rcases p0_3 (m.d 1 4) (by simp) with h128 | h128
      · rcases p0_3 (m.d 2 4) (by simp) with h129 | h129
        · rcases p0_3 (m.d 3 4) (by simp) with h130 | h130
          · linarith only [h130, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h132 | h132
            · linarith only [h118, h132, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h128, h132, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h129, hlam, p0_0]
      · linarith only [h128, hc24, hlam, hphi, ht12, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h138 | h138
    · linarith only [h138, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h140 | h140
      · rcases p0_3 (m.d 2 4) (by simp) with h141 | h141
        · rcases p0_3 (m.d 3 4) (by simp) with h142 | h142
          · rcases p0_3 (m.d 4 5) (by simp) with h143 | h143
            · linarith only [h143, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h140, h143, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h142, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h147 | h147
          · rcases p0_3 (m.d 4 5) (by simp) with h148 | h148
            · linarith only [h148, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h148, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h147, hlam, p0_0]
      · linarith only [h140, hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h154 | h154
    · rcases p0_3 (m.d 1 4) (by simp) with h155 | h155
      · rcases p0_3 (m.d 2 4) (by simp) with h156 | h156
        · linarith only [h156, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h158 | h158
          · rcases p0_3 (m.d 4 5) (by simp) with h159 | h159
            · linarith only [h159, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h154, h159, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h158, hlam, p0_0]
      · linarith only [h155, hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi3]
    · rcases p0_3 (m.d 1 4) (by simp) with h164 | h164
      · rcases p0_3 (m.d 2 4) (by simp) with h165 | h165
        · linarith only [h165, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h167 | h167
          · rcases p0_3 (m.d 4 5) (by simp) with h168 | h168
            · linarith only [h154, h168, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h164, h168, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h167, hlam, p0_0]
      · linarith only [h164, hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi3]
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
    linarith only [hc45, hlam, hphi, ht12, ht23, ht34, p0_1, u1ehi3]
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

theorem n7l_sAB1_H_I_M_IR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h1elo := hb1.1
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
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
        · rcases p0_3 (m.d 3 4) (by simp) with h13 | h13
          · rcases p0_3 (m.d 4 5) (by simp) with h14 | h14
            · linarith only [h14, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h14, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h17 | h17
            · linarith only [h17, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h17, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h21 | h21
    · rcases p0_3 (m.d 1 4) (by simp) with h22 | h22
      · linarith only [h22, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h24 | h24
        · linarith only [h24, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h26 | h26
          · rcases p0_3 (m.d 4 5) (by simp) with h27 | h27
            · linarith only [h27, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h27, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h30 | h30
            · linarith only [h22, h30, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h30, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h21, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h34 | h34
    · rcases p0_3 (m.d 1 4) (by simp) with h35 | h35
      · linarith only [h35, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h37 | h37
        · rcases p0_3 (m.d 3 4) (by simp) with h38 | h38
          · linarith only [h38, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h40 | h40
            · linarith only [h40, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h40, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h43 | h43
          · linarith only [h43, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h45 | h45
            · linarith only [h35, h45, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h45, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h34, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo3, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h55 | h55
    · linarith only [h55, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h57 | h57
      · linarith only [h57, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h59 | h59
        · rcases p0_3 (m.d 3 4) (by simp) with h60 | h60
          · rcases p0_3 (m.d 4 5) (by simp) with h61 | h61
            · linarith only [h61, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h61, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h64 | h64
            · linarith only [h64, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h64, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h59, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h68 | h68
    · rcases p0_3 (m.d 1 4) (by simp) with h69 | h69
      · linarith only [h69, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h71 | h71
        · rcases p0_3 (m.d 3 4) (by simp) with h72 | h72
          · rcases p0_3 (m.d 4 5) (by simp) with h73 | h73
            · linarith only [h73, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h68, h73, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h76 | h76
            · linarith only [h76, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h76, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h71, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h80 | h80
      · linarith only [h80, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h82 | h82
        · rcases p0_3 (m.d 3 4) (by simp) with h83 | h83
          · rcases p0_3 (m.d 4 5) (by simp) with h84 | h84
            · linarith only [h68, h84, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h84, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h87 | h87
            · linarith only [h68, h87, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h87, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h82, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h92 | h92
    · rcases p0_3 (m.d 1 4) (by simp) with h93 | h93
      · linarith only [h93, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h95 | h95
        · rcases p0_3 (m.d 3 4) (by simp) with h96 | h96
          · linarith only [h96, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h98 | h98
            · linarith only [h98, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h92, h98, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h95, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h102 | h102
      · linarith only [h102, h92, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h104 | h104
        · rcases p0_3 (m.d 3 4) (by simp) with h105 | h105
          · linarith only [h105, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h107 | h107
            · linarith only [h107, h92, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h107, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h104, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h112 | h112
    · linarith only [h112, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h114 | h114
      · linarith only [h114, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h116 | h116
        · rcases p0_3 (m.d 3 4) (by simp) with h117 | h117
          · rcases p0_3 (m.d 4 5) (by simp) with h118 | h118
            · linarith only [h118, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h118, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h117, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h122 | h122
          · rcases p0_3 (m.d 4 5) (by simp) with h123 | h123
            · linarith only [h123, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h123, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h122, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h127 | h127
    · rcases p0_3 (m.d 1 4) (by simp) with h128 | h128
      · linarith only [h128, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h130 | h130
        · rcases p0_3 (m.d 3 4) (by simp) with h131 | h131
          · rcases p0_3 (m.d 4 5) (by simp) with h132 | h132
            · linarith only [h132, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h127, h132, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h131, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h136 | h136
          · rcases p0_3 (m.d 4 5) (by simp) with h137 | h137
            · linarith only [h137, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h137, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h136, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h141 | h141
      · linarith only [h141, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h143 | h143
        · rcases p0_3 (m.d 3 4) (by simp) with h144 | h144
          · rcases p0_3 (m.d 4 5) (by simp) with h145 | h145
            · linarith only [h127, h145, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h143, h145, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h144, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h149 | h149
          · rcases p0_3 (m.d 4 5) (by simp) with h150 | h150
            · linarith only [h127, h150, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h150, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h149, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h154 | h154
    · rcases p0_3 (m.d 1 4) (by simp) with h155 | h155
      · linarith only [h155, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h157 | h157
        · linarith only [h157, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h159 | h159
          · rcases p0_3 (m.d 4 5) (by simp) with h160 | h160
            · linarith only [h160, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h154, h160, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h159, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h164 | h164
      · linarith only [h154, h164, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h166 | h166
        · linarith only [h166, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h168 | h168
          · rcases p0_3 (m.d 4 5) (by simp) with h169 | h169
            · linarith only [h154, h169, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h169, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h168, hlam, p0_0]
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

theorem n7l_sAB1_H_I_M_IR_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
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
        · rcases p0_3 (m.d 3 4) (by simp) with h13 | h13
          · rcases p0_3 (m.d 4 5) (by simp) with h14 | h14
            · linarith only [h14, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h14, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h17 | h17
            · linarith only [h17, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h17, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h21 | h21
    · rcases p0_3 (m.d 1 4) (by simp) with h22 | h22
      · rcases p0_3 (m.d 2 4) (by simp) with h23 | h23
        · linarith only [h23, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h25 | h25
          · rcases p0_3 (m.d 4 5) (by simp) with h26 | h26
            · linarith only [h26, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h26, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h29 | h29
            · linarith only [h29, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h29, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · rcases p0_3 (m.d 2 4) (by simp) with h32 | h32
        · linarith only [h32, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h34 | h34
          · rcases p0_3 (m.d 4 5) (by simp) with h35 | h35
            · linarith only [h22, h35, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h35, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h38 | h38
            · linarith only [h22, h38, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h38, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h21, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h42 | h42
    · rcases p0_3 (m.d 1 4) (by simp) with h43 | h43
      · rcases p0_3 (m.d 2 4) (by simp) with h44 | h44
        · rcases p0_3 (m.d 3 4) (by simp) with h45 | h45
          · linarith only [h45, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h47 | h47
            · linarith only [h47, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h47, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h50 | h50
          · linarith only [h50, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h52 | h52
            · linarith only [h44, h52, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h52, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · rcases p0_3 (m.d 2 4) (by simp) with h55 | h55
        · rcases p0_3 (m.d 3 4) (by simp) with h56 | h56
          · linarith only [h56, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h58 | h58
            · linarith only [h43, h58, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h58, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h61 | h61
          · linarith only [h61, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h63 | h63
            · linarith only [h43, h63, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h63, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h42, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h68 | h68
    · linarith only [h68, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h70 | h70
      · rcases p0_3 (m.d 2 4) (by simp) with h71 | h71
        · rcases p0_3 (m.d 3 4) (by simp) with h72 | h72
          · rcases p0_3 (m.d 4 5) (by simp) with h73 | h73
            · linarith only [h73, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h73, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h76 | h76
            · linarith only [h76, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h76, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h79 | h79
          · rcases p0_3 (m.d 4 5) (by simp) with h80 | h80
            · linarith only [h80, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h80, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h83 | h83
            · linarith only [h83, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h83, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h70, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h88 | h88
    · rcases p0_3 (m.d 1 4) (by simp) with h89 | h89
      · rcases p0_3 (m.d 2 4) (by simp) with h90 | h90
        · linarith only [h90, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h92 | h92
          · rcases p0_3 (m.d 4 5) (by simp) with h93 | h93
            · linarith only [h93, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h88, h93, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h96 | h96
            · linarith only [h96, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h96, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h89, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h100 | h100
      · rcases p0_3 (m.d 2 4) (by simp) with h101 | h101
        · linarith only [h101, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h103 | h103
          · rcases p0_3 (m.d 4 5) (by simp) with h104 | h104
            · linarith only [h104, h88, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h104, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h107 | h107
            · linarith only [h107, h88, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h107, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h100, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h111 | h111
    · rcases p0_3 (m.d 1 4) (by simp) with h112 | h112
      · rcases p0_3 (m.d 2 4) (by simp) with h113 | h113
        · rcases p0_3 (m.d 3 4) (by simp) with h114 | h114
          · linarith only [h114, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h116 | h116
            · linarith only [h116, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h111, h116, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h119 | h119
          · linarith only [h119, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h121 | h121
            · linarith only [h113, h121, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h121, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h112, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h125 | h125
      · rcases p0_3 (m.d 2 4) (by simp) with h126 | h126
        · rcases p0_3 (m.d 3 4) (by simp) with h127 | h127
          · linarith only [h127, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h129 | h129
            · linarith only [h111, h129, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h129, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h132 | h132
          · linarith only [h132, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h134 | h134
            · linarith only [h111, h134, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h134, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h125, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h139 | h139
    · linarith only [h139, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h141 | h141
      · rcases p0_3 (m.d 2 4) (by simp) with h142 | h142
        · rcases p0_3 (m.d 3 4) (by simp) with h143 | h143
          · rcases p0_3 (m.d 4 5) (by simp) with h144 | h144
            · linarith only [h144, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h144, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h147 | h147
            · linarith only [h147, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h147, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h142, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h151 | h151
        · rcases p0_3 (m.d 3 4) (by simp) with h152 | h152
          · rcases p0_3 (m.d 4 5) (by simp) with h153 | h153
            · linarith only [h153, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h153, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h156 | h156
            · linarith only [h156, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h156, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h151, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h160 | h160
    · rcases p0_3 (m.d 1 4) (by simp) with h161 | h161
      · linarith only [h161, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h163 | h163
        · rcases p0_3 (m.d 3 4) (by simp) with h164 | h164
          · rcases p0_3 (m.d 4 5) (by simp) with h165 | h165
            · linarith only [h165, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h160, h165, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h168 | h168
            · linarith only [h168, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h168, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h163, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h172 | h172
      · linarith only [h172, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h174 | h174
        · rcases p0_3 (m.d 3 4) (by simp) with h175 | h175
          · rcases p0_3 (m.d 4 5) (by simp) with h176 | h176
            · linarith only [h160, h176, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h176, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h179 | h179
            · linarith only [h160, h179, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h179, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h174, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h184 | h184
    · rcases p0_3 (m.d 1 4) (by simp) with h185 | h185
      · rcases p0_3 (m.d 2 4) (by simp) with h186 | h186
        · rcases p0_3 (m.d 3 4) (by simp) with h187 | h187
          · linarith only [h187, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h189 | h189
            · linarith only [h189, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h184, h189, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h186, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h193 | h193
        · rcases p0_3 (m.d 3 4) (by simp) with h194 | h194
          · linarith only [h194, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h196 | h196
            · linarith only [h185, h196, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h196, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h193, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h200 | h200
      · rcases p0_3 (m.d 2 4) (by simp) with h201 | h201
        · rcases p0_3 (m.d 3 4) (by simp) with h202 | h202
          · linarith only [h202, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h204 | h204
            · linarith only [h184, h204, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h200, h204, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h201, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h208 | h208
        · rcases p0_3 (m.d 3 4) (by simp) with h209 | h209
          · linarith only [h209, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h211 | h211
            · linarith only [h184, h211, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h211, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h208, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h216 | h216
    · linarith only [h216, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h218 | h218
      · rcases p0_3 (m.d 2 4) (by simp) with h219 | h219
        · rcases p0_3 (m.d 3 4) (by simp) with h220 | h220
          · rcases p0_3 (m.d 4 5) (by simp) with h221 | h221
            · linarith only [h221, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h218, h221, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h220, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h225 | h225
          · rcases p0_3 (m.d 4 5) (by simp) with h226 | h226
            · linarith only [h226, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h226, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h225, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h230 | h230
        · rcases p0_3 (m.d 3 4) (by simp) with h231 | h231
          · rcases p0_3 (m.d 4 5) (by simp) with h232 | h232
            · linarith only [h232, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h230, h232, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h231, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h236 | h236
          · rcases p0_3 (m.d 4 5) (by simp) with h237 | h237
            · linarith only [h237, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h237, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h236, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h241 | h241
    · rcases p0_3 (m.d 1 4) (by simp) with h242 | h242
      · linarith only [h242, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h244 | h244
        · rcases p0_3 (m.d 3 4) (by simp) with h245 | h245
          · rcases p0_3 (m.d 4 5) (by simp) with h246 | h246
            · linarith only [h246, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h241, h246, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h245, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h250 | h250
          · rcases p0_3 (m.d 4 5) (by simp) with h251 | h251
            · linarith only [h251, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h251, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h250, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h255 | h255
      · linarith only [h255, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h257 | h257
        · rcases p0_3 (m.d 3 4) (by simp) with h258 | h258
          · rcases p0_3 (m.d 4 5) (by simp) with h259 | h259
            · linarith only [h241, h259, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h257, h259, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h258, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h263 | h263
          · rcases p0_3 (m.d 4 5) (by simp) with h264 | h264
            · linarith only [h241, h264, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h264, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h263, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h268 | h268
    · rcases p0_3 (m.d 1 4) (by simp) with h269 | h269
      · rcases p0_3 (m.d 2 4) (by simp) with h270 | h270
        · linarith only [h270, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h272 | h272
          · rcases p0_3 (m.d 4 5) (by simp) with h273 | h273
            · linarith only [h273, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h268, h273, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h272, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h277 | h277
        · linarith only [h277, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h279 | h279
          · rcases p0_3 (m.d 4 5) (by simp) with h280 | h280
            · linarith only [h269, h280, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h280, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h279, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h284 | h284
      · rcases p0_3 (m.d 2 4) (by simp) with h285 | h285
        · linarith only [h285, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h287 | h287
          · rcases p0_3 (m.d 4 5) (by simp) with h288 | h288
            · linarith only [h268, h288, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h284, h288, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h287, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h292 | h292
        · linarith only [h292, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h294 | h294
          · rcases p0_3 (m.d 4 5) (by simp) with h295 | h295
            · linarith only [h268, h295, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h295, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h294, hlam, p0_0]
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

theorem n7l_sAB1_H_I_M_IR_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h1ehi := hb1.1
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
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
    linarith only [hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h3 | h3
    · rcases p0_3 (m.d 1 4) (by simp) with h4 | h4
      · rcases p0_3 (m.d 2 4) (by simp) with h5 | h5
        · linarith only [h5, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h7 | h7
          · rcases p0_3 (m.d 4 5) (by simp) with h8 | h8
            · linarith only [h8, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h8, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h11 | h11
            · linarith only [h11, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h11, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h4, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi3]
    · linarith only [h3, hlam, p0_0]
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
        · rcases p0_3 (m.d 3 4) (by simp) with h24 | h24
          · linarith only [h24, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h26 | h26
            · linarith only [h18, h26, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h26, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h17, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi3]
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
    rcases p0_3 (m.d 0 4) (by simp) with h32 | h32
    · linarith only [h32, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h34 | h34
      · rcases p0_3 (m.d 2 4) (by simp) with h35 | h35
        · rcases p0_3 (m.d 3 4) (by simp) with h36 | h36
          · rcases p0_3 (m.d 4 5) (by simp) with h37 | h37
            · linarith only [h37, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h37, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h40 | h40
            · linarith only [h40, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h40, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h43 | h43
          · rcases p0_3 (m.d 4 5) (by simp) with h44 | h44
            · linarith only [h44, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h44, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h47 | h47
            · linarith only [h47, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h47, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h34, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h52 | h52
    · rcases p0_3 (m.d 1 4) (by simp) with h53 | h53
      · rcases p0_3 (m.d 2 4) (by simp) with h54 | h54
        · linarith only [h54, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h56 | h56
          · rcases p0_3 (m.d 4 5) (by simp) with h57 | h57
            · linarith only [h57, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h52, h57, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h60 | h60
            · linarith only [h60, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h60, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h53, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h64 | h64
      · rcases p0_3 (m.d 2 4) (by simp) with h65 | h65
        · linarith only [h65, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h67 | h67
          · rcases p0_3 (m.d 4 5) (by simp) with h68 | h68
            · linarith only [h52, h68, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h68, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h71 | h71
            · linarith only [h52, h71, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h71, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h64, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h75 | h75
    · rcases p0_3 (m.d 1 4) (by simp) with h76 | h76
      · rcases p0_3 (m.d 2 4) (by simp) with h77 | h77
        · rcases p0_3 (m.d 3 4) (by simp) with h78 | h78
          · linarith only [h78, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h80 | h80
            · linarith only [h80, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h75, h80, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h83 | h83
          · linarith only [h83, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h85 | h85
            · linarith only [h77, h85, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h85, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h76, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h89 | h89
      · rcases p0_3 (m.d 2 4) (by simp) with h90 | h90
        · rcases p0_3 (m.d 3 4) (by simp) with h91 | h91
          · linarith only [h91, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h93 | h93
            · linarith only [h75, h93, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h93, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h96 | h96
          · linarith only [h96, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h98 | h98
            · linarith only [h75, h98, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h98, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h89, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h103 | h103
    · linarith only [h103, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h105 | h105
      · rcases p0_3 (m.d 2 4) (by simp) with h106 | h106
        · rcases p0_3 (m.d 3 4) (by simp) with h107 | h107
          · rcases p0_3 (m.d 4 5) (by simp) with h108 | h108
            · linarith only [h108, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h108, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h111 | h111
            · linarith only [h111, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h111, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h106, hlam, p0_0]
      · linarith only [h105, hc24, hlam, hphi, ht12, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht12, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h118 | h118
    · rcases p0_3 (m.d 1 4) (by simp) with h119 | h119
      · rcases p0_3 (m.d 2 4) (by simp) with h120 | h120
        · rcases p0_3 (m.d 3 4) (by simp) with h121 | h121
          · linarith only [h121, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h123 | h123
            · linarith only [h123, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h118, h123, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h120, hlam, p0_0]
      · linarith only [h119, hc24, hlam, hphi, ht12, p0_1, u1ehi3]
    · rcases p0_3 (m.d 1 4) (by simp) with h128 | h128
      · rcases p0_3 (m.d 2 4) (by simp) with h129 | h129
        · rcases p0_3 (m.d 3 4) (by simp) with h130 | h130
          · linarith only [h130, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h132 | h132
            · linarith only [h118, h132, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h128, h132, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h129, hlam, p0_0]
      · linarith only [h128, hc24, hlam, hphi, ht12, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h138 | h138
    · linarith only [h138, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h140 | h140
      · rcases p0_3 (m.d 2 4) (by simp) with h141 | h141
        · rcases p0_3 (m.d 3 4) (by simp) with h142 | h142
          · rcases p0_3 (m.d 4 5) (by simp) with h143 | h143
            · linarith only [h143, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h140, h143, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h142, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h147 | h147
          · rcases p0_3 (m.d 4 5) (by simp) with h148 | h148
            · linarith only [h148, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h148, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h147, hlam, p0_0]
      · linarith only [h140, hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h154 | h154
    · rcases p0_3 (m.d 1 4) (by simp) with h155 | h155
      · rcases p0_3 (m.d 2 4) (by simp) with h156 | h156
        · linarith only [h156, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h158 | h158
          · rcases p0_3 (m.d 4 5) (by simp) with h159 | h159
            · linarith only [h159, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h154, h159, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h158, hlam, p0_0]
      · linarith only [h155, hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi3]
    · rcases p0_3 (m.d 1 4) (by simp) with h164 | h164
      · rcases p0_3 (m.d 2 4) (by simp) with h165 | h165
        · linarith only [h165, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h167 | h167
          · rcases p0_3 (m.d 4 5) (by simp) with h168 | h168
            · linarith only [h154, h168, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h164, h168, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h167, hlam, p0_0]
      · linarith only [h164, hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi3]
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
    linarith only [hc45, hlam, hphi, ht12, ht23, ht34, p0_1, u1ehi3]
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

theorem n7l_sAB1_H_I_M_LI_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAB1_H_I_M_LI_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have h1ehi := hb1.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
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
    linarith only [hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u1ehi4, u5elo3]
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
    linarith only [hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u1ehi4, u5elo4]
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

theorem n7l_sAB1_H_I_M_LR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h1elo := hb1.1
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
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
            · linarith only [h7, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h7, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h10 | h10
            · linarith only [h10, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h10, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h13 | h13
          · rcases p0_3 (m.d 4 5) (by simp) with h14 | h14
            · linarith only [h14, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h14, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h17 | h17
            · linarith only [h17, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h17, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h21 | h21
    · rcases p0_3 (m.d 1 4) (by simp) with h22 | h22
      · linarith only [h22, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h24 | h24
        · linarith only [h24, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h26 | h26
          · rcases p0_3 (m.d 4 5) (by simp) with h27 | h27
            · linarith only [h27, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h27, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h30 | h30
            · linarith only [h22, h30, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h30, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
    · linarith only [h21, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h34 | h34
    · rcases p0_3 (m.d 1 4) (by simp) with h35 | h35
      · linarith only [h35, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h37 | h37
        · rcases p0_3 (m.d 3 4) (by simp) with h38 | h38
          · linarith only [h38, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h40 | h40
            · linarith only [h40, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h40, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h43 | h43
          · linarith only [h43, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h45 | h45
            · linarith only [h35, h45, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h45, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
    · linarith only [h34, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo3, u5ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h55 | h55
    · linarith only [h55, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h57 | h57
      · linarith only [h57, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h59 | h59
        · rcases p0_3 (m.d 3 4) (by simp) with h60 | h60
          · rcases p0_3 (m.d 4 5) (by simp) with h61 | h61
            · linarith only [h61, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h61, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h64 | h64
            · linarith only [h64, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h64, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h59, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h68 | h68
    · rcases p0_3 (m.d 1 4) (by simp) with h69 | h69
      · linarith only [h69, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h71 | h71
        · rcases p0_3 (m.d 3 4) (by simp) with h72 | h72
          · rcases p0_3 (m.d 4 5) (by simp) with h73 | h73
            · linarith only [h73, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h68, h73, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h76 | h76
            · linarith only [h76, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h76, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h71, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h80 | h80
      · linarith only [h80, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h82 | h82
        · rcases p0_3 (m.d 3 4) (by simp) with h83 | h83
          · rcases p0_3 (m.d 4 5) (by simp) with h84 | h84
            · linarith only [h68, h84, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h84, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h87 | h87
            · linarith only [h68, h87, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h87, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h82, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h92 | h92
    · rcases p0_3 (m.d 1 4) (by simp) with h93 | h93
      · linarith only [h93, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h95 | h95
        · rcases p0_3 (m.d 3 4) (by simp) with h96 | h96
          · linarith only [h96, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h98 | h98
            · linarith only [h98, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h92, h98, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · linarith only [h95, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h102 | h102
      · linarith only [h102, h92, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h104 | h104
        · rcases p0_3 (m.d 3 4) (by simp) with h105 | h105
          · linarith only [h105, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h107 | h107
            · linarith only [h107, h92, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h107, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h104, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h112 | h112
    · linarith only [h112, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h114 | h114
      · linarith only [h114, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h116 | h116
        · rcases p0_3 (m.d 3 4) (by simp) with h117 | h117
          · rcases p0_3 (m.d 4 5) (by simp) with h118 | h118
            · linarith only [h118, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h118, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
          · linarith only [h117, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h122 | h122
          · rcases p0_3 (m.d 4 5) (by simp) with h123 | h123
            · linarith only [h123, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h123, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
          · linarith only [h122, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h127 | h127
    · rcases p0_3 (m.d 1 4) (by simp) with h128 | h128
      · linarith only [h128, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h130 | h130
        · rcases p0_3 (m.d 3 4) (by simp) with h131 | h131
          · rcases p0_3 (m.d 4 5) (by simp) with h132 | h132
            · linarith only [h132, hc14, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h127, h132, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · linarith only [h131, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h136 | h136
          · rcases p0_3 (m.d 4 5) (by simp) with h137 | h137
            · linarith only [h137, hc14, hc45, hlam, hphi, p0_1]
            · linarith only [h137, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
          · linarith only [h136, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h141 | h141
      · linarith only [h141, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h143 | h143
        · rcases p0_3 (m.d 3 4) (by simp) with h144 | h144
          · rcases p0_3 (m.d 4 5) (by simp) with h145 | h145
            · linarith only [h127, h145, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h143, h145, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
          · linarith only [h144, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h149 | h149
          · rcases p0_3 (m.d 4 5) (by simp) with h150 | h150
            · linarith only [h127, h150, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h150, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
          · linarith only [h149, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h154 | h154
    · rcases p0_3 (m.d 1 4) (by simp) with h155 | h155
      · linarith only [h155, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h157 | h157
        · linarith only [h157, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h159 | h159
          · rcases p0_3 (m.d 4 5) (by simp) with h160 | h160
            · linarith only [h160, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h154, h160, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · linarith only [h159, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h164 | h164
      · linarith only [h154, h164, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3]
      · rcases p0_3 (m.d 2 4) (by simp) with h166 | h166
        · linarith only [h166, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h168 | h168
          · rcases p0_3 (m.d 4 5) (by simp) with h169 | h169
            · linarith only [h154, h169, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h169, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
          · linarith only [h168, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hc45, hlam, hphi, p0_1]
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

theorem n7l_sAB1_H_I_M_LR_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h1ehi := hb1.1
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
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
    linarith only [hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h3 | h3
    · rcases p0_3 (m.d 1 4) (by simp) with h4 | h4
      · rcases p0_3 (m.d 2 4) (by simp) with h5 | h5
        · linarith only [h5, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h7 | h7
          · rcases p0_3 (m.d 4 5) (by simp) with h8 | h8
            · linarith only [h8, hc24, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h8, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h11 | h11
            · linarith only [h11, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h11, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h4, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi3]
    · linarith only [h3, hlam, p0_0]
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
            · linarith only [h21, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h24 | h24
          · linarith only [h24, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h26 | h26
            · linarith only [h18, h26, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h26, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h17, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p0_1, u1ehi3]
    · linarith only [h16, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h32 | h32
    · linarith only [h32, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h34 | h34
      · rcases p0_3 (m.d 2 4) (by simp) with h35 | h35
        · rcases p0_3 (m.d 3 4) (by simp) with h36 | h36
          · rcases p0_3 (m.d 4 5) (by simp) with h37 | h37
            · linarith only [h37, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h37, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h40 | h40
            · linarith only [h40, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h40, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h43 | h43
          · rcases p0_3 (m.d 4 5) (by simp) with h44 | h44
            · linarith only [h44, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h44, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h47 | h47
            · linarith only [h47, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h47, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h34, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h52 | h52
    · rcases p0_3 (m.d 1 4) (by simp) with h53 | h53
      · rcases p0_3 (m.d 2 4) (by simp) with h54 | h54
        · linarith only [h54, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h56 | h56
          · rcases p0_3 (m.d 4 5) (by simp) with h57 | h57
            · linarith only [h57, hc24, hlam, hphi, ht45, p0_1, u5elo4]
            · linarith only [h52, h57, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h60 | h60
            · linarith only [h60, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h60, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h53, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h64 | h64
      · rcases p0_3 (m.d 2 4) (by simp) with h65 | h65
        · linarith only [h65, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h67 | h67
          · rcases p0_3 (m.d 4 5) (by simp) with h68 | h68
            · linarith only [h52, h68, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h68, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h71 | h71
            · linarith only [h52, h71, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h71, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h64, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h75 | h75
    · rcases p0_3 (m.d 1 4) (by simp) with h76 | h76
      · rcases p0_3 (m.d 2 4) (by simp) with h77 | h77
        · rcases p0_3 (m.d 3 4) (by simp) with h78 | h78
          · linarith only [h78, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h80 | h80
            · linarith only [h80, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h75, h80, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h83 | h83
          · linarith only [h83, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h85 | h85
            · linarith only [h77, h85, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h85, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h76, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h89 | h89
      · rcases p0_3 (m.d 2 4) (by simp) with h90 | h90
        · rcases p0_3 (m.d 3 4) (by simp) with h91 | h91
          · linarith only [h91, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h93 | h93
            · linarith only [h75, h93, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h93, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
        · rcases p0_3 (m.d 3 4) (by simp) with h96 | h96
          · linarith only [h96, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h98 | h98
            · linarith only [h75, h98, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h98, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
      · linarith only [h89, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h103 | h103
    · linarith only [h103, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h105 | h105
      · rcases p0_3 (m.d 2 4) (by simp) with h106 | h106
        · rcases p0_3 (m.d 3 4) (by simp) with h107 | h107
          · rcases p0_3 (m.d 4 5) (by simp) with h108 | h108
            · linarith only [h108, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h108, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
          · rcases p0_3 (m.d 4 5) (by simp) with h111 | h111
            · linarith only [h111, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h111, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
        · linarith only [h106, hlam, p0_0]
      · linarith only [h105, hc24, hlam, hphi, ht12, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht12, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h118 | h118
    · rcases p0_3 (m.d 1 4) (by simp) with h119 | h119
      · rcases p0_3 (m.d 2 4) (by simp) with h120 | h120
        · rcases p0_3 (m.d 3 4) (by simp) with h121 | h121
          · linarith only [h121, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h123 | h123
            · linarith only [h123, hc34, hc45, hlam, hphi, p0_1]
            · linarith only [h118, h123, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
        · linarith only [h120, hlam, p0_0]
      · linarith only [h119, hc24, hlam, hphi, ht12, p0_1, u1ehi3]
    · rcases p0_3 (m.d 1 4) (by simp) with h128 | h128
      · rcases p0_3 (m.d 2 4) (by simp) with h129 | h129
        · rcases p0_3 (m.d 3 4) (by simp) with h130 | h130
          · linarith only [h130, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h132 | h132
            · linarith only [h118, h132, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h128, h132, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
        · linarith only [h129, hlam, p0_0]
      · linarith only [h128, hc24, hlam, hphi, ht12, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h138 | h138
    · linarith only [h138, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h140 | h140
      · rcases p0_3 (m.d 2 4) (by simp) with h141 | h141
        · rcases p0_3 (m.d 3 4) (by simp) with h142 | h142
          · rcases p0_3 (m.d 4 5) (by simp) with h143 | h143
            · linarith only [h143, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h140, h143, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
          · linarith only [h142, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h147 | h147
          · rcases p0_3 (m.d 4 5) (by simp) with h148 | h148
            · linarith only [h148, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h148, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
          · linarith only [h147, hlam, p0_0]
      · linarith only [h140, hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h154 | h154
    · rcases p0_3 (m.d 1 4) (by simp) with h155 | h155
      · rcases p0_3 (m.d 2 4) (by simp) with h156 | h156
        · linarith only [h156, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h158 | h158
          · rcases p0_3 (m.d 4 5) (by simp) with h159 | h159
            · linarith only [h159, hc24, hc45, hlam, hphi, p0_1]
            · linarith only [h154, h159, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi9]
          · linarith only [h158, hlam, p0_0]
      · linarith only [h155, hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi3]
    · rcases p0_3 (m.d 1 4) (by simp) with h164 | h164
      · rcases p0_3 (m.d 2 4) (by simp) with h165 | h165
        · linarith only [h165, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h167 | h167
          · rcases p0_3 (m.d 4 5) (by simp) with h168 | h168
            · linarith only [h154, h168, hc04, hc45, hlam, hphi, p0_1]
            · linarith only [h164, h168, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi9]
          · linarith only [h167, hlam, p0_0]
      · linarith only [h164, hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi9]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hc45, hlam, hphi, p0_1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u1ehi3, u5elo4]
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

theorem n7l_sAB1_H_L_H_I_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h1elo := hb1.1
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 3 4 5 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h2, h5, h6, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · linarith only [h6, hc34, hlam, hphi, u4elo4]
            · linarith only [h5, hc23, hlam, hphi, ht34, u4elo3]
          · linarith only [h4, hc13, hlam, hphi, ht34, u4elo3]
        · linarith only [h3, hc12, hlam, hphi, ht23, ht34, u4elo2]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h12 | h12
        · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
          · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
            · rcases m.htr 3 4 5 (by decide) (by decide) with h15 | h15
              · linarith only [h0, h12, h14, h15, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · linarith only [h15, hc34, hlam, hphi, u4elo4]
            · linarith only [h14, h2, hc12, hlam, hphi, ht23, ht34, u4elo3]
          · linarith only [h12, h13, h2, hc24, hlam, hphi, u4elo3]
        · linarith only [h12, hc12, hlam, hphi, ht23, ht34, u4elo2]
    · linarith only [h1, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h22 | h22
    · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
      · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
        · rcases m.htr 1 3 4 (by decide) (by decide) with h25 | h25
          · rcases m.htr 2 3 4 (by decide) (by decide) with h26 | h26
            · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
              · linarith only [h0, h22, h24, h26, h27, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
              · linarith only [h27, hc34, hlam, hphi, u4elo4]
            · linarith only [h26, hc23, hlam, hphi, ht34, u4elo3]
          · linarith only [h0, h25, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
        · linarith only [h0, h22, h23, h24, hc14, hlam, hphi, u4elo2]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h33 | h33
        · rcases m.htr 1 3 4 (by decide) (by decide) with h34 | h34
          · rcases m.htr 2 3 4 (by decide) (by decide) with h35 | h35
            · rcases m.htr 3 4 5 (by decide) (by decide) with h36 | h36
              · linarith only [h0, h22, h33, h35, h36, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
              · linarith only [h36, hc34, hlam, hphi, u4elo4]
            · linarith only [h0, h22, h23, h33, h35, hc24, hlam, hphi, u4elo3]
          · linarith only [h0, h22, h33, h34, hc24, hlam, hphi, u4elo3]
        · linarith only [h33, hc12, hlam, hphi, ht23, ht34, u4elo2]
    · linarith only [h22, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]

theorem n7l_sAB1_H_L_H_I_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5bigk := hb5.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11 | h11
                        · rcases h5bigk with h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p12_1, u4elo0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h4, h9, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p12_1, u4elo0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p12_1, u4elo0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p12_1, u4elo0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h0, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h0, h9, hc01, hc35, hlam, hphi, ht0b, ht5b, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h0, h11, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p12_1, u4elo0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h0, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p12_1, u4elo0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h2, hlam, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h6, hlam, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h11, h2, hc02, hc45, hlam, hphi, ht0b, ht5b, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h0, h4, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p12_1, u4elo0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h3, hlam, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h3, hc03, hc15, hlam, hphi, ht0b, ht5b, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h9, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h0, h6, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h4, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h7, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h10, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h11, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                        · linarith only [h11, hc34, hlam, hphi, u4elo4]
                      · linarith only [h10, h4, hc24, hlam, hphi, u4elo0]
                    · linarith only [h3, h4, h9, hc23, hlam, hphi, ht34, u4elo0]
                  · linarith only [h8, hc23, hlam, hphi, ht34, u4elo3]
                · linarith only [h4, h7, hc14, hlam, hphi, u4elo0]
              · linarith only [h2, h4, h6, hc12, hlam, hphi, ht23, ht34, u4elo0]
            · linarith only [h5, hc12, hlam, hphi, ht23, ht34, u4elo2]
          · linarith only [h4, hc04, hlam, hphi, u4elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h46 | h46
          · rcases m.htr 1 2 4 (by decide) (by decide) with h47 | h47
            · rcases m.htr 1 2 5 (by decide) (by decide) with h48 | h48
              · rcases m.htr 1 4 5 (by decide) (by decide) with h49 | h49
                · rcases m.htr 2 3 4 (by decide) (by decide) with h50 | h50
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h51 | h51
                    · linarith only [h0, h3, h46, h48, h51, hc03, hlam, hphi, ht34, u4elo0]
                    · linarith only [h0, h46, h48, h50, h51, hc34, hlam, hphi, u4elo0]
                  · linarith only [h50, hc23, hlam, hphi, ht34, u4elo3]
                · linarith only [h49, hc14, hlam, hphi, u4elo4]
              · linarith only [h2, h46, h48, hc12, hlam, hphi, ht23, ht34, u4elo0]
            · linarith only [h47, hc12, hlam, hphi, ht23, ht34, u4elo2]
          · linarith only [h46, hc04, hlam, hphi, u4elo4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h59 | h59
        · rcases m.htr 0 4 5 (by decide) (by decide) with h60 | h60
          · linarith only [h1, h2, h60, hc24, hlam, hphi, u4elo0]
          · linarith only [h60, hc04, hlam, hphi, u4elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h63 | h63
          · linarith only [h1, h2, h63, hc24, hlam, hphi, u4elo0]
          · linarith only [h63, hc04, hlam, hphi, u4elo4]
    · linarith only [h1, hc02, hlam, hphi, ht23, ht34, u4elo2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h67 | h67
    · rcases m.htr 0 2 5 (by decide) (by decide) with h68 | h68
      · rcases m.htr 0 3 5 (by decide) (by decide) with h69 | h69
        · rcases m.htr 0 4 5 (by decide) (by decide) with h70 | h70
          · rcases m.htr 1 2 4 (by decide) (by decide) with h71 | h71
            · rcases m.htr 1 2 5 (by decide) (by decide) with h72 | h72
              · rcases m.htr 1 4 5 (by decide) (by decide) with h73 | h73
                · linarith only [h0, h73, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                · linarith only [h73, hc14, hlam, hphi, u4elo4]
              · linarith only [h68, h70, h72, hc12, hlam, hphi, ht23, ht34, u4elo0]
            · linarith only [h71, hc12, hlam, hphi, ht23, ht34, u4elo2]
          · linarith only [h70, hc04, hlam, hphi, u4elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h79 | h79
          · rcases m.htr 1 2 4 (by decide) (by decide) with h80 | h80
            · rcases m.htr 1 2 5 (by decide) (by decide) with h81 | h81
              · rcases m.htr 1 4 5 (by decide) (by decide) with h82 | h82
                · linarith only [h0, h82, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                · linarith only [h82, hc14, hlam, hphi, u4elo4]
              · linarith only [h68, h79, h81, hc12, hlam, hphi, ht23, ht34, u4elo0]
            · linarith only [h80, hc12, hlam, hphi, ht23, ht34, u4elo2]
          · linarith only [h79, hc04, hlam, hphi, u4elo4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h88 | h88
        · rcases m.htr 0 4 5 (by decide) (by decide) with h89 | h89
          · linarith only [h67, h68, h89, hc24, hlam, hphi, u4elo0]
          · linarith only [h89, hc04, hlam, hphi, u4elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h92 | h92
          · linarith only [h67, h68, h92, hc24, hlam, hphi, u4elo0]
          · linarith only [h92, hc04, hlam, hphi, u4elo4]
    · linarith only [h67, hc02, hlam, hphi, ht23, ht34, u4elo2]

theorem n7l_sAB1_H_L_H_I_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h1ehi := hb1.1
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  linarith only [hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo1]

theorem n7l_sAB1_H_L_H_L_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h1elo := hb1.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 3 4 5 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h4, h6, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · linarith only [h6, hc34, hlam, hphi, u4elo4]
            · linarith only [h5, hc23, hlam, hphi, ht34, u4elo3]
          · linarith only [h2, h4, hc13, hlam, hphi, ht34, u4elo0]
        · linarith only [h3, hc12, hlam, hphi, ht23, ht34, u4elo2]
      · linarith only [h2, hc03, hlam, hphi, ht34, u4elo3]
    · linarith only [h1, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h14 | h14
    · rcases m.htr 0 3 4 (by decide) (by decide) with h15 | h15
      · rcases m.htr 1 2 4 (by decide) (by decide) with h16 | h16
        · rcases m.htr 1 3 4 (by decide) (by decide) with h17 | h17
          · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
            · rcases m.htr 3 4 5 (by decide) (by decide) with h19 | h19
              · linarith only [h0, h14, h16, h18, h19, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
              · linarith only [h19, hc34, hlam, hphi, u4elo4]
            · linarith only [h18, hc23, hlam, hphi, ht34, u4elo3]
          · linarith only [h0, h15, h17, hc01, hlam, hphi, ht12, ht23, ht34, u4elo0]
        · linarith only [h16, hc12, hlam, hphi, ht23, ht34, u4elo2]
      · linarith only [h15, hc03, hlam, hphi, ht34, u4elo3]
    · linarith only [h14, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]

theorem n7l_sAB1_H_L_H_L_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h4elo := hb4.1
  have h5elo := hb5.1
  have h1bigk := hb1.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                            · linarith only [h0, h11, h13, h5, hc01, hc45, hlam, hphi, ht0b, ht5b]
                            · linarith only [h13, hc34, hlam, hphi, u4elo4]
                          · linarith only [h12, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h11, hc23, hlam, hphi, ht34, u4elo3]
                      · linarith only [h10, h8, hc34, hlam, hphi, u4elo4]
                    · linarith only [h9, hc13, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h5, h8, hc23, hlam, hphi, ht34, u4elo3]
                · linarith only [h7, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h5, h6, hc23, hlam, hphi, ht34, u4elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h23 | h23
              · rcases m.htr 1 2 5 (by decide) (by decide) with h24 | h24
                · rcases m.htr 1 3 4 (by decide) (by decide) with h25 | h25
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h26 | h26
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h27 | h27
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h28 | h28
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h29 | h29
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h30 | h30
                            · linarith only [h0, h23, h28, h30, h4, h5, hc01, hc45, hlam, hphi, ht0b, ht5b]
                            · linarith only [h30, hc34, hlam, hphi, u4elo4]
                          · linarith only [h29, h5, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                        · linarith only [h23, h28, h5, hc24, hlam, hphi, u4elo3]
                      · linarith only [h27, hc14, hlam, hphi, u4elo4]
                    · linarith only [h23, h26, h5, hc24, hlam, hphi, ht45, u5elo3]
                  · linarith only [h23, h25, h5, hc24, hlam, hphi, u4elo3]
                · linarith only [h23, h24, hc24, hlam, hphi, ht45, u5elo2]
              · linarith only [h23, hc12, hlam, hphi, ht23, ht34, u4elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h40 | h40
            · linarith only [h0, h4, h40, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h42 | h42
              · rcases m.htr 1 2 5 (by decide) (by decide) with h43 | h43
                · rcases m.htr 1 3 4 (by decide) (by decide) with h44 | h44
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h45 | h45
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h46 | h46
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h47 | h47
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h48 | h48
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h49 | h49
                            · rcases h1bigk with h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h42, h47, h49, hc01, hc45, hlam, hphi, ht0b, ht5b, p50_1]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h40, h42, h47, h49, hc01, hc45, hlam, hphi, ht0b, ht5b, p50_1]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                rcases p50_3 (m.d 0 1) (by simp) with h54 | h54
                                · rcases p50_3 (m.d 1 2) (by simp) with h55 | h55
                                  · linarith only [h0, h55, hlam]
                                  · linarith only [h42, h55, hlam]
                                · linarith only [h54, hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                rcases p50_3 (m.d 0 1) (by simp) with h59 | h59
                                · rcases p50_3 (m.d 1 2) (by simp) with h60 | h60
                                  · linarith only [h0, h60, hlam]
                                  · linarith only [h43, h60, hlam]
                                · linarith only [h59, hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h0, hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h40, hlam, p50_1]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h0, h4, h42, h47, h49, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p50_1]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                rcases p50_3 (m.d 0 1) (by simp) with h68 | h68
                                · rcases p50_3 (m.d 1 2) (by simp) with h69 | h69
                                  · rcases p50_3 (m.d 1 3) (by simp) with h70 | h70
                                    · rcases p50_3 (m.d 1 4) (by simp) with h71 | h71
                                      · linarith only [h42, h71, hlam]
                                      · linarith only [h46, h71, hlam]
                                    · linarith only [h45, h70, hlam]
                                  · linarith only [h43, h69, hlam]
                                · linarith only [h3, h68, hlam]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h1, hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h1, h42, h47, h49, hc01, hc45, hlam, hphi, ht0b, ht5b, p50_1]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h1, h42, h47, h49, hc01, hc45, hlam, hphi, ht0b, ht5b, p50_1]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                rcases p50_3 (m.d 0 1) (by simp) with h81 | h81
                                · rcases p50_3 (m.d 1 2) (by simp) with h82 | h82
                                  · linarith only [h40, h82, hlam]
                                  · linarith only [h43, h82, hlam]
                                · linarith only [h3, h81, hlam]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h2, hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h42, hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h44, hlam, p50_1]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h2, h43, h48, h49, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p50_1, u4elo0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h3, hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h43, hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h45, hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [h46, hlam, p50_0]
                              · have p50_0 := h50c.1
                                have p50_1 := h50c.2.1
                                have p50_2 := h50c.2.2.1
                                have p50_3 := h50c.2.2.2
                                linarith only [hlam, p50_0]
                            · linarith only [h49, hc34, hlam, hphi, u4elo4]
                          · linarith only [h4, h48, hc03, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h0, h4, h42, h47, hc24, hlam, hphi, u4elo3]
                      · linarith only [h46, hc14, hlam, hphi, u4elo4]
                    · linarith only [h40, h42, h45, hc24, hlam, hphi, ht45, u5elo3]
                  · linarith only [h40, h42, h44, hc24, hlam, hphi, u4elo3]
                · linarith only [h42, h43, hc24, hlam, hphi, ht45, u5elo2]
              · linarith only [h42, hc12, hlam, hphi, ht23, ht34, u4elo2]
        · linarith only [h3, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · linarith only [h2, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h106 | h106
      · rcases m.htr 0 1 5 (by decide) (by decide) with h107 | h107
        · rcases m.htr 0 2 3 (by decide) (by decide) with h108 | h108
          · linarith only [h0, h1, h108, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h110 | h110
            · linarith only [h0, h1, h108, h110, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h112 | h112
              · rcases m.htr 1 2 5 (by decide) (by decide) with h113 | h113
                · rcases m.htr 1 3 4 (by decide) (by decide) with h114 | h114
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h115 | h115
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h116 | h116
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h117 | h117
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h118 | h118
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h119 | h119
                            · linarith only [h0, h1, h110, h112, h117, h119, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h106, h116, h119, hc34, hlam, hphi, u4elo0]
                          · linarith only [h0, h1, h110, h118, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h106, h110, h112, h116, h117, hc24, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u4elo0]
                      · linarith only [h116, hc14, hlam, hphi, u4elo4]
                    · linarith only [h0, h1, h112, h115, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h0, h1, h112, h114, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h112, h113, hc24, hlam, hphi, ht45, u5elo2]
              · linarith only [h112, hc12, hlam, hphi, ht23, ht34, u4elo2]
        · linarith only [h107, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
      · linarith only [h0, h106, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h131 | h131
    · rcases m.htr 0 1 4 (by decide) (by decide) with h132 | h132
      · rcases m.htr 0 1 5 (by decide) (by decide) with h133 | h133
        · rcases m.htr 0 2 3 (by decide) (by decide) with h134 | h134
          · rcases m.htr 1 2 3 (by decide) (by decide) with h135 | h135
            · rcases m.htr 1 2 4 (by decide) (by decide) with h136 | h136
              · rcases m.htr 1 2 5 (by decide) (by decide) with h137 | h137
                · rcases m.htr 1 3 4 (by decide) (by decide) with h138 | h138
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h139 | h139
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h140 | h140
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h141 | h141
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h142 | h142
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h143 | h143
                            · linarith only [h0, h131, h135, h141, h143, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h143, hc34, hlam, hphi, u4elo4]
                          · linarith only [h142, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h141, hc23, hlam, hphi, ht34, u4elo3]
                      · linarith only [h136, h140, hc24, hlam, hphi, u4elo4]
                    · linarith only [h139, hc13, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h135, h138, hc23, hlam, hphi, ht34, u4elo3]
                · linarith only [h0, h137, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
              · linarith only [h0, h131, h135, h136, hc23, hlam, hphi, ht34, u4elo2]
            · linarith only [h0, h134, h135, hlam]
          · linarith only [h0, h131, h134, hlam]
        · linarith only [h131, h133, hc13, hlam, hphi, ht34, ht45, u5elo1]
      · linarith only [h131, h132, hc13, hlam, hphi, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h157 | h157
      · rcases m.htr 0 1 5 (by decide) (by decide) with h158 | h158
        · rcases m.htr 0 2 3 (by decide) (by decide) with h159 | h159
          · rcases m.htr 1 2 3 (by decide) (by decide) with h160 | h160
            · rcases m.htr 1 2 4 (by decide) (by decide) with h161 | h161
              · rcases m.htr 1 2 5 (by decide) (by decide) with h162 | h162
                · rcases m.htr 1 3 4 (by decide) (by decide) with h163 | h163
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h164 | h164
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h165 | h165
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h166 | h166
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h167 | h167
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h168 | h168
                            · rcases h1bigk with h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c
                              · have p169_0 := h169c.1
                                have p169_1 := h169c.2.1
                                have p169_2 := h169c.2.2.1
                                have p169_3 := h169c.2.2.2
                                linarith only [hlam, p169_0]
                              · have p169_0 := h169c.1
                                have p169_1 := h169c.2.1
                                have p169_2 := h169c.2.2.1
                                have p169_3 := h169c.2.2.2
                                linarith only [h0, hlam, p169_0]
                              · have p169_0 := h169c.1
                                have p169_1 := h169c.2.1
                                have p169_2 := h169c.2.2.1
                                have p169_3 := h169c.2.2.2
                                linarith only [h131, hlam, p169_0]
                              · have p169_0 := h169c.1
                                have p169_1 := h169c.2.1
                                have p169_2 := h169c.2.2.1
                                have p169_3 := h169c.2.2.2
                                linarith only [h131, h160, h161, h166, h168, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p169_1]
                              · have p169_0 := h169c.1
                                have p169_1 := h169c.2.1
                                have p169_2 := h169c.2.2.1
                                have p169_3 := h169c.2.2.2
                                rcases p169_3 (m.d 0 1) (by simp) with h174 | h174
                                · rcases p169_3 (m.d 1 2) (by simp) with h175 | h175
                                  · rcases p169_3 (m.d 1 3) (by simp) with h176 | h176
                                    · rcases p169_3 (m.d 1 4) (by simp) with h177 | h177
                                      · linarith only [h157, h177, hlam]
                                      · linarith only [h165, h177, hlam]
                                    · linarith only [h164, h176, hlam]
                                  · linarith only [h162, h175, hlam]
                                · linarith only [h174, hlam, p169_0]
                              · have p169_0 := h169c.1
                                have p169_1 := h169c.2.1
                                have p169_2 := h169c.2.2.1
                                have p169_3 := h169c.2.2.2
                                linarith only [h157, h161, h166, h168, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p169_1]
                              · have p169_0 := h169c.1
                                have p169_1 := h169c.2.1
                                have p169_2 := h169c.2.2.1
                                have p169_3 := h169c.2.2.2
                                linarith only [hlam, p169_0]
                              · have p169_0 := h169c.1
                                have p169_1 := h169c.2.1
                                have p169_2 := h169c.2.2.1
                                have p169_3 := h169c.2.2.2
                                linarith only [h131, hc01, hc12, hlam, hphi, p169_1]
                              · have p169_0 := h169c.1
                                have p169_1 := h169c.2.1
                                have p169_2 := h169c.2.2.1
                                have p169_3 := h169c.2.2.2
                                rcases p169_3 (m.d 0 1) (by simp) with h186 | h186
                                · linarith only [h0, h186, hlam]
                                · linarith only [h157, h186, hlam]
                              · have p169_0 := h169c.1
                                have p169_1 := h169c.2.1
                                have p169_2 := h169c.2.2.1
                                have p169_3 := h169c.2.2.2
                                rcases p169_3 (m.d 0 1) (by simp) with h189 | h189
                                · linarith only [h0, h189, hlam]
                                · linarith only [h158, h189, hlam]
                              · have p169_0 := h169c.1
                                have p169_1 := h169c.2.1
                                have p169_2 := h169c.2.2.1
                                have p169_3 := h169c.2.2.2
                                linarith only [h157, h160, h161, h166, h168, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p169_1]
                              · have p169_0 := h169c.1
                                have p169_1 := h169c.2.1
                                have p169_2 := h169c.2.2.1
                                have p169_3 := h169c.2.2.2
                                linarith only [h160, hlam, p169_0]
                              · have p169_0 := h169c.1
                                have p169_1 := h169c.2.1
                                have p169_2 := h169c.2.2.1
                                have p169_3 := h169c.2.2.2
                                linarith only [hlam, p169_0]
                              · have p169_0 := h169c.1
                                have p169_1 := h169c.2.1
                                have p169_2 := h169c.2.2.1
                                have p169_3 := h169c.2.2.2
                                rcases p169_3 (m.d 0 1) (by simp) with h195 | h195
                                · linarith only [h131, h195, hlam]
                                · linarith only [h157, h195, hlam]
                              · have p169_0 := h169c.1
                                have p169_1 := h169c.2.1
                                have p169_2 := h169c.2.2.1
                                have p169_3 := h169c.2.2.2
                                rcases p169_3 (m.d 0 1) (by simp) with h198 | h198
                                · linarith only [h131, h198, hlam]
                                · linarith only [h158, h198, hlam]
                              · have p169_0 := h169c.1
                                have p169_1 := h169c.2.1
                                have p169_2 := h169c.2.2.1
                                have p169_3 := h169c.2.2.2
                                linarith only [h157, hlam, p169_0]
                              · have p169_0 := h169c.1
                                have p169_1 := h169c.2.1
                                have p169_2 := h169c.2.2.1
                                have p169_3 := h169c.2.2.2
                                linarith only [h161, hlam, p169_0]
                              · have p169_0 := h169c.1
                                have p169_1 := h169c.2.1
                                have p169_2 := h169c.2.2.1
                                have p169_3 := h169c.2.2.2
                                linarith only [h163, hlam, p169_1]
                              · have p169_0 := h169c.1
                                have p169_1 := h169c.2.1
                                have p169_2 := h169c.2.2.1
                                have p169_3 := h169c.2.2.2
                                linarith only [hlam, p169_0]
                              · have p169_0 := h169c.1
                                have p169_1 := h169c.2.1
                                have p169_2 := h169c.2.2.1
                                have p169_3 := h169c.2.2.2
                                linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p169_1, u4elo1]
                              · have p169_0 := h169c.1
                                have p169_1 := h169c.2.1
                                have p169_2 := h169c.2.2.1
                                have p169_3 := h169c.2.2.2
                                linarith only [h158, hlam, p169_0]
                              · have p169_0 := h169c.1
                                have p169_1 := h169c.2.1
                                have p169_2 := h169c.2.2.1
                                have p169_3 := h169c.2.2.2
                                linarith only [h162, hlam, p169_0]
                              · have p169_0 := h169c.1
                                have p169_1 := h169c.2.1
                                have p169_2 := h169c.2.2.1
                                have p169_3 := h169c.2.2.2
                                linarith only [h164, hlam, p169_0]
                              · have p169_0 := h169c.1
                                have p169_1 := h169c.2.1
                                have p169_2 := h169c.2.2.1
                                have p169_3 := h169c.2.2.2
                                linarith only [h165, hlam, p169_0]
                              · have p169_0 := h169c.1
                                have p169_1 := h169c.2.1
                                have p169_2 := h169c.2.2.1
                                have p169_3 := h169c.2.2.2
                                linarith only [hlam, p169_0]
                            · linarith only [h168, hc34, hlam, hphi, u4elo4]
                          · linarith only [h167, hc23, hlam, hphi, ht34, ht45, u5elo3]
                        · linarith only [h166, hc23, hlam, hphi, ht34, u4elo3]
                      · linarith only [h165, hc14, hlam, hphi, u4elo4]
                    · linarith only [h164, hc13, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h131, h163, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                · linarith only [h162, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
              · linarith only [h131, h160, h161, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
            · linarith only [h0, h157, h159, h160, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h220 | h220
            · rcases m.htr 1 2 4 (by decide) (by decide) with h221 | h221
              · rcases m.htr 1 2 5 (by decide) (by decide) with h222 | h222
                · rcases m.htr 1 3 4 (by decide) (by decide) with h223 | h223
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h224 | h224
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h225 | h225
                      · linarith only [h0, h157, h159, h220, h225, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h225, hc14, hlam, hphi, u4elo4]
                    · linarith only [h0, h159, h220, h224, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · linarith only [h0, h157, h159, h220, h221, h223, hc24, hlam, hphi, u4elo3]
                · linarith only [h0, h157, h159, h220, h221, h222, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · linarith only [h0, h159, h220, h221, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h232 | h232
              · rcases m.htr 1 2 5 (by decide) (by decide) with h233 | h233
                · rcases m.htr 1 3 4 (by decide) (by decide) with h234 | h234
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h235 | h235
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h236 | h236
                      · linarith only [h0, h157, h220, h236, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h236, hc14, hlam, hphi, u4elo4]
                    · linarith only [h235, hc13, hlam, hphi, ht34, ht45, u5elo3]
                  · linarith only [h0, h220, h234, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                · linarith only [h0, h157, h232, h233, hc24, hlam, hphi, ht45, u5elo2]
              · linarith only [h0, h232, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
        · linarith only [h157, h158, hc14, hlam, hphi, ht45, u5elo1]
      · linarith only [h157, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]

theorem n7l_sAB1_H_L_H_L_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h1ehi := hb1.1
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  linarith only [hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo1]

theorem n7l_sAB1_H_L_H_R_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAB1_H_L_H_R_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAB1_H_L_H_R_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAB1_H_L_M_IR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAB1_H_L_M_IR_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAB1_H_L_M_IR_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h1ehi := hb1.1
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  linarith only [hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo1]

theorem n7l_sAB1_H_L_M_LI_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAB1_H_L_M_LI_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAB1_H_L_M_LI_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h1ehi := hb1.1
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  linarith only [hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo1]

theorem n7l_sAB1_H_L_M_LR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAB1_H_L_M_LR_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc14 := m.hcor 1 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.2.2.1
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi9]
  · linarith only [h0, hc14, hlam, hphi, u4elo4]

theorem n7l_sAB1_H_L_M_LR_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_L m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h1ehi := hb1.1
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  linarith only [hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo1]

theorem n7l_sAB1_H_R_H_I_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h1elo := hb1.1
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  rcases m.htr 1 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi4]
  · linarith only [h0, hc45, hlam, hphi, u4ehi1]

theorem n7l_sAB1_H_R_H_I_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5emax := hb5.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 3 4 5 (by decide) (by decide) with h5 | h5
            · linarith only [h2, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
            · linarith only [h0, h5, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
          · linarith only [h1, h4, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
        · linarith only [h2, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
        · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
          · rcases m.htr 3 4 5 (by decide) (by decide) with h12 | h12
            · linarith only [h10, h12, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
            · linarith only [h12, h2, hc45, hlam, hphi, u4ehi2]
          · linarith only [h1, h11, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
          · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
            · rcases h5emax with h18 | h18 | h18 | h18 | h18
              · linarith only [h0, h18, hlam, ht45, u4ehi4]
              · linarith only [h1, h18, hlam, ht45, u4ehi4]
              · linarith only [h16, h18, hlam, ht45, u4ehi4]
              · linarith only [h10, h16, h18, h2, hc23, hc34, hlam, hphi, ht45, u4ehi4]
              · linarith only [h18, hlam, ht45, u4ehi4]
            · linarith only [h16, h17, h2, hlam]
          · linarith only [h16, hc45, hlam, hphi, u4ehi2]
    · linarith only [h0, h1, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
  · linarith only [h0, hc45, hlam, hphi, u4ehi0]

theorem n7l_sAB1_H_R_H_I_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h4ehi := hb4.1
  have h5emax := hb5.2.2
  have h1ehi := hb1.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 4 5 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h6, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
              · linarith only [h6, hc45, hlam, hphi, u4ehi2]
            · linarith only [h4, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
            · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
              · linarith only [h0, h11, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
              · linarith only [h11, hc45, hlam, hphi, u4ehi2]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
              · linarith only [h0, h14, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
              · linarith only [h14, hc45, hlam, hphi, u4ehi2]
        · linarith only [h0, h2, h3, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
      · linarith only [h2, hc45, hlam, hphi, u4ehi0]
    · linarith only [h0, h1, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h20 | h20
    · rcases m.htr 0 4 5 (by decide) (by decide) with h21 | h21
      · rcases m.htr 1 4 5 (by decide) (by decide) with h22 | h22
        · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
          · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
            · rcases m.htr 2 4 5 (by decide) (by decide) with h25 | h25
              · linarith only [h0, h20, h25, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · linarith only [h21, h25, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
            · linarith only [h0, h20, h21, h23, h24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h29 | h29
            · rcases m.htr 2 4 5 (by decide) (by decide) with h30 | h30
              · linarith only [h0, h20, h30, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · linarith only [h21, h30, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h33 | h33
              · linarith only [h0, h20, h23, h33, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
              · linarith only [h0, h20, h21, h29, h33, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · linarith only [h0, h20, h21, h22, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
      · linarith only [h21, hc45, hlam, hphi, u4ehi0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h38 | h38
      · rcases m.htr 1 4 5 (by decide) (by decide) with h39 | h39
        · rcases m.htr 2 3 4 (by decide) (by decide) with h40 | h40
          · rcases m.htr 2 3 5 (by decide) (by decide) with h41 | h41
            · rcases m.htr 2 4 5 (by decide) (by decide) with h42 | h42
              · rcases m.htr 3 4 5 (by decide) (by decide) with h43 | h43
                · linarith only [h40, h43, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · linarith only [h38, h43, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
              · linarith only [h0, h38, h42, hlam]
            · linarith only [h0, h38, h40, h41, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h48 | h48
            · rcases m.htr 2 4 5 (by decide) (by decide) with h49 | h49
              · rcases m.htr 3 4 5 (by decide) (by decide) with h50 | h50
                · linarith only [h40, h48, h50, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                · linarith only [h20, h38, h40, h48, h50, hc02, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h0, h49, hc45, hlam, hphi, u4ehi0]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h54 | h54
              · rcases m.htr 3 4 5 (by decide) (by decide) with h55 | h55
                · rcases h5emax with h56 | h56 | h56 | h56 | h56
                  · linarith only [h38, h56, hlam, ht45, u4ehi4]
                  · linarith only [h56, hlam, ht12, ht23, ht34, ht45, u1ehi4]
                  · linarith only [h20, h38, h56, hlam, ht45, u4ehi4]
                  · linarith only [h48, h56, hc23, hlam, ht34, ht45]
                  · linarith only [h56, hlam, ht45, u4ehi4]
                · linarith only [h0, h38, h40, h55, hlam]
              · linarith only [h0, h38, h54, hlam]
        · linarith only [h38, h39, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
      · linarith only [h38, hc45, hlam, hphi, u4ehi0]

theorem n7l_sAB1_H_R_H_L_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB1_H_R_H_L_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB1_H_R_H_L_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB1_H_R_H_R_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5ehi := hb5.1
  have h1elo := hb1.1
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  rcases m.htr 1 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi4]
  · linarith only [h0, hc45, hlam, hphi, u4ehi1]

theorem n7l_sAB1_H_R_H_R_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
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
  have h5ehi := hb5.1
  have h1bigk := hb1.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
              · linarith only [h5, h7, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                · linarith only [h4, h5, h9, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
                  · linarith only [h11, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                  · linarith only [h11, hc45, hlam, hphi, u4ehi1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14 | h14
            · linarith only [h14, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h16 | h16
              · linarith only [h16, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h18 | h18
                · linarith only [h1, h18, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h20 | h20
                  · linarith only [h2, h20, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h20, hc45, hlam, hphi, u4ehi1]
        · linarith only [h2, h3, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h24 | h24
        · linarith only [h2, h24, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h26 | h26
          · rcases m.htr 1 2 4 (by decide) (by decide) with h27 | h27
            · linarith only [h0, h2, h27, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h29 | h29
              · linarith only [h0, h2, h27, h29, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h31 | h31
                · linarith only [h0, h2, h26, h27, h31, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                · linarith only [h0, h2, h26, h31, hc23, hc34, hlam, hphi]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h34 | h34
            · linarith only [h26, h34, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h36 | h36
              · linarith only [h1, h26, h36, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h38 | h38
                · linarith only [h1, h2, h34, h38, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h40 | h40
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h41 | h41
                    · linarith only [h1, h24, h26, h38, h40, h41, hc12, hc23, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h43 | h43
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h44 | h44
                        · rcases h1bigk with h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [hlam, p45_0]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h24, h36, hc12, hc25, hlam, hphi, p45_1]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h24, h26, h36, hc12, hc25, hlam, hphi, p45_1]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h2, hlam, p45_0]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h24, hlam, p45_0]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h0, hlam, p45_0]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [hlam, p45_0]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h26, hlam, p45_1]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h34, hlam, p45_1]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h36, hlam, p45_1]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h1, hlam, p45_0]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h1, h24, h36, hc12, hc25, hlam, hphi, p45_1]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [hlam, p45_0]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h38, hlam, p45_0]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h1, h24, hlam, p45_1]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h1, h34, h41, hc13, hc34, hlam, hphi, p45_1]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            rcases p45_3 (m.d 0 1) (by simp) with h62 | h62
                            · linarith only [h2, h62, hlam]
                            · linarith only [h0, h62, hlam]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            rcases p45_3 (m.d 0 1) (by simp) with h65 | h65
                            · linarith only [h2, h65, hlam]
                            · linarith only [h1, h65, hlam]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [hlam, p45_0]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h24, h34, h41, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p45_1, u5ehi0]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h1, h26, h36, h41, h43, hc12, hc34, hlam, hphi, ht23, p45_1]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            rcases p45_3 (m.d 0 1) (by simp) with h71 | h71
                            · linarith only [h24, h71, hlam]
                            · linarith only [h0, h71, hlam]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            rcases p45_3 (m.d 0 1) (by simp) with h74 | h74
                            · linarith only [h24, h74, hlam]
                            · linarith only [h1, h74, hlam]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [h40, hlam, p45_0]
                          · have p45_0 := h45c.1
                            have p45_1 := h45c.2.1
                            have p45_2 := h45c.2.2.1
                            have p45_3 := h45c.2.2.2
                            linarith only [hlam, p45_0]
                        · linarith only [h2, h34, h41, h44, hc45, hlam, hphi, u4ehi0]
                      · linarith only [h34, h40, h43, hlam]
                  · linarith only [h2, h40, hc45, hlam, hphi, u4ehi0]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h82 | h82
      · linarith only [h1, h82, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h84 | h84
        · linarith only [h1, h84, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h86 | h86
          · linarith only [h0, h1, h86, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h88 | h88
            · linarith only [h0, h1, h86, h88, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h90 | h90
              · linarith only [h0, h1, h86, h90, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h92 | h92
                · rcases m.htr 1 4 5 (by decide) (by decide) with h93 | h93
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h94 | h94
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h95 | h95
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h96 | h96
                        · linarith only [h86, h92, h96, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                        · linarith only [h96, hc45, hlam, hphi, u4ehi3]
                      · linarith only [h88, h93, h95, hlam]
                    · linarith only [h0, h84, h86, h92, h93, h94, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h93, hc45, hlam, hphi, u4ehi1]
                · linarith only [h0, h1, h92, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h103 | h103
    · rcases m.htr 0 1 4 (by decide) (by decide) with h104 | h104
      · linarith only [h0, h104, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h106 | h106
        · linarith only [h0, h106, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h108 | h108
          · rcases m.htr 1 2 4 (by decide) (by decide) with h109 | h109
            · rcases m.htr 1 2 5 (by decide) (by decide) with h110 | h110
              · rcases m.htr 1 3 4 (by decide) (by decide) with h111 | h111
                · linarith only [h103, h104, h109, h111, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h113 | h113
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h114 | h114
                    · linarith only [h103, h106, h108, h111, h113, h114, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h116 | h116
                      · linarith only [h109, h116, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                      · linarith only [h116, hc45, hlam, hphi, u4ehi2]
                  · linarith only [h113, hc45, hlam, hphi, u4ehi1]
              · linarith only [h109, h110, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h121 | h121
              · linarith only [h109, h121, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h123 | h123
                · linarith only [h103, h123, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h125 | h125
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h126 | h126
                    · linarith only [h123, h125, h126, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h103, h109, h126, hc13, hc34, hlam, hphi]
                  · linarith only [h125, hc45, hlam, hphi, u4ehi1]
          · linarith only [h0, h103, h108, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h131 | h131
      · linarith only [h0, h131, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h133 | h133
        · linarith only [h0, h133, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h135 | h135
          · rcases m.htr 1 2 4 (by decide) (by decide) with h136 | h136
            · rcases m.htr 1 2 5 (by decide) (by decide) with h137 | h137
              · rcases m.htr 1 3 4 (by decide) (by decide) with h138 | h138
                · rcases m.htr 1 4 5 (by decide) (by decide) with h139 | h139
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h140 | h140
                    · linarith only [h135, h140, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h142 | h142
                      · linarith only [h136, h142, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h142, hc45, hlam, hphi, u4ehi2]
                  · linarith only [h139, hc45, hlam, hphi, u4ehi1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h146 | h146
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h147 | h147
                    · linarith only [h138, h146, h147, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h149 | h149
                      · linarith only [h136, h149, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h149, hc45, hlam, hphi, u4ehi2]
                  · linarith only [h146, hc45, hlam, hphi, u4ehi1]
              · linarith only [h136, h137, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h154 | h154
              · linarith only [h136, h154, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h156 | h156
                · linarith only [h135, h136, h156, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h158 | h158
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h159 | h159
                    · linarith only [h103, h156, h159, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h161 | h161
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h162 | h162
                        · rcases h1bigk with h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c | h163c
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [hlam, p163_0]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h0, hlam, p163_0]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h103, hlam, p163_0]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h131, hlam, p163_0]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h133, hlam, p163_0]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h154, h159, h161, hc01, hc34, hlam, hphi, ht12, ht23, p163_1]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [hlam, p163_0]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h103, h154, h159, h161, hc01, hc34, hlam, hphi, ht12, ht23, p163_1]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h136, hlam, p163_1]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h154, hlam, p163_1]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h135, h154, h159, h161, hc01, hc34, hlam, hphi, ht12, ht23, p163_1]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h135, hlam, p163_0]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [hlam, p163_0]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h156, hlam, p163_0]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h135, h154, h159, h161, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p163_1, u5ehi1]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            rcases p163_3 (m.d 0 1) (by simp) with h179 | h179
                            · linarith only [h179, hlam, p163_0]
                            · rcases p163_3 (m.d 1 2) (by simp) with h181 | h181
                              · linarith only [h136, h181, hlam]
                              · linarith only [h0, h181, hlam]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h0, hc01, hc14, hlam, hphi, p163_1]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h103, hc01, hc14, hlam, hphi, p163_1]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [hlam, p163_0]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h133, h136, h159, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p163_1, u5ehi0]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            rcases p163_3 (m.d 0 1) (by simp) with h188 | h188
                            · linarith only [h188, hlam, p163_0]
                            · rcases p163_3 (m.d 1 2) (by simp) with h190 | h190
                              · linarith only [h154, h190, hlam]
                              · linarith only [h0, h190, hlam]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h103, h135, hc01, hc15, hlam, hphi, p163_1]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h103, h136, h158, h159, hc01, hc34, hlam, hphi, ht12, ht23, p163_1]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [h158, hlam, p163_0]
                          · have p163_0 := h163c.1
                            have p163_1 := h163c.2.1
                            have p163_2 := h163c.2.2.1
                            have p163_3 := h163c.2.2.2
                            linarith only [hlam, p163_0]
                        · linarith only [h136, h159, h162, hc45, hlam, hphi, u4ehi1]
                      · linarith only [h136, h158, h161, hlam]
                  · linarith only [h158, hc45, hlam, hphi, u4ehi1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h200 | h200
            · linarith only [h135, h200, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h202 | h202
              · linarith only [h135, h202, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h204 | h204
                · rcases m.htr 1 4 5 (by decide) (by decide) with h205 | h205
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h206 | h206
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h207 | h207
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h208 | h208
                        · linarith only [h204, h208, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h205, h208, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h200, h205, h207, hlam]
                    · linarith only [h0, h135, h206, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h205, hc45, hlam, hphi, u4ehi1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h214 | h214
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h215 | h215
                    · linarith only [h103, h204, h215, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h135, h215, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h214, hc45, hlam, hphi, u4ehi1]

theorem n7l_sAB1_H_R_H_R_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h5ehi := hb5.1
  have h1ehi := hb1.1
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4 | h4
        · linarith only [h2, h4, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h6 | h6
          · linarith only [h1, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
          · linarith only [h6, hc45, hlam, hphi, u4ehi1]
    · linarith only [h0, h1, hc14, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h10 | h10
    · linarith only [h0, h10, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h12 | h12
      · rcases m.htr 1 2 5 (by decide) (by decide) with h13 | h13
        · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
          · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
            · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
              · linarith only [h12, h16, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
              · linarith only [h16, hc45, hlam, hphi, u4ehi2]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h19 | h19
              · linarith only [h12, h19, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
              · linarith only [h19, hc45, hlam, hphi, u4ehi2]
          · linarith only [h10, h14, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
        · linarith only [h0, h13, hc25, hlam, hphi, ht12, u1ehi0]
      · linarith only [h0, h12, hc24, hlam, hphi, ht12, u1ehi0]

theorem n7l_sAB1_H_R_M_IR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h1elo := hb1.1
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  rcases m.htr 1 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi4]
  · linarith only [h0, hc45, hlam, hphi, u4ehi1]

theorem n7l_sAB1_H_R_M_IR_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
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
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 3 4 5 (by decide) (by decide) with h3 | h3
        · rcases h5emax with h4 | h4 | h4 | h4 | h4
          · linarith only [h0, h4, hlam, ht45, u4ehi4]
          · linarith only [h1, h4, hlam, ht45, u4ehi4]
          · linarith only [h2, h4, hlam, ht45, u4ehi4]
          · linarith only [h3, h4, hlam, ht45, u4ehi4]
          · linarith only [h4, hlam, ht45, u4ehi4]
        · linarith only [h0, h3, hc04, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
      · linarith only [h1, h2, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
    · linarith only [h1, hc45, hlam, hphi, u4ehi1]
  · linarith only [h0, hc45, hlam, hphi, u4ehi0]

theorem n7l_sAB1_H_R_M_IR_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h1ehi := hb1.1
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2 | h2
      · linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h4 | h4
        · linarith only [h1, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
        · linarith only [h4, hc45, hlam, hphi, u4ehi1]
    · linarith only [h0, h1, hc14, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h8 | h8
    · linarith only [h0, h8, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
      · rcases m.htr 1 4 5 (by decide) (by decide) with h11 | h11
        · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
          · rcases m.htr 2 4 5 (by decide) (by decide) with h13 | h13
            · linarith only [h10, h13, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
            · linarith only [h13, hc45, hlam, hphi, u4ehi2]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
            · linarith only [h10, h16, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
            · linarith only [h16, hc45, hlam, hphi, u4ehi2]
        · linarith only [h11, h8, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
      · linarith only [h0, h10, hc24, hlam, hphi, ht12, u1ehi0]

theorem n7l_sAB1_H_R_M_LI_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB1_H_R_M_LI_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB1_H_R_M_LI_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB1_H_R_M_LR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB1_H_R_M_LR_L_I (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB1_H_R_M_LR_L_R (m : N7Model)
    (hb4 : CMSig2_7_H_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB1_M_IR_H_L_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB1_M_IR_H_L_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB1_M_IR_H_L_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5elo := hb5.1
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi4, u5elo4]

theorem n7l_sAB1_M_IR_H_R_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc04 := m.hcor 0 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have h5ehi := hb5.1
  have h1elo := hb1.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
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
            · linarith only [h7, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h7, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h10 | h10
            · linarith only [h10, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h10, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h13 | h13
          · rcases p0_3 (m.d 4 5) (by simp) with h14 | h14
            · linarith only [h14, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h14, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h17 | h17
            · linarith only [h17, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h17, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h21 | h21
    · rcases p0_3 (m.d 1 4) (by simp) with h22 | h22
      · linarith only [h22, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3, u4ehi2]
      · rcases p0_3 (m.d 2 4) (by simp) with h24 | h24
        · linarith only [h24, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h26 | h26
          · rcases p0_3 (m.d 4 5) (by simp) with h27 | h27
            · linarith only [h27, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h27, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h30 | h30
            · linarith only [h22, h30, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h30, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h21, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h34 | h34
    · rcases p0_3 (m.d 1 4) (by simp) with h35 | h35
      · linarith only [h35, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3, u4ehi3]
      · rcases p0_3 (m.d 2 4) (by simp) with h37 | h37
        · rcases p0_3 (m.d 3 4) (by simp) with h38 | h38
          · linarith only [h38, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h40 | h40
            · linarith only [h40, hc45, hlam, hphi, p0_1, u4ehi3]
            · linarith only [h40, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h43 | h43
          · linarith only [h43, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h45 | h45
            · linarith only [h35, h45, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h45, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h34, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3, u4ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3, u4ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3, u4ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo3, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h55 | h55
    · linarith only [h55, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h57 | h57
      · linarith only [h57, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3, u4ehi0]
      · rcases p0_3 (m.d 2 4) (by simp) with h59 | h59
        · rcases p0_3 (m.d 3 4) (by simp) with h60 | h60
          · rcases p0_3 (m.d 4 5) (by simp) with h61 | h61
            · linarith only [h61, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h61, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h64 | h64
            · linarith only [h64, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h64, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h59, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h68 | h68
    · rcases p0_3 (m.d 1 4) (by simp) with h69 | h69
      · linarith only [h69, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h71 | h71
        · rcases p0_3 (m.d 3 4) (by simp) with h72 | h72
          · rcases p0_3 (m.d 4 5) (by simp) with h73 | h73
            · linarith only [h73, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h68, h73, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h76 | h76
            · linarith only [h76, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h76, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h71, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h80 | h80
      · linarith only [h80, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h82 | h82
        · rcases p0_3 (m.d 3 4) (by simp) with h83 | h83
          · rcases p0_3 (m.d 4 5) (by simp) with h84 | h84
            · linarith only [h68, h84, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h84, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h87 | h87
            · linarith only [h68, h87, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h87, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h82, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h92 | h92
    · rcases p0_3 (m.d 1 4) (by simp) with h93 | h93
      · linarith only [h93, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3, u4ehi3]
      · rcases p0_3 (m.d 2 4) (by simp) with h95 | h95
        · rcases p0_3 (m.d 3 4) (by simp) with h96 | h96
          · linarith only [h96, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h98 | h98
            · linarith only [h98, hc45, hlam, hphi, p0_1, u4ehi3]
            · linarith only [h92, h98, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h95, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h102 | h102
      · linarith only [h102, h92, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3, u4ehi0]
      · rcases p0_3 (m.d 2 4) (by simp) with h104 | h104
        · rcases p0_3 (m.d 3 4) (by simp) with h105 | h105
          · linarith only [h105, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h107 | h107
            · linarith only [h107, h92, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h107, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h104, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h112 | h112
    · linarith only [h112, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h114 | h114
      · linarith only [h114, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3, u4ehi0]
      · rcases p0_3 (m.d 2 4) (by simp) with h116 | h116
        · rcases p0_3 (m.d 3 4) (by simp) with h117 | h117
          · rcases p0_3 (m.d 4 5) (by simp) with h118 | h118
            · linarith only [h118, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h118, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h117, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h122 | h122
          · rcases p0_3 (m.d 4 5) (by simp) with h123 | h123
            · linarith only [h123, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h123, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h122, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h127 | h127
    · rcases p0_3 (m.d 1 4) (by simp) with h128 | h128
      · linarith only [h128, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h130 | h130
        · rcases p0_3 (m.d 3 4) (by simp) with h131 | h131
          · rcases p0_3 (m.d 4 5) (by simp) with h132 | h132
            · linarith only [h132, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h127, h132, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h131, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h136 | h136
          · rcases p0_3 (m.d 4 5) (by simp) with h137 | h137
            · linarith only [h137, hc45, hlam, hphi, p0_1, u4ehi1]
            · linarith only [h137, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h136, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h141 | h141
      · linarith only [h141, hlam, p0_0]
      · rcases p0_3 (m.d 2 4) (by simp) with h143 | h143
        · rcases p0_3 (m.d 3 4) (by simp) with h144 | h144
          · rcases p0_3 (m.d 4 5) (by simp) with h145 | h145
            · linarith only [h127, h145, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h143, h145, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · linarith only [h144, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h149 | h149
          · rcases p0_3 (m.d 4 5) (by simp) with h150 | h150
            · linarith only [h127, h150, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h150, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h149, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h154 | h154
    · rcases p0_3 (m.d 1 4) (by simp) with h155 | h155
      · linarith only [h155, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3, u4ehi2]
      · rcases p0_3 (m.d 2 4) (by simp) with h157 | h157
        · linarith only [h157, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h159 | h159
          · rcases p0_3 (m.d 4 5) (by simp) with h160 | h160
            · linarith only [h160, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h154, h160, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h159, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h164 | h164
      · linarith only [h154, h164, hlam, hphi, ht01, ht0b, ht45, ht5b, p0_1, u1elo3, u4ehi0]
      · rcases p0_3 (m.d 2 4) (by simp) with h166 | h166
        · linarith only [h166, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h168 | h168
          · rcases p0_3 (m.d 4 5) (by simp) with h169 | h169
            · linarith only [h154, h169, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h169, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h168, hlam, p0_0]
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
    linarith only [hc45, hlam, hphi, p0_1, u4ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u4ehi1]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u4ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u4ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAB1_M_IR_H_R_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have h5ehi := hb5.1
  have h1ehi := hb1.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
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
        · linarith only [h5, hc24, hlam, hphi, ht12, p0_1, u1ehi3]
        · rcases p0_3 (m.d 3 4) (by simp) with h7 | h7
          · linarith only [h7, hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi3]
          · rcases p0_3 (m.d 4 5) (by simp) with h9 | h9
            · linarith only [h9, hc45, hlam, hphi, ht12, ht23, ht34, p0_1, u1ehi3]
            · linarith only [h9, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h2, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h13 | h13
    · rcases p0_3 (m.d 1 4) (by simp) with h14 | h14
      · rcases p0_3 (m.d 2 4) (by simp) with h15 | h15
        · linarith only [h15, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h17 | h17
          · rcases p0_3 (m.d 4 5) (by simp) with h18 | h18
            · linarith only [h18, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h18, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h21 | h21
            · linarith only [h21, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h21, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · rcases p0_3 (m.d 2 4) (by simp) with h24 | h24
        · linarith only [h24, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h26 | h26
          · linarith only [h14, h26, hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi3]
          · rcases p0_3 (m.d 4 5) (by simp) with h28 | h28
            · linarith only [h14, h28, hc45, hlam, hphi, ht12, ht23, ht34, p0_1, u1ehi3]
            · linarith only [h28, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h13, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h32 | h32
    · rcases p0_3 (m.d 1 4) (by simp) with h33 | h33
      · rcases p0_3 (m.d 2 4) (by simp) with h34 | h34
        · rcases p0_3 (m.d 3 4) (by simp) with h35 | h35
          · linarith only [h35, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h37 | h37
            · linarith only [h37, hc45, hlam, hphi, p0_1, u4ehi3]
            · linarith only [h37, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h40 | h40
          · linarith only [h40, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h42 | h42
            · linarith only [h34, h42, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h42, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
      · rcases p0_3 (m.d 2 4) (by simp) with h45 | h45
        · linarith only [h33, h45, hc24, hlam, hphi, ht12, p0_1, u1ehi3]
        · rcases p0_3 (m.d 3 4) (by simp) with h47 | h47
          · linarith only [h47, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h49 | h49
            · linarith only [h33, h49, hc45, hlam, hphi, ht12, ht23, ht34, p0_1, u1ehi3]
            · linarith only [h49, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
    · linarith only [h32, hlam, p0_0]
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
        · rcases p0_3 (m.d 3 4) (by simp) with h58 | h58
          · rcases p0_3 (m.d 4 5) (by simp) with h59 | h59
            · linarith only [h59, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h59, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h62 | h62
            · linarith only [h62, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h62, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h65 | h65
          · rcases p0_3 (m.d 4 5) (by simp) with h66 | h66
            · linarith only [h66, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h66, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h69 | h69
            · linarith only [h69, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h69, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
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
    rcases p0_3 (m.d 0 4) (by simp) with h74 | h74
    · rcases p0_3 (m.d 1 4) (by simp) with h75 | h75
      · rcases p0_3 (m.d 2 4) (by simp) with h76 | h76
        · linarith only [h76, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h78 | h78
          · rcases p0_3 (m.d 4 5) (by simp) with h79 | h79
            · linarith only [h79, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h74, h79, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h82 | h82
            · linarith only [h82, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h82, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h75, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h86 | h86
      · rcases p0_3 (m.d 2 4) (by simp) with h87 | h87
        · linarith only [h87, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h89 | h89
          · rcases p0_3 (m.d 4 5) (by simp) with h90 | h90
            · linarith only [h74, h90, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h90, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h93 | h93
            · linarith only [h74, h93, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h93, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h86, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h97 | h97
    · rcases p0_3 (m.d 1 4) (by simp) with h98 | h98
      · rcases p0_3 (m.d 2 4) (by simp) with h99 | h99
        · rcases p0_3 (m.d 3 4) (by simp) with h100 | h100
          · linarith only [h100, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h102 | h102
            · linarith only [h102, hc45, hlam, hphi, p0_1, u4ehi3]
            · linarith only [h102, h97, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h105 | h105
          · linarith only [h105, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h107 | h107
            · linarith only [h107, h99, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h107, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h98, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h111 | h111
      · rcases p0_3 (m.d 2 4) (by simp) with h112 | h112
        · rcases p0_3 (m.d 3 4) (by simp) with h113 | h113
          · linarith only [h113, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h115 | h115
            · linarith only [h115, h97, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h115, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · rcases p0_3 (m.d 3 4) (by simp) with h118 | h118
          · linarith only [h118, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h120 | h120
            · linarith only [h120, h97, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h120, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
      · linarith only [h111, hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h125 | h125
    · linarith only [h125, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h127 | h127
      · rcases p0_3 (m.d 2 4) (by simp) with h128 | h128
        · rcases p0_3 (m.d 3 4) (by simp) with h129 | h129
          · rcases p0_3 (m.d 4 5) (by simp) with h130 | h130
            · linarith only [h130, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h130, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
          · rcases p0_3 (m.d 4 5) (by simp) with h133 | h133
            · linarith only [h133, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h133, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
        · linarith only [h128, hlam, p0_0]
      · linarith only [h127, hc24, hlam, hphi, ht12, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht12, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h140 | h140
    · rcases p0_3 (m.d 1 4) (by simp) with h141 | h141
      · rcases p0_3 (m.d 2 4) (by simp) with h142 | h142
        · rcases p0_3 (m.d 3 4) (by simp) with h143 | h143
          · linarith only [h143, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h145 | h145
            · linarith only [h145, hc45, hlam, hphi, p0_1, u4ehi3]
            · linarith only [h140, h145, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h142, hlam, p0_0]
      · linarith only [h141, hc24, hlam, hphi, ht12, p0_1, u1ehi3]
    · rcases p0_3 (m.d 1 4) (by simp) with h150 | h150
      · rcases p0_3 (m.d 2 4) (by simp) with h151 | h151
        · rcases p0_3 (m.d 3 4) (by simp) with h152 | h152
          · linarith only [h152, hlam, p0_0]
          · rcases p0_3 (m.d 4 5) (by simp) with h154 | h154
            · linarith only [h140, h154, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h150, h154, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
        · linarith only [h151, hlam, p0_0]
      · linarith only [h150, hc24, hlam, hphi, ht12, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p0_1, u5ehi4]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h160 | h160
    · linarith only [h160, hlam, p0_0]
    · rcases p0_3 (m.d 1 4) (by simp) with h162 | h162
      · rcases p0_3 (m.d 2 4) (by simp) with h163 | h163
        · rcases p0_3 (m.d 3 4) (by simp) with h164 | h164
          · rcases p0_3 (m.d 4 5) (by simp) with h165 | h165
            · linarith only [h165, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h162, h165, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h164, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h169 | h169
          · rcases p0_3 (m.d 4 5) (by simp) with h170 | h170
            · linarith only [h170, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h170, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p0_1, u5ehi4]
          · linarith only [h169, hlam, p0_0]
      · linarith only [h162, hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    rcases p0_3 (m.d 0 4) (by simp) with h176 | h176
    · rcases p0_3 (m.d 1 4) (by simp) with h177 | h177
      · rcases p0_3 (m.d 2 4) (by simp) with h178 | h178
        · linarith only [h178, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h180 | h180
          · rcases p0_3 (m.d 4 5) (by simp) with h181 | h181
            · linarith only [h181, hc45, hlam, hphi, p0_1, u4ehi2]
            · linarith only [h176, h181, hc04, hlam, hphi, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h180, hlam, p0_0]
      · linarith only [h177, hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi3]
    · rcases p0_3 (m.d 1 4) (by simp) with h186 | h186
      · rcases p0_3 (m.d 2 4) (by simp) with h187 | h187
        · linarith only [h187, hlam, p0_0]
        · rcases p0_3 (m.d 3 4) (by simp) with h189 | h189
          · rcases p0_3 (m.d 4 5) (by simp) with h190 | h190
            · linarith only [h176, h190, hc45, hlam, hphi, p0_1, u4ehi0]
            · linarith only [h186, h190, hc14, hlam, hphi, ht01, ht0b, ht5b, p0_1, u5ehi4]
          · linarith only [h189, hlam, p0_0]
      · linarith only [h186, hc34, hlam, hphi, ht12, ht23, p0_1, u1ehi3]
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
    linarith only [hc45, hlam, hphi, p0_1, u4ehi0]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, ht12, ht23, ht34, p0_1, u1ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u4ehi2]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hc45, hlam, hphi, p0_1, u4ehi3]
  · have p0_0 := h0c.1
    have p0_1 := h0c.2.1
    have p0_2 := h0c.2.2.1
    have p0_3 := h0c.2.2.2
    linarith only [hlam, p0_0]

theorem n7l_sAB1_M_IR_M_LI_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5elo := hb5.1
  have h5emax := hb5.2.2.1
  have h1elo := hb1.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 3 4 5 (by decide) (by decide) with h3 | h3
        · rcases h5emax with h4 | h4 | h4 | h4 | h4
          · linarith only [h0, h4, hlam, ht45, u4ehi4]
          · linarith only [h1, h4, hlam, ht45, u4ehi4]
          · linarith only [h2, h4, hlam, ht45, u4ehi4]
          · linarith only [h3, h4, hlam, ht45, u4ehi4]
          · linarith only [h4, hlam, ht45, u4ehi4]
        · linarith only [h1, h3, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi3]
      · linarith only [h1, h2, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi2]
    · linarith only [h0, h1, hlam, hphi, ht45, u4ehi1, u5elo0]
  · linarith only [h0, hlam, hphi, ht45, u4ehi0, u5elo4]

theorem n7l_sAB1_M_IR_M_LI_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5elo := hb5.1
  have h5emax := hb5.2.2.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 4 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 3 4 5 (by decide) (by decide) with h3 | h3
        · rcases h5emax with h4 | h4 | h4 | h4 | h4
          · linarith only [h0, h4, hlam, ht45, u4ehi4]
          · linarith only [h1, h4, hlam, ht45, u4ehi4]
          · linarith only [h2, h4, hlam, ht45, u4ehi4]
          · linarith only [h3, h4, hlam, ht45, u4ehi4]
          · linarith only [h4, hlam, ht45, u4ehi4]
        · linarith only [h0, h3, hlam, hphi, ht45, u4ehi3, u5elo0]
      · linarith only [h0, h2, hlam, hphi, ht45, u4ehi2, u5elo0]
    · linarith only [h0, h1, hlam, hphi, ht45, u4ehi1, u5elo0]
  · linarith only [h0, hlam, hphi, ht45, u4ehi0, u5elo4]

theorem n7l_sAB1_M_IR_M_LI_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5elo := hb5.1
  have h5emax := hb5.2.2.1
  have h1ehi := hb1.1
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 2 4 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 3 4 5 (by decide) (by decide) with h2 | h2
      · rcases h5emax with h3 | h3 | h3 | h3 | h3
        · linarith only [h0, h3, hlam, ht12, ht23, ht34, ht45, u1ehi4]
        · linarith only [h3, hlam, ht12, ht23, ht34, ht45, u1ehi4]
        · linarith only [h1, h3, hlam, ht45, u4ehi4]
        · linarith only [h2, h3, hlam, ht45, u4ehi4]
        · linarith only [h3, hlam, ht45, u4ehi4]
      · linarith only [h1, h2, hlam, hphi, ht45, u4ehi3, u5elo2]
    · linarith only [h1, hlam, hphi, ht45, u4ehi2, u5elo4]
  · linarith only [h0, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]

theorem n7l_sAB1_M_IR_M_LR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h1elo := hb1.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h7, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                  · linarith only [h2, h7, h9, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
                  · linarith only [h6, h9, hc23, hlam, hphi, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h12 | h12
                · linarith only [h0, h12, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h14 | h14
                  · linarith only [h1, h14, h6, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h16 | h16
                    · linarith only [h1, h16, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h18 | h18
                      · linarith only [h16, h18, h2, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi8]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h20 | h20
                        · linarith only [h2, h20, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi9]
                        · linarith only [h20, hlam, hphi, ht45, u4ehi1, u5elo4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
              · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
                · linarith only [h0, h24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h26 | h26
                  · linarith only [h2, h24, h26, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi7]
                  · linarith only [h0, h23, h26, h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h29 | h29
                · linarith only [h0, h29, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h31 | h31
                  · linarith only [h1, h23, h31, h5, hlam, hphi, u5ehi7, u5elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h33 | h33
                    · linarith only [h1, h33, h5, hlam, hphi, ht45, u4ehi3, u5elo3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h35 | h35
                      · linarith only [h1, h35, h5, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h37 | h37
                        · linarith only [h2, h37, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi9]
                        · linarith only [h37, hlam, hphi, ht45, u4ehi1, u5elo4]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h40 | h40
            · rcases m.htr 1 2 3 (by decide) (by decide) with h41 | h41
              · linarith only [h0, h4, h41, hc23, hlam, hphi, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h43 | h43
                · linarith only [h0, h4, h43, hlam, hphi, ht45, u4ehi2, u5elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h45 | h45
                  · linarith only [h0, h4, h45, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h47 | h47
                    · linarith only [h1, h47, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h49 | h49
                      · linarith only [h2, h47, h49, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi8]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h51 | h51
                        · linarith only [h2, h51, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi9]
                        · linarith only [h51, hlam, hphi, ht45, u4ehi1, u5elo4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h54 | h54
              · linarith only [h0, h4, h54, hc23, hlam, hphi, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h56 | h56
                · linarith only [h1, h40, h54, h56, hlam, hphi, ht45, u4ehi2, u5elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h58 | h58
                  · linarith only [h1, h4, h40, h54, h58, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h60 | h60
                    · linarith only [h1, h40, h60, hlam, hphi, ht45, u4ehi3, u5elo3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h62 | h62
                      · linarith only [h1, h40, h62, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h64 | h64
                        · linarith only [h2, h64, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi4]
                        · linarith only [h64, hlam, hphi, ht45, u4ehi1, u5elo4]
        · linarith only [h2, h3, hlam, hphi, ht45, u4ehi0, u5elo1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h68 | h68
        · linarith only [h2, h68, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi6]
        · linarith only [h1, h68, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h71 | h71
      · linarith only [h1, h71, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h73 | h73
        · linarith only [h1, h73, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi6]
        · linarith only [h0, h73, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h76 | h76
    · rcases m.htr 0 1 4 (by decide) (by decide) with h77 | h77
      · linarith only [h0, h77, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h79 | h79
        · linarith only [h0, h79, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi6]
        · linarith only [h76, h79, hc13, hlam, hphi, ht34, ht45, u5elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h82 | h82
      · linarith only [h0, h82, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h84 | h84
        · linarith only [h0, h84, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi6]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h86 | h86
          · rcases m.htr 0 3 5 (by decide) (by decide) with h87 | h87
            · rcases m.htr 1 2 3 (by decide) (by decide) with h88 | h88
              · rcases m.htr 1 2 4 (by decide) (by decide) with h89 | h89
                · rcases m.htr 1 2 5 (by decide) (by decide) with h90 | h90
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h91 | h91
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h92 | h92
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h93 | h93
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h94 | h94
                          · linarith only [h88, h94, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h96 | h96
                            · linarith only [h88, h91, h94, h96, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi8]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h98 | h98
                              · linarith only [h89, h98, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi4]
                              · linarith only [h93, h98, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi2]
                        · linarith only [h93, hlam, hphi, ht45, u4ehi1, u5elo4]
                      · linarith only [h87, h91, h92, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h103 | h103
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h104 | h104
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h105 | h105
                          · linarith only [h105, h76, h87, h91, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h107 | h107
                            · linarith only [h105, h107, h89, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi8]
                            · linarith only [h107, h76, h87, h91, hc23, hc34, hlam, hphi]
                        · linarith only [h104, hlam, hphi, ht45, u4ehi1, u5elo4]
                      · linarith only [h103, h76, h87, hlam]
                  · linarith only [h86, h89, h90, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h113 | h113
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h114 | h114
                    · linarith only [h114, h88, h89, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h116 | h116
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h117 | h117
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h118 | h118
                          · linarith only [h114, h118, h76, h87, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h120 | h120
                            · linarith only [h118, h120, h88, h89, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi8]
                            · linarith only [h118, h120, h76, h87, h88, h89, hc23, hc34, hlam, hphi]
                        · linarith only [h117, hlam, hphi, ht45, u4ehi1, u5elo4]
                      · linarith only [h116, h76, h87, hlam]
                  · linarith only [h113, h76, h86, h87, h88, hc02, hlam, hphi, ht0b, ht5b, u5ehi8]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h126 | h126
                · rcases m.htr 1 2 5 (by decide) (by decide) with h127 | h127
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h128 | h128
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h129 | h129
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h130 | h130
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h131 | h131
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h132 | h132
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h133 | h133
                              · linarith only [h126, h133, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi4]
                              · linarith only [h133, hlam, hphi, ht45, u4ehi2, u5elo4]
                            · linarith only [h126, h132, h87, h88, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                          · linarith only [h126, h130, h131, h88, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                        · linarith only [h130, hlam, hphi, ht45, u4ehi1, u5elo4]
                      · linarith only [h129, h76, h87, hlam]
                    · linarith only [h126, h128, h88, hlam]
                  · linarith only [h0, h127, h86, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h142 | h142
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h143 | h143
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h144 | h144
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h145 | h145
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h146 | h146
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h147 | h147
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h148 | h148
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h149 | h149
                                · linarith only [h143, h149, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi9]
                                · linarith only [h149, hlam, hphi, ht45, u4ehi3, u5elo4]
                              · linarith only [h143, h145, h148, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi2]
                            · linarith only [h0, h147, h86, h88, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                          · linarith only [h0, h146, h86, h88, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                        · linarith only [h145, hlam, hphi, ht45, u4ehi1, u5elo4]
                      · linarith only [h144, h76, h87, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h157 | h157
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h158 | h158
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h159 | h159
                          · linarith only [h143, h159, h76, h87, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                          · linarith only [h0, h159, h86, h88, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                        · linarith only [h0, h143, h158, h86, h88, hlam, hphi, u5ehi7, u5elo4]
                      · linarith only [h0, h157, h86, h87, h88, hc03, hlam, hphi, ht0b, ht5b, u5ehi7]
                  · linarith only [h0, h142, h86, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h165 | h165
              · rcases m.htr 1 2 4 (by decide) (by decide) with h166 | h166
                · rcases m.htr 1 2 5 (by decide) (by decide) with h167 | h167
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h168 | h168
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h169 | h169
                      · linarith only [h165, h169, h76, h87, hc01, hlam, hphi, u1elo1]
                      · linarith only [h168, h169, hlam, hphi, ht45, u4ehi1, u5elo3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h172 | h172
                      · linarith only [h172, h76, h87, hc01, hlam, hphi, u1elo2]
                      · linarith only [h172, h76, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · linarith only [h166, h167, h86, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h176 | h176
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h177 | h177
                    · linarith only [h165, h166, h177, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h179 | h179
                      · linarith only [h165, h179, h76, h87, hc01, hlam, hphi, u1elo1]
                      · linarith only [h179, h76, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · linarith only [h165, h176, hc23, hlam, hphi, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h183 | h183
                · rcases m.htr 1 2 5 (by decide) (by decide) with h184 | h184
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h185 | h185
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h186 | h186
                      · linarith only [h186, h76, h87, hc01, hlam, hphi, u1elo2]
                      · linarith only [h185, h186, hlam, hphi, ht45, u4ehi3, u5elo3]
                    · linarith only [h165, h183, h185, hlam]
                  · linarith only [h0, h184, h86, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h191 | h191
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h192 | h192
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h193 | h193
                      · linarith only [h193, h76, h87, hc01, hlam, hphi, u1elo2]
                      · linarith only [h192, h193, hlam, hphi, ht45, u4ehi3, u5elo3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h196 | h196
                      · linarith only [h196, h76, h87, hc01, hlam, hphi, u1elo2]
                      · linarith only [h196, h76, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                  · linarith only [h0, h191, h86, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h200 | h200
            · rcases m.htr 1 2 3 (by decide) (by decide) with h201 | h201
              · rcases m.htr 1 2 4 (by decide) (by decide) with h202 | h202
                · rcases m.htr 1 2 5 (by decide) (by decide) with h203 | h203
                  · linarith only [h0, h203, h86, hc01, hlam, hphi, u1elo1]
                  · linarith only [h202, h203, hlam, hphi, ht45, u4ehi1, u5elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h206 | h206
                  · linarith only [h0, h206, h86, hc01, hlam, hphi, u1elo1]
                  · linarith only [h201, h206, hc23, hlam, hphi, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h209 | h209
                · rcases m.htr 1 2 5 (by decide) (by decide) with h210 | h210
                  · linarith only [h0, h210, h86, hc01, hlam, hphi, u1elo1]
                  · linarith only [h209, h210, hlam, hphi, ht45, u4ehi1, u5elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h213 | h213
                  · linarith only [h0, h213, h86, hc01, hlam, hphi, u1elo1]
                  · linarith only [h0, h213, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h216 | h216
              · rcases m.htr 1 2 4 (by decide) (by decide) with h217 | h217
                · rcases m.htr 1 2 5 (by decide) (by decide) with h218 | h218
                  · linarith only [h0, h218, h86, hc01, hlam, hphi, u1elo1]
                  · linarith only [h217, h218, hlam, hphi, ht45, u4ehi1, u5elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h221 | h221
                  · linarith only [h0, h221, h86, hc01, hlam, hphi, u1elo1]
                  · linarith only [h216, h221, hc23, hlam, hphi, ht34, ht45, u5elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h224 | h224
                · rcases m.htr 1 2 5 (by decide) (by decide) with h225 | h225
                  · linarith only [h0, h225, h86, hc01, hlam, hphi, u1elo1]
                  · linarith only [h224, h225, hlam, hphi, ht45, u4ehi1, u5elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h228 | h228
                  · linarith only [h0, h228, h86, hc01, hlam, hphi, u1elo1]
                  · linarith only [h0, h228, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]

theorem n7l_sAB1_M_IR_M_LR_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h1ehi := hb1.1
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h3, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h8 | h8
                · linarith only [h0, h3, h4, h6, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h10 | h10
                  · linarith only [h0, h10, h3, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
                  · linarith only [h10, h6, hc23, hlam, hphi, ht34, ht45, u5elo4]
            · linarith only [h4, h5, hlam, hphi, ht45, u4ehi1, u5elo3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
            · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
              · linarith only [h14, h15, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
                · linarith only [h0, h17, h3, hc01, hlam, hphi, ht0b, ht5b, u5ehi8]
                · linarith only [h14, h17, h4, hc23, hc34, hlam, hphi]
            · linarith only [h14, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h21 | h21
          · rcases m.htr 1 3 5 (by decide) (by decide) with h22 | h22
            · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
              · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
                · rcases m.htr 3 4 5 (by decide) (by decide) with h25 | h25
                  · linarith only [h1, h21, h25, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h25, hlam, hphi, ht45, u4ehi3, u5elo4]
                · linarith only [h2, h22, h24, h3, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
              · linarith only [h23, h3, hc34, hlam, hphi, ht12, ht23, u1ehi1]
            · linarith only [h21, h22, hlam, hphi, ht45, u4ehi3, u5elo3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h31 | h31
            · rcases m.htr 2 3 4 (by decide) (by decide) with h32 | h32
              · linarith only [h21, h31, h32, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
              · linarith only [h3, h32, hc34, hlam, hphi, ht12, ht23, u1ehi1]
            · linarith only [h31, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
      · linarith only [h2, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h38 | h38
    · linarith only [h0, h38, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h40 | h40
      · linarith only [h0, h40, hc12, hlam, hphi, u1ehi4]
      · linarith only [h40, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]

theorem n7l_sAB1_M_LI_H_I_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h1elo := hb1.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
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
            · rcases m.htr 0 1 2 (by decide) (by decide) with h11 | h11
              · rcases m.htr 0 1 4 (by decide) (by decide) with h12 | h12
                · linarith only [h12, h6, hlam]
                · linarith only [h11, h12, hc12, hlam, hphi, ht23, ht34, u4elo1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h15 | h15
                · linarith only [h15, h6, hlam]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h17 | h17
                  · linarith only [h17, h7, hlam]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h19 | h19
                    · linarith only [h19, h8, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h21 | h21
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h22 | h22
                        · linarith only [h11, h17, h22, hc01, hlam, hphi, u1elo1]
                        · linarith only [h21, h22, hc23, hlam, hphi, ht34, u4elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h25 | h25
                        · linarith only [h17, h25, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
                        · linarith only [h11, h25, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
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
            · rcases m.htr 0 1 2 (by decide) (by decide) with h42 | h42
              · rcases m.htr 0 1 4 (by decide) (by decide) with h43 | h43
                · linarith only [h43, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0]
                · linarith only [h36, h43, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h46 | h46
                · linarith only [h42, h46, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
                · linarith only [h36, h46, hlam]
          · linarith only [h39, hc34, hlam, hphi, p0_1, u4elo1]
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
    rcases p0_3 (m.d 0 4) (by simp) with h57 | h57
    · rcases p0_3 (m.d 1 4) (by simp) with h58 | h58
      · rcases p0_3 (m.d 2 4) (by simp) with h59 | h59
        · rcases p0_3 (m.d 3 4) (by simp) with h60 | h60
          · rcases p0_3 (m.d 4 5) (by simp) with h61 | h61
            · linarith only [h61, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h63 | h63
              · rcases m.htr 0 1 4 (by decide) (by decide) with h64 | h64
                · linarith only [h58, h64, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0]
                · linarith only [h63, h64, hc12, hlam, hphi, ht23, ht34, u4elo1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h67 | h67
                · linarith only [h58, h63, h67, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h69 | h69
                  · linarith only [h63, h69, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
                  · linarith only [h57, h69, hlam]
          · linarith only [h60, hc34, hlam, hphi, p0_1, u4elo2]
        · linarith only [h59, hlam, p0_0]
      · linarith only [h58, hc14, hlam, hphi, p0_1, u4elo2]
    · linarith only [h57, hc04, hlam, hphi, p0_1, u4elo2]
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
    rcases p0_3 (m.d 0 4) (by simp) with h80 | h80
    · rcases p0_3 (m.d 1 4) (by simp) with h81 | h81
      · rcases p0_3 (m.d 2 4) (by simp) with h82 | h82
        · rcases p0_3 (m.d 3 4) (by simp) with h83 | h83
          · rcases p0_3 (m.d 4 5) (by simp) with h84 | h84
            · linarith only [h84, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h86 | h86
              · rcases m.htr 0 1 4 (by decide) (by decide) with h87 | h87
                · linarith only [h81, h87, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0]
                · linarith only [h86, h87, hc12, hlam, hphi, ht23, ht34, u4elo1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h90 | h90
                · linarith only [h81, h86, h90, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h92 | h92
                  · linarith only [h82, h86, h92, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
                  · rcases m.htr 0 3 4 (by decide) (by decide) with h94 | h94
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h95 | h95
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h96 | h96
                        · linarith only [h86, h92, h96, hc01, hlam, hphi, u1elo1]
                        · linarith only [h95, h96, hc23, hlam, hphi, ht34, u4elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h99 | h99
                        · linarith only [h86, h92, h99, hc01, hlam, hphi, u1elo1]
                        · linarith only [h86, h99, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                    · linarith only [h80, h94, hlam]
          · linarith only [h83, hlam, p0_0]
        · linarith only [h82, hc24, hlam, hphi, p0_1, u4elo3]
      · linarith only [h81, hc14, hlam, hphi, p0_1, u4elo3]
    · linarith only [h80, hc04, hlam, hphi, p0_1, u4elo3]
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

theorem n7l_sAB1_M_LI_H_I_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have h1ehi := hb1.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 3 4 5 (by decide) (by decide) with h6 | h6
              · rcases h4bigk with h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c | h7c
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hc14, hlam, hphi, p7_1, u4elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hc24, hlam, hphi, p7_1, u4elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p7_1, u4elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  rcases p7_3 (m.d 0 4) (by simp) with h12 | h12
                  · rcases p7_3 (m.d 1 4) (by simp) with h13 | h13
                    · linarith only [h1, h13, hlam]
                    · linarith only [h13, h4, hlam]
                  · linarith only [h12, hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h1, hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h5, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p7_1, u4elo1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h1, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p7_1, u4elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  rcases p7_3 (m.d 0 4) (by simp) with h21 | h21
                  · rcases p7_3 (m.d 1 4) (by simp) with h22 | h22
                    · rcases p7_3 (m.d 2 4) (by simp) with h23 | h23
                      · linarith only [h2, h23, hlam]
                      · linarith only [h23, h5, h6, hlam]
                    · linarith only [h22, hlam, p7_0]
                  · linarith only [h1, h21, h5, h6, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo2]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h1, h2, hlam, p7_1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h2, hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h1, h2, hc34, hlam, hphi, p7_1, u4elo0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  rcases p7_3 (m.d 0 4) (by simp) with h32 | h32
                  · rcases p7_3 (m.d 1 4) (by simp) with h33 | h33
                    · rcases p7_3 (m.d 2 4) (by simp) with h34 | h34
                      · rcases p7_3 (m.d 3 4) (by simp) with h35 | h35
                        · linarith only [h35, h5, hlam]
                        · linarith only [h35, h6, hlam]
                      · linarith only [h34, hlam, p7_0]
                    · linarith only [h33, h4, hlam]
                  · linarith only [h1, h32, h6, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo3]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h1, h2, h5, hlam, p7_1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h3, hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h5, hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h0, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p7_1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hc04, hlam, hphi, p7_1, u4elo4]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h4, hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h5, h6, hlam, p7_1]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [h6, hlam, p7_0]
                · have p7_0 := h7c.1
                  have p7_1 := h7c.2.1
                  have p7_2 := h7c.2.2.1
                  have p7_3 := h7c.2.2.2
                  linarith only [hlam, p7_0]
              · linarith only [h1, h4, h6, hc34, hlam, hphi, u4elo0]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h52 | h52
              · rcases h4bigk with h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c
                · have p53_0 := h53c.1
                  have p53_1 := h53c.2.1
                  have p53_2 := h53c.2.2.1
                  have p53_3 := h53c.2.2.2
                  linarith only [hlam, p53_0]
                · have p53_0 := h53c.1
                  have p53_1 := h53c.2.1
                  have p53_2 := h53c.2.2.1
                  have p53_3 := h53c.2.2.2
                  linarith only [hc14, hlam, hphi, p53_1, u4elo0]
                · have p53_0 := h53c.1
                  have p53_1 := h53c.2.1
                  have p53_2 := h53c.2.2.1
                  have p53_3 := h53c.2.2.2
                  linarith only [h5, hc23, hlam, hphi, ht34, p53_1, u4elo0]
                · have p53_0 := h53c.1
                  have p53_1 := h53c.2.1
                  have p53_2 := h53c.2.2.1
                  have p53_3 := h53c.2.2.2
                  linarith only [h5, hc23, hlam, hphi, ht34, p53_1, u4elo0]
                · have p53_0 := h53c.1
                  have p53_1 := h53c.2.1
                  have p53_2 := h53c.2.2.1
                  have p53_3 := h53c.2.2.2
                  rcases p53_3 (m.d 0 4) (by simp) with h58 | h58
                  · rcases p53_3 (m.d 1 4) (by simp) with h59 | h59
                    · linarith only [h1, h59, hlam]
                    · linarith only [h4, h59, hlam]
                  · linarith only [h58, hlam, p53_0]
                · have p53_0 := h53c.1
                  have p53_1 := h53c.2.1
                  have p53_2 := h53c.2.2.1
                  have p53_3 := h53c.2.2.2
                  linarith only [h1, hlam, p53_0]
                · have p53_0 := h53c.1
                  have p53_1 := h53c.2.1
                  have p53_2 := h53c.2.2.1
                  have p53_3 := h53c.2.2.2
                  linarith only [hlam, p53_0]
                · have p53_0 := h53c.1
                  have p53_1 := h53c.2.1
                  have p53_2 := h53c.2.2.1
                  have p53_3 := h53c.2.2.2
                  linarith only [h5, hc23, hlam, hphi, ht34, p53_1, u4elo1]
                · have p53_0 := h53c.1
                  have p53_1 := h53c.2.1
                  have p53_2 := h53c.2.2.1
                  have p53_3 := h53c.2.2.2
                  linarith only [h1, h5, hc23, hlam, hphi, ht34, p53_1, u4elo0]
                · have p53_0 := h53c.1
                  have p53_1 := h53c.2.1
                  have p53_2 := h53c.2.2.1
                  have p53_3 := h53c.2.2.2
                  rcases p53_3 (m.d 0 4) (by simp) with h67 | h67
                  · rcases p53_3 (m.d 1 4) (by simp) with h68 | h68
                    · rcases p53_3 (m.d 2 4) (by simp) with h69 | h69
                      · linarith only [h2, h69, hlam]
                      · linarith only [h1, h5, h69, hc23, hlam, hphi, ht34, p53_1, u4elo0]
                    · linarith only [h68, hlam, p53_0]
                  · linarith only [h1, h67, hlam, p53_1]
                · have p53_0 := h53c.1
                  have p53_1 := h53c.2.1
                  have p53_2 := h53c.2.2.1
                  have p53_3 := h53c.2.2.2
                  linarith only [hc04, hlam, hphi, p53_1, u4elo2]
                · have p53_0 := h53c.1
                  have p53_1 := h53c.2.1
                  have p53_2 := h53c.2.2.1
                  have p53_3 := h53c.2.2.2
                  linarith only [h2, hlam, p53_0]
                · have p53_0 := h53c.1
                  have p53_1 := h53c.2.1
                  have p53_2 := h53c.2.2.1
                  have p53_3 := h53c.2.2.2
                  linarith only [hlam, p53_0]
                · have p53_0 := h53c.1
                  have p53_1 := h53c.2.1
                  have p53_2 := h53c.2.2.1
                  have p53_3 := h53c.2.2.2
                  linarith only [h5, hlam, p53_1]
                · have p53_0 := h53c.1
                  have p53_1 := h53c.2.1
                  have p53_2 := h53c.2.2.1
                  have p53_3 := h53c.2.2.2
                  linarith only [h0, h3, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p53_1]
                · have p53_0 := h53c.1
                  have p53_1 := h53c.2.1
                  have p53_2 := h53c.2.2.1
                  have p53_3 := h53c.2.2.2
                  linarith only [h1, h3, hlam, p53_1]
                · have p53_0 := h53c.1
                  have p53_1 := h53c.2.1
                  have p53_2 := h53c.2.2.1
                  have p53_3 := h53c.2.2.2
                  linarith only [h3, hlam, p53_0]
                · have p53_0 := h53c.1
                  have p53_1 := h53c.2.1
                  have p53_2 := h53c.2.2.1
                  have p53_3 := h53c.2.2.2
                  linarith only [h0, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p53_1]
                · have p53_0 := h53c.1
                  have p53_1 := h53c.2.1
                  have p53_2 := h53c.2.2.1
                  have p53_3 := h53c.2.2.2
                  linarith only [hlam, p53_0]
                · have p53_0 := h53c.1
                  have p53_1 := h53c.2.1
                  have p53_2 := h53c.2.2.1
                  have p53_3 := h53c.2.2.2
                  linarith only [h0, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p53_1]
                · have p53_0 := h53c.1
                  have p53_1 := h53c.2.1
                  have p53_2 := h53c.2.2.1
                  have p53_3 := h53c.2.2.2
                  linarith only [hc04, hlam, hphi, p53_1, u4elo4]
                · have p53_0 := h53c.1
                  have p53_1 := h53c.2.1
                  have p53_2 := h53c.2.2.1
                  have p53_3 := h53c.2.2.2
                  linarith only [h4, hlam, p53_0]
                · have p53_0 := h53c.1
                  have p53_1 := h53c.2.1
                  have p53_2 := h53c.2.2.1
                  have p53_3 := h53c.2.2.2
                  linarith only [h0, h3, h5, h52, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p53_1]
                · have p53_0 := h53c.1
                  have p53_1 := h53c.2.1
                  have p53_2 := h53c.2.2.1
                  have p53_3 := h53c.2.2.2
                  linarith only [h52, hlam, p53_0]
                · have p53_0 := h53c.1
                  have p53_1 := h53c.2.1
                  have p53_2 := h53c.2.2.1
                  have p53_3 := h53c.2.2.2
                  linarith only [hlam, p53_0]
              · linarith only [h1, h4, h52, hc34, hlam, hphi, u4elo0]
          · linarith only [h4, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
        · linarith only [h3, hlam, hphi, ht12, ht23, ht34, u1ehi2, u4elo3]
      · linarith only [h2, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo2]
    · linarith only [h1, hlam, hphi, ht12, ht23, ht34, u1ehi0, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h94 | h94
    · linarith only [h0, h94, hc13, hlam, hphi, u1ehi3]
    · linarith only [h94, hlam, hphi, ht12, ht23, ht34, u1ehi0, u4elo1]

theorem n7l_sAB1_M_LI_H_L_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
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
  have h1elo := hb1.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
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
            · rcases m.htr 0 1 2 (by decide) (by decide) with h11 | h11
              · rcases m.htr 0 1 3 (by decide) (by decide) with h12 | h12
                · rcases m.htr 0 1 4 (by decide) (by decide) with h13 | h13
                  · linarith only [h13, h6, hlam]
                  · linarith only [h11, h13, hc12, hlam, hphi, ht23, ht34, u4elo1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h16 | h16
                  · linarith only [h16, h6, hlam]
                  · linarith only [h11, h16, hc12, hlam, hphi, ht23, ht34, u4elo1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h19 | h19
                · rcases m.htr 0 1 4 (by decide) (by decide) with h20 | h20
                  · linarith only [h20, h6, hlam]
                  · linarith only [h19, h20, hc13, hlam, hphi, ht34, u4elo1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h23 | h23
                  · linarith only [h23, h6, hlam]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h25 | h25
                    · linarith only [h25, h7, hlam]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h27 | h27
                      · linarith only [h27, h8, hlam]
                      · rcases m.htr 1 2 3 (by decide) (by decide) with h29 | h29
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h30 | h30
                          · linarith only [h11, h25, h30, hc01, hlam, hphi, u1elo1]
                          · linarith only [h29, h30, hc23, hlam, hphi, ht34, u4elo2]
                        · rcases m.htr 1 2 4 (by decide) (by decide) with h33 | h33
                          · linarith only [h25, h33, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
                          · linarith only [h11, h33, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
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
            · rcases m.htr 0 1 2 (by decide) (by decide) with h50 | h50
              · rcases m.htr 0 1 3 (by decide) (by decide) with h51 | h51
                · rcases m.htr 0 1 4 (by decide) (by decide) with h52 | h52
                  · linarith only [h52, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0]
                  · linarith only [h44, h52, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h55 | h55
                  · linarith only [h51, h55, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo2]
                  · linarith only [h44, h55, hlam]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h58 | h58
                · rcases m.htr 0 1 4 (by decide) (by decide) with h59 | h59
                  · linarith only [h50, h59, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
                  · linarith only [h44, h59, hlam]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h62 | h62
                  · linarith only [h50, h62, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
                  · linarith only [h44, h62, hlam]
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
    rcases p0_3 (m.d 0 4) (by simp) with h73 | h73
    · rcases p0_3 (m.d 1 4) (by simp) with h74 | h74
      · rcases p0_3 (m.d 2 4) (by simp) with h75 | h75
        · rcases p0_3 (m.d 3 4) (by simp) with h76 | h76
          · rcases p0_3 (m.d 4 5) (by simp) with h77 | h77
            · linarith only [h77, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h79 | h79
              · rcases m.htr 0 1 3 (by decide) (by decide) with h80 | h80
                · rcases m.htr 0 1 4 (by decide) (by decide) with h81 | h81
                  · linarith only [h74, h81, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0]
                  · linarith only [h79, h81, hc12, hlam, hphi, ht23, ht34, u4elo1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h84 | h84
                  · linarith only [h74, h80, h84, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo2]
                  · linarith only [h79, h84, hc12, hlam, hphi, ht23, ht34, u4elo1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h87 | h87
                · rcases m.htr 0 1 4 (by decide) (by decide) with h88 | h88
                  · linarith only [h74, h79, h88, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
                  · linarith only [h87, h88, hc13, hlam, hphi, ht34, u4elo1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h91 | h91
                  · linarith only [h74, h87, h91, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo2]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h93 | h93
                    · linarith only [h79, h93, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
                    · linarith only [h73, h93, hlam]
          · linarith only [h76, hc34, hlam, hphi, p0_1, u4elo2]
        · linarith only [h75, hlam, p0_0]
      · linarith only [h74, hc14, hlam, hphi, p0_1, u4elo2]
    · linarith only [h73, hc04, hlam, hphi, p0_1, u4elo2]
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
    rcases p0_3 (m.d 0 4) (by simp) with h104 | h104
    · rcases p0_3 (m.d 1 4) (by simp) with h105 | h105
      · rcases p0_3 (m.d 2 4) (by simp) with h106 | h106
        · rcases p0_3 (m.d 3 4) (by simp) with h107 | h107
          · rcases p0_3 (m.d 4 5) (by simp) with h108 | h108
            · linarith only [h108, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h110 | h110
              · rcases m.htr 0 1 3 (by decide) (by decide) with h111 | h111
                · rcases m.htr 0 1 4 (by decide) (by decide) with h112 | h112
                  · linarith only [h105, h112, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0]
                  · linarith only [h110, h112, hc12, hlam, hphi, ht23, ht34, u4elo1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h115 | h115
                  · linarith only [h105, h111, h115, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo2]
                  · linarith only [h110, h115, hc12, hlam, hphi, ht23, ht34, u4elo1]
              · rcases m.htr 0 1 3 (by decide) (by decide) with h118 | h118
                · rcases m.htr 0 1 4 (by decide) (by decide) with h119 | h119
                  · linarith only [h105, h110, h119, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
                  · linarith only [h118, h119, hc13, hlam, hphi, ht34, u4elo1]
                · rcases m.htr 0 1 4 (by decide) (by decide) with h122 | h122
                  · linarith only [h105, h118, h122, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo2]
                  · rcases m.htr 0 2 4 (by decide) (by decide) with h124 | h124
                    · linarith only [h106, h110, h124, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
                    · rcases m.htr 0 3 4 (by decide) (by decide) with h126 | h126
                      · linarith only [h118, h126, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo2]
                      · linarith only [h104, h126, hlam]
          · linarith only [h107, hlam, p0_0]
        · linarith only [h106, hc24, hlam, hphi, p0_1, u4elo3]
      · linarith only [h105, hc14, hlam, hphi, p0_1, u4elo3]
    · linarith only [h104, hc04, hlam, hphi, p0_1, u4elo3]
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

theorem n7l_sAB1_M_LI_H_L_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h1ehi := hb1.1
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  linarith only [hlam, hphi, ht12, ht23, ht34, ht45, u1ehi4, u5elo1]

theorem n7l_sAB1_M_LI_H_R_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc13 := m.hcor 1 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.1
  have h1elo := hb1.1
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  rcases m.htr 1 3 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h3 | h3
      · linarith only [h0, h1, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
      · linarith only [h0, h1, h3, hc34, hlam, hphi, u4elo4]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
    · linarith only [h6, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h8 | h8
      · linarith only [h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3, u5ehi4]
      · linarith only [h0, h8, hc13, hlam, hphi, ht34, u4elo4]

theorem n7l_sAB1_M_LI_H_R_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
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
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 3 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h6 | h6
            · linarith only [h1, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi4]
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
            · linarith only [h1, h26, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
            · linarith only [h1, h18, h2, h26, hc23, hlam, hphi, ht34, u4elo4]
    · linarith only [h0, h1, hc23, hlam, hphi, ht34, u4elo2]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h30 | h30
    · rcases m.htr 1 2 5 (by decide) (by decide) with h31 | h31
      · linarith only [h0, h31, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
        · rcases m.htr 2 3 5 (by decide) (by decide) with h34 | h34
          · rcases m.htr 2 4 5 (by decide) (by decide) with h35 | h35
            · linarith only [h35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi4]
            · linarith only [h30, h31, h35, hc24, hlam, hphi, u4elo4]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h38 | h38
            · linarith only [h30, h38, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
            · linarith only [h0, h30, h34, h38, hc24, hlam, hphi, u4elo4]
        · linarith only [h0, h30, h33, hc24, hlam, hphi, u4elo3]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h42 | h42
      · linarith only [h30, h42, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi2]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h44 | h44
        · rcases m.htr 2 3 5 (by decide) (by decide) with h45 | h45
          · rcases m.htr 2 4 5 (by decide) (by decide) with h46 | h46
            · linarith only [h46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi4]
            · linarith only [h30, h46, hc12, hlam, hphi, ht23, ht34, u4elo4]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h49 | h49
            · linarith only [h49, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2, u5ehi4]
            · linarith only [h30, h49, hc12, hlam, hphi, ht23, ht34, u4elo4]
        · linarith only [h0, h44, hc12, hlam, hphi, ht23, ht34, u4elo3]

theorem n7l_sAB1_M_LI_H_R_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h1ehi := hb1.1
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  rcases m.htr 1 4 5 (by decide) (by decide) with h0 | h0
  · linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi4]
  · linarith only [h0, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]

theorem n7l_sAB1_M_LI_M_IR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4elo := hb4.1
  have h5ehi := hb5.2.1
  have h1elo := hb1.1
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h6 | h6
            · linarith only [h2, h3, h4, h6, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
              · rcases m.htr 2 4 5 (by decide) (by decide) with h9 | h9
                · linarith only [h2, h3, h4, h6, h9, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h3, h4, h8, h9, hc34, hlam, hphi, u4elo4]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
                · linarith only [h12, h3, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                · linarith only [h12, h3, h4, h8, hc23, hlam, hphi, ht34, u4elo4]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h15 | h15
          · linarith only [h0, h15, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h17 | h17
            · linarith only [h1, h17, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
              · rcases m.htr 2 4 5 (by decide) (by decide) with h20 | h20
                · linarith only [h17, h20, h3, hc12, hlam, hphi, ht23, ht34, u4elo2]
                · linarith only [h20, h3, hc12, hlam, hphi, ht23, ht34, u4elo4]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h23 | h23
                · linarith only [h17, h19, h23, h3, hc12, hlam, hphi, ht23, ht34, u4elo3]
                · linarith only [h23, h3, hc12, hlam, hphi, ht23, ht34, u4elo4]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h26 | h26
        · linarith only [h0, h2, h26, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h28 | h28
          · linarith only [h1, h2, h26, h28, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi2]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h30 | h30
            · linarith only [h1, h2, h30, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
            · linarith only [h1, h2, h26, h30, hc12, hlam, hphi, ht23, ht34, u4elo4]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h34 | h34
    · rcases m.htr 0 1 5 (by decide) (by decide) with h35 | h35
      · linarith only [h0, h35, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h37 | h37
        · rcases m.htr 1 2 5 (by decide) (by decide) with h38 | h38
          · rcases m.htr 1 4 5 (by decide) (by decide) with h39 | h39
            · linarith only [h34, h35, h38, h39, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
            · linarith only [h34, h35, h39, hc14, hlam, hphi, u4elo4]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h42 | h42
            · linarith only [h34, h42, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
            · linarith only [h0, h34, h38, h42, hc14, hlam, hphi, u4elo4]
        · linarith only [h0, h34, h37, hc14, hlam, hphi, u4elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h46 | h46
      · linarith only [h34, h46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1, u5ehi1]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h48 | h48
        · rcases m.htr 1 2 5 (by decide) (by decide) with h49 | h49
          · rcases m.htr 1 4 5 (by decide) (by decide) with h50 | h50
            · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
              · rcases m.htr 2 4 5 (by decide) (by decide) with h52 | h52
                · linarith only [h48, h52, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                · linarith only [h50, h52, hc24, hlam, hphi, u4elo1]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h55 | h55
                · linarith only [h48, h55, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                · linarith only [h50, h55, hc24, hlam, hphi, u4elo1]
            · linarith only [h34, h50, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h59 | h59
            · linarith only [h48, h49, h59, hlam]
            · linarith only [h34, h59, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
        · linarith only [h0, h48, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]

theorem n7l_sAB1_M_LI_M_IR_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAB1_M_LI_M_IR_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have h1ehi := hb1.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
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
    linarith only [hlam, hphi, ht12, ht23, ht34, p0_1, u1ehi3, u4elo3]
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
    linarith only [hlam, hphi, ht12, ht23, ht34, p0_1, u1ehi3, u4elo4]
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

theorem n7l_sAB1_M_LI_M_LI_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
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
  have h1elo := hb1.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
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
            · rcases m.htr 0 1 2 (by decide) (by decide) with h11 | h11
              · rcases m.htr 0 1 4 (by decide) (by decide) with h12 | h12
                · linarith only [h12, h6, hlam]
                · linarith only [h11, h12, hc12, hlam, hphi, ht23, ht34, u4elo1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h15 | h15
                · linarith only [h15, h6, hlam]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h17 | h17
                  · linarith only [h17, h7, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h19 | h19
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h20 | h20
                      · linarith only [h11, h17, h20, hc01, hlam, hphi, u1elo1]
                      · linarith only [h11, h20, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                    · linarith only [h19, hlam, p0_0]
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
    rcases p0_3 (m.d 0 4) (by simp) with h32 | h32
    · rcases p0_3 (m.d 1 4) (by simp) with h33 | h33
      · rcases p0_3 (m.d 2 4) (by simp) with h34 | h34
        · rcases p0_3 (m.d 3 4) (by simp) with h35 | h35
          · rcases p0_3 (m.d 4 5) (by simp) with h36 | h36
            · linarith only [h36, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h38 | h38
              · rcases m.htr 0 1 4 (by decide) (by decide) with h39 | h39
                · linarith only [h39, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0]
                · linarith only [h32, h39, hlam]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h42 | h42
                · linarith only [h38, h42, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
                · linarith only [h32, h42, hlam]
          · linarith only [h35, hc34, hlam, hphi, p0_1, u4elo1]
        · linarith only [h32, h34, hc24, hlam, hphi, p0_1, u4elo0]
      · linarith only [h33, hlam, p0_0]
    · linarith only [h32, hc04, hlam, hphi, p0_1, u4elo1]
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
    rcases p0_3 (m.d 0 4) (by simp) with h53 | h53
    · rcases p0_3 (m.d 1 4) (by simp) with h54 | h54
      · rcases p0_3 (m.d 2 4) (by simp) with h55 | h55
        · rcases p0_3 (m.d 3 4) (by simp) with h56 | h56
          · rcases p0_3 (m.d 4 5) (by simp) with h57 | h57
            · linarith only [h57, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h59 | h59
              · rcases m.htr 0 1 4 (by decide) (by decide) with h60 | h60
                · linarith only [h54, h60, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0]
                · linarith only [h59, h60, hc12, hlam, hphi, ht23, ht34, u4elo1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h63 | h63
                · linarith only [h54, h59, h63, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h65 | h65
                  · linarith only [h59, h65, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
                  · linarith only [h53, h65, hlam]
          · linarith only [h56, hc34, hlam, hphi, p0_1, u4elo2]
        · linarith only [h55, hlam, p0_0]
      · linarith only [h54, hc14, hlam, hphi, p0_1, u4elo2]
    · linarith only [h53, hc04, hlam, hphi, p0_1, u4elo2]
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
    rcases p0_3 (m.d 0 4) (by simp) with h76 | h76
    · rcases p0_3 (m.d 1 4) (by simp) with h77 | h77
      · rcases p0_3 (m.d 2 4) (by simp) with h78 | h78
        · rcases p0_3 (m.d 3 4) (by simp) with h79 | h79
          · rcases p0_3 (m.d 4 5) (by simp) with h80 | h80
            · linarith only [h80, hlam, p0_0]
            · rcases m.htr 0 1 2 (by decide) (by decide) with h82 | h82
              · rcases m.htr 0 1 4 (by decide) (by decide) with h83 | h83
                · linarith only [h77, h83, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo0]
                · linarith only [h82, h83, hc12, hlam, hphi, ht23, ht34, u4elo1]
              · rcases m.htr 0 1 4 (by decide) (by decide) with h86 | h86
                · linarith only [h77, h82, h86, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
                · rcases m.htr 0 2 4 (by decide) (by decide) with h88 | h88
                  · linarith only [h78, h82, h88, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h90 | h90
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h91 | h91
                      · linarith only [h76, h88, h91, hc45, hlam, hphi, ht01, ht0b, ht5b, p0_1, u1elo1]
                      · linarith only [h82, h91, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                    · linarith only [h76, h90, hlam, p0_1]
          · linarith only [h79, hlam, p0_0]
        · linarith only [h76, h78, hc24, hlam, hphi, p0_1, u4elo0]
      · linarith only [h76, h77, hc14, hlam, hphi, p0_1, u4elo0]
    · linarith only [h76, hc04, hlam, hphi, p0_1, u4elo3]
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

theorem n7l_sAB1_M_LI_M_LI_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAB1_M_LI_M_LI_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc05 := m.hcor 0 5 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h5elo := hb5.1
  have h5bigk := hb5.2.2.2
  have h1ehi := hb1.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
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
    linarith only [hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u1ehi4, u5elo3]
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
    linarith only [hlam, hphi, ht12, ht23, ht34, ht45, p0_1, u1ehi4, u5elo4]
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

theorem n7l_sAB1_M_LI_M_LR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAB1_M_LI_M_LR_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAB1_M_LI_M_LR_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4elo := hb4.1
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have h1ehi := hb1.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 3 4 5 (by decide) (by decide) with h5 | h5
            · linarith only [h1, h3, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi9]
            · linarith only [h2, h4, h5, hc34, hlam, hphi, u4elo0]
          · linarith only [h4, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
        · linarith only [h3, hlam, hphi, ht12, ht23, ht34, u1ehi2, u4elo3]
      · linarith only [h2, hlam, hphi, ht12, ht23, ht34, u1ehi0, u4elo1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h12 | h12
    · linarith only [h0, h12, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h14 | h14
      · linarith only [h0, h14, hc12, hlam, hphi, u1ehi3]
      · linarith only [h14, hlam, hphi, ht12, ht23, ht34, u1ehi0, u4elo1]

theorem n7l_sAB1_M_LR_H_I_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAB1_M_LR_H_I_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAB1_M_LR_H_I_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAB1_M_LR_H_L_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.2.1
  have h5elo := hb5.1
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi9, u5elo4]

theorem n7l_sAB1_M_LR_H_L_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.2.1
  have h5elo := hb5.1
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi9, u5elo4]

theorem n7l_sAB1_M_LR_H_L_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_L m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h4ehi := hb4.2.2.1
  have h5elo := hb5.1
  have u4ehi9 := h4ehi (m.d 4 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [hlam, hphi, ht45, u4ehi9, u5elo4]

theorem n7l_sAB1_M_LR_H_R_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAB1_M_LR_H_R_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAB1_M_LR_H_R_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAB1_M_LR_M_IR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAB1_M_LR_M_IR_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAB1_M_LR_M_IR_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAB1_M_LR_M_LI_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAB1_M_LR_M_LI_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAB1_M_LR_M_LI_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LI m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAB1_M_LR_M_LR_L_0 (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAB1_M_LR_M_LR_L_I (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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

theorem n7l_sAB1_M_LR_M_LR_L_R (m : N7Model)
    (hb4 : CMSig2_7_M_LR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
