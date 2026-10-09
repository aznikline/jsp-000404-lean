import Jsp000404.S7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem n8l_sBT8_H_I_M_LI (m : N8Model)
    (hb0 : CMSig2_8_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_M_LI m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc06 := m.hcor 0 6 (by decide)
  have hc16 := m.hcor 1 6 (by decide)
  have hc26 := m.hcor 2 6 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have h6elo := hb6.1
  have h6bigk := hb6.2.2.2
  have u6elo0 := h6elo (m.d 0 6) (by simp)
  have u6elo1 := h6elo (m.d 1 6) (by simp)
  have u6elo2 := h6elo (m.d 2 6) (by simp)
  have u6elo3 := h6elo (m.d 3 6) (by simp)
  have u6elo4 := h6elo (m.d 4 6) (by simp)
  have u6elo5 := h6elo (m.d 5 6) (by simp)
  rcases h6bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc26, hlam, hphi, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc36, hlam, hphi, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc46, hlam, hphi, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u6elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc26, hlam, hphi, p0_1, u6elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc36, hlam, hphi, p0_1, u6elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc46, hlam, hphi, p0_1, u6elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, p0_1, u6elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u6elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u6elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc36, hlam, hphi, p0_1, u6elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc46, hlam, hphi, p0_1, u6elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, p0_1, u6elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u6elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u6elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc26, hlam, hphi, p0_1, u6elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc46, hlam, hphi, p0_1, u6elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, p0_1, u6elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u6elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u6elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc26, hlam, hphi, p0_1, u6elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc36, hlam, hphi, p0_1, u6elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, p0_1, u6elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u6elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u6elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc26, hlam, hphi, p0_1, u6elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc36, hlam, hphi, p0_1, u6elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc46, hlam, hphi, p0_1, u6elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n8l_sBT8_H_I_M_LR (m : N8Model)
    (hb0 : CMSig2_8_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_M_LR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0bigk := hb0.1
  have h6elo := hb6.1
  have h6ehi := hb6.2.2.1
  have u6elo0 := h6elo (m.d 0 6) (by simp)
  have u6ehi6 := h6ehi (m.d 0 6) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 0 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h5 | h5
        · rcases p0_3 (m.d 0 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 0 5) (by simp) with h7 | h7
            · rcases p0_3 (m.d 0 6) (by simp) with h8 | h8
              · linarith only [h8, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h8, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h11 | h11
              · linarith only [h11, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h11, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h14 | h14
            · rcases p0_3 (m.d 0 6) (by simp) with h15 | h15
              · linarith only [h15, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h15, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h18 | h18
              · linarith only [h18, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h18, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
        · rcases p0_3 (m.d 0 4) (by simp) with h21 | h21
          · rcases p0_3 (m.d 0 5) (by simp) with h22 | h22
            · rcases p0_3 (m.d 0 6) (by simp) with h23 | h23
              · linarith only [h23, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h23, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h26 | h26
              · linarith only [h26, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h26, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h29 | h29
            · rcases p0_3 (m.d 0 6) (by simp) with h30 | h30
              · linarith only [h30, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h30, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h33 | h33
              · linarith only [h33, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h33, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h37 | h37
    · rcases p0_3 (m.d 0 2) (by simp) with h38 | h38
      · rcases p0_3 (m.d 0 3) (by simp) with h39 | h39
        · linarith only [h39, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h41 | h41
          · rcases p0_3 (m.d 0 5) (by simp) with h42 | h42
            · rcases p0_3 (m.d 0 6) (by simp) with h43 | h43
              · linarith only [h43, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h43, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h46 | h46
              · linarith only [h46, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h46, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h49 | h49
            · rcases p0_3 (m.d 0 6) (by simp) with h50 | h50
              · linarith only [h50, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h50, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h53 | h53
              · linarith only [h53, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h53, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
      · rcases p0_3 (m.d 0 3) (by simp) with h56 | h56
        · linarith only [h56, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h58 | h58
          · rcases p0_3 (m.d 0 5) (by simp) with h59 | h59
            · rcases p0_3 (m.d 0 6) (by simp) with h60 | h60
              · linarith only [h38, h60, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h60, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h63 | h63
              · linarith only [h63, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h63, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h66 | h66
            · rcases p0_3 (m.d 0 6) (by simp) with h67 | h67
              · linarith only [h67, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h67, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h70 | h70
              · linarith only [h70, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h70, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
    · linarith only [h37, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h74 | h74
    · rcases p0_3 (m.d 0 2) (by simp) with h75 | h75
      · rcases p0_3 (m.d 0 3) (by simp) with h76 | h76
        · rcases p0_3 (m.d 0 4) (by simp) with h77 | h77
          · linarith only [h77, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h79 | h79
            · rcases p0_3 (m.d 0 6) (by simp) with h80 | h80
              · linarith only [h80, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h80, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h83 | h83
              · linarith only [h83, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h83, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
        · rcases p0_3 (m.d 0 4) (by simp) with h86 | h86
          · linarith only [h86, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h88 | h88
            · rcases p0_3 (m.d 0 6) (by simp) with h89 | h89
              · linarith only [h76, h89, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h89, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h92 | h92
              · linarith only [h92, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h92, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
      · rcases p0_3 (m.d 0 3) (by simp) with h95 | h95
        · rcases p0_3 (m.d 0 4) (by simp) with h96 | h96
          · linarith only [h96, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h98 | h98
            · rcases p0_3 (m.d 0 6) (by simp) with h99 | h99
              · linarith only [h75, h99, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h99, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h102 | h102
              · linarith only [h102, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h102, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
        · rcases p0_3 (m.d 0 4) (by simp) with h105 | h105
          · linarith only [h105, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h107 | h107
            · rcases p0_3 (m.d 0 6) (by simp) with h108 | h108
              · linarith only [h108, h95, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h108, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h111 | h111
              · linarith only [h111, h95, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h111, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
    · linarith only [h74, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h115 | h115
    · rcases p0_3 (m.d 0 2) (by simp) with h116 | h116
      · rcases p0_3 (m.d 0 3) (by simp) with h117 | h117
        · rcases p0_3 (m.d 0 4) (by simp) with h118 | h118
          · rcases p0_3 (m.d 0 5) (by simp) with h119 | h119
            · linarith only [h119, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h121 | h121
              · linarith only [h121, hc05, hlam, hphi, ht56, p0_1, u6elo0]
              · linarith only [h121, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h124 | h124
            · linarith only [h124, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h126 | h126
              · linarith only [h118, h126, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h126, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
        · rcases p0_3 (m.d 0 4) (by simp) with h129 | h129
          · rcases p0_3 (m.d 0 5) (by simp) with h130 | h130
            · linarith only [h130, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h132 | h132
              · linarith only [h117, h132, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h132, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h135 | h135
            · linarith only [h135, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h137 | h137
              · linarith only [h129, h137, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h137, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
      · rcases p0_3 (m.d 0 3) (by simp) with h140 | h140
        · rcases p0_3 (m.d 0 4) (by simp) with h141 | h141
          · rcases p0_3 (m.d 0 5) (by simp) with h142 | h142
            · linarith only [h142, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h144 | h144
              · linarith only [h116, h144, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h144, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h147 | h147
            · linarith only [h147, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h149 | h149
              · linarith only [h141, h149, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h149, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
        · rcases p0_3 (m.d 0 4) (by simp) with h152 | h152
          · rcases p0_3 (m.d 0 5) (by simp) with h153 | h153
            · linarith only [h153, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h155 | h155
              · linarith only [h140, h155, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h155, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h158 | h158
            · linarith only [h158, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h160 | h160
              · linarith only [h152, h160, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h160, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
    · linarith only [h115, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h165 | h165
    · linarith only [h165, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h167 | h167
      · rcases p0_3 (m.d 0 3) (by simp) with h168 | h168
        · rcases p0_3 (m.d 0 4) (by simp) with h169 | h169
          · rcases p0_3 (m.d 0 5) (by simp) with h170 | h170
            · rcases p0_3 (m.d 0 6) (by simp) with h171 | h171
              · linarith only [h171, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h171, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h174 | h174
              · linarith only [h174, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h174, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h177 | h177
            · rcases p0_3 (m.d 0 6) (by simp) with h178 | h178
              · linarith only [h178, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h178, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h181 | h181
              · linarith only [h181, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h181, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
        · rcases p0_3 (m.d 0 4) (by simp) with h184 | h184
          · rcases p0_3 (m.d 0 5) (by simp) with h185 | h185
            · rcases p0_3 (m.d 0 6) (by simp) with h186 | h186
              · linarith only [h186, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h186, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h189 | h189
              · linarith only [h189, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h189, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h192 | h192
            · rcases p0_3 (m.d 0 6) (by simp) with h193 | h193
              · linarith only [h193, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h193, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h196 | h196
              · linarith only [h196, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h196, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
      · linarith only [h167, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h201 | h201
    · rcases p0_3 (m.d 0 2) (by simp) with h202 | h202
      · rcases p0_3 (m.d 0 3) (by simp) with h203 | h203
        · linarith only [h203, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h205 | h205
          · rcases p0_3 (m.d 0 5) (by simp) with h206 | h206
            · rcases p0_3 (m.d 0 6) (by simp) with h207 | h207
              · linarith only [h207, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h201, h207, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h210 | h210
              · linarith only [h210, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h210, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h213 | h213
            · rcases p0_3 (m.d 0 6) (by simp) with h214 | h214
              · linarith only [h214, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h214, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h217 | h217
              · linarith only [h217, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h217, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
      · linarith only [h202, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h221 | h221
      · rcases p0_3 (m.d 0 3) (by simp) with h222 | h222
        · linarith only [h222, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h224 | h224
          · rcases p0_3 (m.d 0 5) (by simp) with h225 | h225
            · rcases p0_3 (m.d 0 6) (by simp) with h226 | h226
              · linarith only [h201, h226, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h226, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h229 | h229
              · linarith only [h229, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h229, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h232 | h232
            · rcases p0_3 (m.d 0 6) (by simp) with h233 | h233
              · linarith only [h233, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h233, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h236 | h236
              · linarith only [h236, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h236, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
      · linarith only [h221, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h240 | h240
    · rcases p0_3 (m.d 0 2) (by simp) with h241 | h241
      · rcases p0_3 (m.d 0 3) (by simp) with h242 | h242
        · rcases p0_3 (m.d 0 4) (by simp) with h243 | h243
          · linarith only [h243, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h245 | h245
            · rcases p0_3 (m.d 0 6) (by simp) with h246 | h246
              · linarith only [h246, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h240, h246, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h249 | h249
              · linarith only [h249, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h240, h249, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
        · rcases p0_3 (m.d 0 4) (by simp) with h252 | h252
          · linarith only [h252, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h254 | h254
            · rcases p0_3 (m.d 0 6) (by simp) with h255 | h255
              · linarith only [h242, h255, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h240, h255, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h258 | h258
              · linarith only [h258, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h240, h258, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
      · linarith only [h241, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h262 | h262
      · rcases p0_3 (m.d 0 3) (by simp) with h263 | h263
        · rcases p0_3 (m.d 0 4) (by simp) with h264 | h264
          · linarith only [h264, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h266 | h266
            · rcases p0_3 (m.d 0 6) (by simp) with h267 | h267
              · linarith only [h240, h267, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h267, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h270 | h270
              · linarith only [h270, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h270, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
        · rcases p0_3 (m.d 0 4) (by simp) with h273 | h273
          · linarith only [h273, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h275 | h275
            · rcases p0_3 (m.d 0 6) (by simp) with h276 | h276
              · linarith only [h263, h276, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h276, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h279 | h279
              · linarith only [h279, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h279, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
      · linarith only [h262, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h283 | h283
    · rcases p0_3 (m.d 0 2) (by simp) with h284 | h284
      · rcases p0_3 (m.d 0 3) (by simp) with h285 | h285
        · rcases p0_3 (m.d 0 4) (by simp) with h286 | h286
          · rcases p0_3 (m.d 0 5) (by simp) with h287 | h287
            · linarith only [h287, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h289 | h289
              · linarith only [h289, hc05, hlam, hphi, ht56, p0_1, u6elo0]
              · linarith only [h283, h289, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h292 | h292
            · linarith only [h292, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h294 | h294
              · linarith only [h286, h294, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h283, h294, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
        · rcases p0_3 (m.d 0 4) (by simp) with h297 | h297
          · rcases p0_3 (m.d 0 5) (by simp) with h298 | h298
            · linarith only [h298, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h300 | h300
              · linarith only [h285, h300, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h300, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h303 | h303
            · linarith only [h303, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h305 | h305
              · linarith only [h297, h305, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h305, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
      · linarith only [h284, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h309 | h309
      · rcases p0_3 (m.d 0 3) (by simp) with h310 | h310
        · rcases p0_3 (m.d 0 4) (by simp) with h311 | h311
          · rcases p0_3 (m.d 0 5) (by simp) with h312 | h312
            · linarith only [h312, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h314 | h314
              · linarith only [h283, h314, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h314, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h317 | h317
            · linarith only [h317, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h319 | h319
              · linarith only [h311, h319, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h319, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
        · rcases p0_3 (m.d 0 4) (by simp) with h322 | h322
          · rcases p0_3 (m.d 0 5) (by simp) with h323 | h323
            · linarith only [h323, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h325 | h325
              · linarith only [h310, h325, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h325, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h328 | h328
            · linarith only [h328, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h330 | h330
              · linarith only [h322, h330, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h330, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
      · linarith only [h309, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h335 | h335
    · linarith only [h335, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h337 | h337
      · rcases p0_3 (m.d 0 3) (by simp) with h338 | h338
        · rcases p0_3 (m.d 0 4) (by simp) with h339 | h339
          · rcases p0_3 (m.d 0 5) (by simp) with h340 | h340
            · rcases p0_3 (m.d 0 6) (by simp) with h341 | h341
              · linarith only [h341, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h341, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h344 | h344
              · linarith only [h344, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h344, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h347 | h347
            · rcases p0_3 (m.d 0 6) (by simp) with h348 | h348
              · linarith only [h348, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h348, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h351 | h351
              · linarith only [h351, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h351, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
        · linarith only [h338, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h355 | h355
        · rcases p0_3 (m.d 0 4) (by simp) with h356 | h356
          · rcases p0_3 (m.d 0 5) (by simp) with h357 | h357
            · rcases p0_3 (m.d 0 6) (by simp) with h358 | h358
              · linarith only [h358, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h358, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h361 | h361
              · linarith only [h361, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h361, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h364 | h364
            · rcases p0_3 (m.d 0 6) (by simp) with h365 | h365
              · linarith only [h365, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h365, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h368 | h368
              · linarith only [h368, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h368, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
        · linarith only [h355, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h372 | h372
    · rcases p0_3 (m.d 0 2) (by simp) with h373 | h373
      · linarith only [h373, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h375 | h375
        · rcases p0_3 (m.d 0 4) (by simp) with h376 | h376
          · rcases p0_3 (m.d 0 5) (by simp) with h377 | h377
            · rcases p0_3 (m.d 0 6) (by simp) with h378 | h378
              · linarith only [h378, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h372, h378, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h381 | h381
              · linarith only [h381, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h372, h381, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h384 | h384
            · rcases p0_3 (m.d 0 6) (by simp) with h385 | h385
              · linarith only [h385, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h385, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h388 | h388
              · linarith only [h388, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h388, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
        · linarith only [h375, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h392 | h392
      · linarith only [h392, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h394 | h394
        · rcases p0_3 (m.d 0 4) (by simp) with h395 | h395
          · rcases p0_3 (m.d 0 5) (by simp) with h396 | h396
            · rcases p0_3 (m.d 0 6) (by simp) with h397 | h397
              · linarith only [h372, h397, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h397, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h400 | h400
              · linarith only [h400, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h400, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h403 | h403
            · rcases p0_3 (m.d 0 6) (by simp) with h404 | h404
              · linarith only [h404, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h404, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h407 | h407
              · linarith only [h407, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h407, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
        · linarith only [h394, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h412 | h412
    · rcases p0_3 (m.d 0 2) (by simp) with h413 | h413
      · rcases p0_3 (m.d 0 3) (by simp) with h414 | h414
        · rcases p0_3 (m.d 0 4) (by simp) with h415 | h415
          · linarith only [h415, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h417 | h417
            · rcases p0_3 (m.d 0 6) (by simp) with h418 | h418
              · linarith only [h418, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h412, h418, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h421 | h421
              · linarith only [h421, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h413, h421, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
        · linarith only [h414, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h425 | h425
        · rcases p0_3 (m.d 0 4) (by simp) with h426 | h426
          · linarith only [h426, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h428 | h428
            · rcases p0_3 (m.d 0 6) (by simp) with h429 | h429
              · linarith only [h413, h429, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h429, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h432 | h432
              · linarith only [h432, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h432, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
        · linarith only [h425, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h436 | h436
      · rcases p0_3 (m.d 0 3) (by simp) with h437 | h437
        · rcases p0_3 (m.d 0 4) (by simp) with h438 | h438
          · linarith only [h438, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h440 | h440
            · rcases p0_3 (m.d 0 6) (by simp) with h441 | h441
              · linarith only [h412, h441, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h436, h441, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h444 | h444
              · linarith only [h444, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h444, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
        · linarith only [h437, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h448 | h448
        · rcases p0_3 (m.d 0 4) (by simp) with h449 | h449
          · linarith only [h449, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h451 | h451
            · rcases p0_3 (m.d 0 6) (by simp) with h452 | h452
              · linarith only [h436, h452, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h452, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h455 | h455
              · linarith only [h455, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h455, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
        · linarith only [h448, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h459 | h459
    · rcases p0_3 (m.d 0 2) (by simp) with h460 | h460
      · rcases p0_3 (m.d 0 3) (by simp) with h461 | h461
        · rcases p0_3 (m.d 0 4) (by simp) with h462 | h462
          · rcases p0_3 (m.d 0 5) (by simp) with h463 | h463
            · linarith only [h463, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h465 | h465
              · linarith only [h465, hc05, hlam, hphi, ht56, p0_1, u6elo0]
              · linarith only [h459, h465, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h468 | h468
            · linarith only [h468, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h470 | h470
              · linarith only [h462, h470, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h460, h470, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
        · linarith only [h461, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h474 | h474
        · rcases p0_3 (m.d 0 4) (by simp) with h475 | h475
          · rcases p0_3 (m.d 0 5) (by simp) with h476 | h476
            · linarith only [h476, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h478 | h478
              · linarith only [h460, h478, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h478, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h481 | h481
            · linarith only [h481, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h483 | h483
              · linarith only [h475, h483, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h483, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
        · linarith only [h474, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h487 | h487
      · rcases p0_3 (m.d 0 3) (by simp) with h488 | h488
        · rcases p0_3 (m.d 0 4) (by simp) with h489 | h489
          · rcases p0_3 (m.d 0 5) (by simp) with h490 | h490
            · linarith only [h490, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h492 | h492
              · linarith only [h459, h492, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h487, h492, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h495 | h495
            · linarith only [h495, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h497 | h497
              · linarith only [h489, h497, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h497, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
        · linarith only [h488, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h501 | h501
        · rcases p0_3 (m.d 0 4) (by simp) with h502 | h502
          · rcases p0_3 (m.d 0 5) (by simp) with h503 | h503
            · linarith only [h503, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h505 | h505
              · linarith only [h487, h505, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h505, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h508 | h508
            · linarith only [h508, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h510 | h510
              · linarith only [h487, h510, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h510, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
        · linarith only [h501, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h515 | h515
    · linarith only [h515, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h517 | h517
      · rcases p0_3 (m.d 0 3) (by simp) with h518 | h518
        · rcases p0_3 (m.d 0 4) (by simp) with h519 | h519
          · rcases p0_3 (m.d 0 5) (by simp) with h520 | h520
            · rcases p0_3 (m.d 0 6) (by simp) with h521 | h521
              · linarith only [h521, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h517, h521, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h524 | h524
              · linarith only [h524, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h524, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · linarith only [h519, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h528 | h528
          · rcases p0_3 (m.d 0 5) (by simp) with h529 | h529
            · rcases p0_3 (m.d 0 6) (by simp) with h530 | h530
              · linarith only [h530, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h517, h530, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h533 | h533
              · linarith only [h533, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h533, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · linarith only [h528, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h537 | h537
        · rcases p0_3 (m.d 0 4) (by simp) with h538 | h538
          · rcases p0_3 (m.d 0 5) (by simp) with h539 | h539
            · rcases p0_3 (m.d 0 6) (by simp) with h540 | h540
              · linarith only [h540, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h537, h540, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h543 | h543
              · linarith only [h543, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h543, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · linarith only [h538, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h547 | h547
          · rcases p0_3 (m.d 0 5) (by simp) with h548 | h548
            · rcases p0_3 (m.d 0 6) (by simp) with h549 | h549
              · linarith only [h549, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h549, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h552 | h552
              · linarith only [h552, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h552, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · linarith only [h547, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h556 | h556
    · rcases p0_3 (m.d 0 2) (by simp) with h557 | h557
      · linarith only [h557, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h559 | h559
        · rcases p0_3 (m.d 0 4) (by simp) with h560 | h560
          · rcases p0_3 (m.d 0 5) (by simp) with h561 | h561
            · rcases p0_3 (m.d 0 6) (by simp) with h562 | h562
              · linarith only [h562, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h556, h562, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h565 | h565
              · linarith only [h565, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h556, h565, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · linarith only [h560, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h569 | h569
          · rcases p0_3 (m.d 0 5) (by simp) with h570 | h570
            · rcases p0_3 (m.d 0 6) (by simp) with h571 | h571
              · linarith only [h571, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h556, h571, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h574 | h574
              · linarith only [h574, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h556, h574, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · linarith only [h569, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h578 | h578
      · linarith only [h578, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h580 | h580
        · rcases p0_3 (m.d 0 4) (by simp) with h581 | h581
          · rcases p0_3 (m.d 0 5) (by simp) with h582 | h582
            · rcases p0_3 (m.d 0 6) (by simp) with h583 | h583
              · linarith only [h556, h583, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h580, h583, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h586 | h586
              · linarith only [h586, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h580, h586, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · linarith only [h581, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h590 | h590
          · rcases p0_3 (m.d 0 5) (by simp) with h591 | h591
            · rcases p0_3 (m.d 0 6) (by simp) with h592 | h592
              · linarith only [h592, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h592, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h595 | h595
              · linarith only [h595, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h595, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · linarith only [h590, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h599 | h599
    · rcases p0_3 (m.d 0 2) (by simp) with h600 | h600
      · rcases p0_3 (m.d 0 3) (by simp) with h601 | h601
        · linarith only [h601, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h603 | h603
          · rcases p0_3 (m.d 0 5) (by simp) with h604 | h604
            · rcases p0_3 (m.d 0 6) (by simp) with h605 | h605
              · linarith only [h605, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h599, h605, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h608 | h608
              · linarith only [h608, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h599, h608, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · linarith only [h603, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h612 | h612
        · linarith only [h612, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h614 | h614
          · rcases p0_3 (m.d 0 5) (by simp) with h615 | h615
            · rcases p0_3 (m.d 0 6) (by simp) with h616 | h616
              · linarith only [h600, h616, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h616, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h619 | h619
              · linarith only [h619, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h619, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · linarith only [h614, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h623 | h623
      · rcases p0_3 (m.d 0 3) (by simp) with h624 | h624
        · linarith only [h624, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h626 | h626
          · rcases p0_3 (m.d 0 5) (by simp) with h627 | h627
            · rcases p0_3 (m.d 0 6) (by simp) with h628 | h628
              · linarith only [h599, h628, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h623, h628, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h631 | h631
              · linarith only [h631, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h623, h631, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · linarith only [h626, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h635 | h635
        · linarith only [h635, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h637 | h637
          · rcases p0_3 (m.d 0 5) (by simp) with h638 | h638
            · rcases p0_3 (m.d 0 6) (by simp) with h639 | h639
              · linarith only [h623, h639, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h639, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h642 | h642
              · linarith only [h642, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h642, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · linarith only [h637, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h647 | h647
    · rcases p0_3 (m.d 0 2) (by simp) with h648 | h648
      · rcases p0_3 (m.d 0 3) (by simp) with h649 | h649
        · rcases p0_3 (m.d 0 4) (by simp) with h650 | h650
          · rcases p0_3 (m.d 0 5) (by simp) with h651 | h651
            · linarith only [h651, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h653 | h653
              · linarith only [h653, hc05, hlam, hphi, ht56, p0_1, u6elo0]
              · linarith only [h647, h653, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · linarith only [h650, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h657 | h657
          · rcases p0_3 (m.d 0 5) (by simp) with h658 | h658
            · linarith only [h658, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h660 | h660
              · linarith only [h649, h660, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h647, h660, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · linarith only [h657, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h664 | h664
        · rcases p0_3 (m.d 0 4) (by simp) with h665 | h665
          · rcases p0_3 (m.d 0 5) (by simp) with h666 | h666
            · linarith only [h666, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h668 | h668
              · linarith only [h648, h668, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h664, h668, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · linarith only [h665, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h672 | h672
          · rcases p0_3 (m.d 0 5) (by simp) with h673 | h673
            · linarith only [h673, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h675 | h675
              · linarith only [h664, h675, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h647, h675, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · linarith only [h672, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h679 | h679
      · rcases p0_3 (m.d 0 3) (by simp) with h680 | h680
        · rcases p0_3 (m.d 0 4) (by simp) with h681 | h681
          · rcases p0_3 (m.d 0 5) (by simp) with h682 | h682
            · linarith only [h682, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h684 | h684
              · linarith only [h647, h684, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h679, h684, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · linarith only [h681, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h688 | h688
          · rcases p0_3 (m.d 0 5) (by simp) with h689 | h689
            · linarith only [h689, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h691 | h691
              · linarith only [h680, h691, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h679, h691, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · linarith only [h688, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h695 | h695
        · rcases p0_3 (m.d 0 4) (by simp) with h696 | h696
          · rcases p0_3 (m.d 0 5) (by simp) with h697 | h697
            · linarith only [h697, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h699 | h699
              · linarith only [h679, h699, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h695, h699, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · linarith only [h696, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h703 | h703
          · rcases p0_3 (m.d 0 5) (by simp) with h704 | h704
            · linarith only [h704, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h706 | h706
              · linarith only [h695, h706, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h706, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
          · linarith only [h703, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h711 | h711
    · linarith only [h711, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h713 | h713
      · rcases p0_3 (m.d 0 3) (by simp) with h714 | h714
        · rcases p0_3 (m.d 0 4) (by simp) with h715 | h715
          · rcases p0_3 (m.d 0 5) (by simp) with h716 | h716
            · rcases p0_3 (m.d 0 6) (by simp) with h717 | h717
              · linarith only [h717, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h713, h717, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h716, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h721 | h721
            · rcases p0_3 (m.d 0 6) (by simp) with h722 | h722
              · linarith only [h722, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h714, h722, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h721, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h726 | h726
          · rcases p0_3 (m.d 0 5) (by simp) with h727 | h727
            · rcases p0_3 (m.d 0 6) (by simp) with h728 | h728
              · linarith only [h728, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h713, h728, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h727, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h732 | h732
            · rcases p0_3 (m.d 0 6) (by simp) with h733 | h733
              · linarith only [h733, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h733, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h732, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h737 | h737
        · rcases p0_3 (m.d 0 4) (by simp) with h738 | h738
          · rcases p0_3 (m.d 0 5) (by simp) with h739 | h739
            · rcases p0_3 (m.d 0 6) (by simp) with h740 | h740
              · linarith only [h740, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h737, h740, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h739, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h744 | h744
            · rcases p0_3 (m.d 0 6) (by simp) with h745 | h745
              · linarith only [h745, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h745, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h744, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h749 | h749
          · rcases p0_3 (m.d 0 5) (by simp) with h750 | h750
            · rcases p0_3 (m.d 0 6) (by simp) with h751 | h751
              · linarith only [h751, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h749, h751, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h750, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h755 | h755
            · rcases p0_3 (m.d 0 6) (by simp) with h756 | h756
              · linarith only [h756, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h756, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h755, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h760 | h760
    · rcases p0_3 (m.d 0 2) (by simp) with h761 | h761
      · linarith only [h761, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h763 | h763
        · rcases p0_3 (m.d 0 4) (by simp) with h764 | h764
          · rcases p0_3 (m.d 0 5) (by simp) with h765 | h765
            · rcases p0_3 (m.d 0 6) (by simp) with h766 | h766
              · linarith only [h766, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h760, h766, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h765, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h770 | h770
            · rcases p0_3 (m.d 0 6) (by simp) with h771 | h771
              · linarith only [h771, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h763, h771, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h770, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h775 | h775
          · rcases p0_3 (m.d 0 5) (by simp) with h776 | h776
            · rcases p0_3 (m.d 0 6) (by simp) with h777 | h777
              · linarith only [h777, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h760, h777, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h776, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h781 | h781
            · rcases p0_3 (m.d 0 6) (by simp) with h782 | h782
              · linarith only [h782, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h782, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h781, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h786 | h786
      · linarith only [h786, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h788 | h788
        · rcases p0_3 (m.d 0 4) (by simp) with h789 | h789
          · rcases p0_3 (m.d 0 5) (by simp) with h790 | h790
            · rcases p0_3 (m.d 0 6) (by simp) with h791 | h791
              · linarith only [h760, h791, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h788, h791, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h790, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h795 | h795
            · rcases p0_3 (m.d 0 6) (by simp) with h796 | h796
              · linarith only [h796, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h788, h796, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h795, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h800 | h800
          · rcases p0_3 (m.d 0 5) (by simp) with h801 | h801
            · rcases p0_3 (m.d 0 6) (by simp) with h802 | h802
              · linarith only [h802, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h800, h802, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h801, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h806 | h806
            · rcases p0_3 (m.d 0 6) (by simp) with h807 | h807
              · linarith only [h807, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h807, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h806, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h811 | h811
    · rcases p0_3 (m.d 0 2) (by simp) with h812 | h812
      · rcases p0_3 (m.d 0 3) (by simp) with h813 | h813
        · linarith only [h813, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h815 | h815
          · rcases p0_3 (m.d 0 5) (by simp) with h816 | h816
            · rcases p0_3 (m.d 0 6) (by simp) with h817 | h817
              · linarith only [h817, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h811, h817, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h816, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h821 | h821
            · rcases p0_3 (m.d 0 6) (by simp) with h822 | h822
              · linarith only [h822, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h812, h822, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h821, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h826 | h826
        · linarith only [h826, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h828 | h828
          · rcases p0_3 (m.d 0 5) (by simp) with h829 | h829
            · rcases p0_3 (m.d 0 6) (by simp) with h830 | h830
              · linarith only [h812, h830, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h828, h830, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h829, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h834 | h834
            · rcases p0_3 (m.d 0 6) (by simp) with h835 | h835
              · linarith only [h835, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h835, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h834, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h839 | h839
      · rcases p0_3 (m.d 0 3) (by simp) with h840 | h840
        · linarith only [h840, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h842 | h842
          · rcases p0_3 (m.d 0 5) (by simp) with h843 | h843
            · rcases p0_3 (m.d 0 6) (by simp) with h844 | h844
              · linarith only [h811, h844, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h839, h844, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h843, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h848 | h848
            · rcases p0_3 (m.d 0 6) (by simp) with h849 | h849
              · linarith only [h849, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h839, h849, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h848, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h853 | h853
        · linarith only [h853, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h855 | h855
          · rcases p0_3 (m.d 0 5) (by simp) with h856 | h856
            · rcases p0_3 (m.d 0 6) (by simp) with h857 | h857
              · linarith only [h839, h857, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h855, h857, hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h856, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h861 | h861
            · rcases p0_3 (m.d 0 6) (by simp) with h862 | h862
              · linarith only [h862, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h862, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h861, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h866 | h866
    · rcases p0_3 (m.d 0 2) (by simp) with h867 | h867
      · rcases p0_3 (m.d 0 3) (by simp) with h868 | h868
        · rcases p0_3 (m.d 0 4) (by simp) with h869 | h869
          · linarith only [h869, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h871 | h871
            · rcases p0_3 (m.d 0 6) (by simp) with h872 | h872
              · linarith only [h872, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h866, h872, hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h871, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h876 | h876
          · linarith only [h876, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h878 | h878
            · rcases p0_3 (m.d 0 6) (by simp) with h879 | h879
              · linarith only [h868, h879, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h867, h879, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h878, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h883 | h883
        · rcases p0_3 (m.d 0 4) (by simp) with h884 | h884
          · linarith only [h884, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h886 | h886
            · rcases p0_3 (m.d 0 6) (by simp) with h887 | h887
              · linarith only [h867, h887, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h883, h887, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h886, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h891 | h891
          · linarith only [h891, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h893 | h893
            · rcases p0_3 (m.d 0 6) (by simp) with h894 | h894
              · linarith only [h883, h894, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h894, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h893, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h898 | h898
      · rcases p0_3 (m.d 0 3) (by simp) with h899 | h899
        · rcases p0_3 (m.d 0 4) (by simp) with h900 | h900
          · linarith only [h900, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h902 | h902
            · rcases p0_3 (m.d 0 6) (by simp) with h903 | h903
              · linarith only [h866, h903, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h898, h903, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h902, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h907 | h907
          · linarith only [h907, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h909 | h909
            · rcases p0_3 (m.d 0 6) (by simp) with h910 | h910
              · linarith only [h899, h910, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h898, h910, hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h909, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h914 | h914
        · rcases p0_3 (m.d 0 4) (by simp) with h915 | h915
          · linarith only [h915, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h917 | h917
            · rcases p0_3 (m.d 0 6) (by simp) with h918 | h918
              · linarith only [h898, h918, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h914, h918, hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h917, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h922 | h922
          · linarith only [h922, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h924 | h924
            · rcases p0_3 (m.d 0 6) (by simp) with h925 | h925
              · linarith only [h914, h925, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h925, hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
            · linarith only [h924, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi6]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, ht56, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n8l_sBT8_H_L_H_L (m : N8Model)
    (hb0 : CMSig2_8_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_H_L m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc16 := m.hcor 1 6 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc26 := m.hcor 2 6 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0elo := hb0.1
  have h6elo := hb6.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u6elo1 := h6elo (m.d 1 6) (by simp)
  have u6elo2 := h6elo (m.d 2 6) (by simp)
  have u6elo3 := h6elo (m.d 3 6) (by simp)
  have u6elo4 := h6elo (m.d 4 6) (by simp)
  have u6elo5 := h6elo (m.d 5 6) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 6 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                · linarith only [h0, h3, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                · linarith only [h0, h10, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                · linarith only [h0, h10, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h13 | h13
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14 | h14
                · linarith only [h0, h14, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                · linarith only [h0, h14, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
                · linarith only [h0, h17, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                · linarith only [h0, h17, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h20 | h20
            · linarith only [h20, h3, h4, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h22 | h22
              · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
                · linarith only [h0, h23, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                · linarith only [h23, h3, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h26 | h26
                · linarith only [h0, h26, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                · linarith only [h22, h26, h3, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo4]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h29 | h29
          · rcases m.htr 0 3 4 (by decide) (by decide) with h30 | h30
            · rcases m.htr 0 4 5 (by decide) (by decide) with h31 | h31
              · rcases m.htr 1 2 3 (by decide) (by decide) with h32 | h32
                · linarith only [h0, h3, h32, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h34 | h34
                  · linarith only [h1, h32, h34, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                  · linarith only [h29, h34, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h37 | h37
                · linarith only [h0, h3, h37, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h39 | h39
                  · linarith only [h1, h37, h39, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                  · linarith only [h29, h39, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo1]
            · linarith only [h29, h3, h30, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h43 | h43
            · rcases m.htr 0 4 5 (by decide) (by decide) with h44 | h44
              · rcases m.htr 1 2 3 (by decide) (by decide) with h45 | h45
                · linarith only [h0, h45, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h47 | h47
                  · linarith only [h1, h29, h45, h47, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h49 | h49
                    · linarith only [h0, h49, hc25, hlam, hphi, ht0b, ht56, ht6b, u0elo0]
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h51 | h51
                      · linarith only [h1, h45, h51, hc26, hlam, hphi, ht0b, ht6b, u0elo0]
                      · linarith only [h51, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h54 | h54
                · linarith only [h0, h3, h43, h54, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h56 | h56
                  · linarith only [h1, h29, h54, h56, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h58 | h58
                    · linarith only [h0, h58, hc25, hlam, hphi, ht0b, ht56, ht6b, u0elo0]
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h60 | h60
                      · linarith only [h1, h54, h60, hc26, hlam, hphi, ht0b, ht6b, u0elo0]
                      · linarith only [h60, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h63 | h63
              · rcases m.htr 1 2 3 (by decide) (by decide) with h64 | h64
                · linarith only [h0, h3, h64, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h66 | h66
                  · linarith only [h0, h29, h63, h66, hc45, hlam, hphi, ht0b, ht56, ht6b, u0elo1]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h68 | h68
                    · linarith only [h1, h64, h68, hc25, hlam, hphi, ht0b, ht56, ht6b, u0elo0]
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h70 | h70
                      · linarith only [h1, h64, h70, hc26, hlam, hphi, ht0b, ht6b, u0elo0]
                      · linarith only [h70, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h73 | h73
                · linarith only [h0, h3, h73, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h75 | h75
                  · linarith only [h0, h29, h43, h75, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h77 | h77
                    · linarith only [h0, h77, hc25, hlam, hphi, ht0b, ht56, ht6b, u0elo0]
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h79 | h79
                      · linarith only [h1, h73, h79, hc26, hlam, hphi, ht0b, ht6b, u0elo0]
                      · linarith only [h79, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
      · linarith only [h2, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
    · rcases m.htr 0 1 6 (by decide) (by decide) with h83 | h83
      · rcases m.htr 0 2 3 (by decide) (by decide) with h84 | h84
        · linarith only [h0, h1, h84, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h86 | h86
          · rcases m.htr 0 3 4 (by decide) (by decide) with h87 | h87
            · rcases m.htr 0 4 5 (by decide) (by decide) with h88 | h88
              · rcases m.htr 1 2 3 (by decide) (by decide) with h89 | h89
                · linarith only [h0, h84, h89, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h91 | h91
                  · linarith only [h0, h1, h91, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                  · linarith only [h86, h91, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h94 | h94
                · linarith only [h0, h1, h84, h94, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h96 | h96
                  · linarith only [h0, h1, h96, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                  · linarith only [h86, h96, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo1]
            · linarith only [h0, h1, h86, h87, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h100 | h100
            · rcases m.htr 0 4 5 (by decide) (by decide) with h101 | h101
              · rcases m.htr 1 2 3 (by decide) (by decide) with h102 | h102
                · linarith only [h0, h102, h84, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h104 | h104
                  · linarith only [h0, h101, h104, h86, hc45, hlam, hphi, ht0b, ht56, ht6b, u0elo1]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h106 | h106
                    · linarith only [h0, h1, h106, hc25, hlam, hphi, ht0b, ht56, ht6b, u0elo2]
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h108 | h108
                      · linarith only [h0, h1, h108, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                      · linarith only [h108, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h111 | h111
                · linarith only [h0, h1, h111, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h113 | h113
                  · linarith only [h0, h1, h113, h86, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h115 | h115
                    · linarith only [h0, h1, h115, hc25, hlam, hphi, ht0b, ht56, ht6b, u0elo2]
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h117 | h117
                      · linarith only [h0, h1, h117, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                      · linarith only [h117, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h120 | h120
              · rcases m.htr 1 2 3 (by decide) (by decide) with h121 | h121
                · linarith only [h0, h1, h100, h121, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h123 | h123
                  · linarith only [h0, h1, h100, h123, h83, h86, hc16, hlam, hphi, ht0b, ht6b, u0elo1]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h125 | h125
                    · linarith only [h0, h125, hc25, hlam, hphi, ht0b, ht56, ht6b, u0elo0]
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h127 | h127
                      · linarith only [h0, h1, h100, h127, hc26, hlam, hphi, ht0b, ht6b, u0elo3]
                      · linarith only [h127, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h130 | h130
                · linarith only [h0, h1, h100, h120, h130, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h132 | h132
                  · linarith only [h0, h1, h100, h120, h132, h86, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h134 | h134
                    · linarith only [h0, h1, h100, h120, h134, hc25, hlam, hphi, ht0b, ht56, ht6b, u0elo4]
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h136 | h136
                      · linarith only [h0, h1, h100, h120, h136, hc26, hlam, hphi, ht0b, ht6b, u0elo4]
                      · linarith only [h136, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
      · linarith only [h83, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h140 | h140
    · rcases m.htr 0 1 6 (by decide) (by decide) with h141 | h141
      · rcases m.htr 0 2 3 (by decide) (by decide) with h142 | h142
        · rcases m.htr 0 2 4 (by decide) (by decide) with h143 | h143
          · rcases m.htr 0 3 4 (by decide) (by decide) with h144 | h144
            · rcases m.htr 0 4 5 (by decide) (by decide) with h145 | h145
              · rcases m.htr 1 2 3 (by decide) (by decide) with h146 | h146
                · rcases m.htr 1 2 4 (by decide) (by decide) with h147 | h147
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h148 | h148
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h149 | h149
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h150 | h150
                        · linarith only [h140, h150, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                        · linarith only [h0, h140, h144, h150, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                      · linarith only [h0, h149, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h154 | h154
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h155 | h155
                        · linarith only [h140, h155, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                        · linarith only [h144, h155, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo2]
                      · linarith only [h0, h154, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                  · linarith only [h0, h140, h143, h146, h147, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                · linarith only [h0, h142, h146, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h161 | h161
                · rcases m.htr 1 2 4 (by decide) (by decide) with h162 | h162
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h163 | h163
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h164 | h164
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h165 | h165
                        · linarith only [h140, h165, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                        · linarith only [h144, h165, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo2]
                      · linarith only [h0, h164, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h169 | h169
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h170 | h170
                        · linarith only [h0, h140, h163, h170, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                        · linarith only [h0, h140, h144, h161, h163, h170, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b]
                      · linarith only [h0, h169, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                  · linarith only [h0, h140, h143, h161, h162, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                · linarith only [h0, h142, h161, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h176 | h176
              · rcases m.htr 1 2 3 (by decide) (by decide) with h177 | h177
                · rcases m.htr 1 2 4 (by decide) (by decide) with h178 | h178
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h179 | h179
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h180 | h180
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h181 | h181
                        · linarith only [h140, h144, h181, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h183 | h183
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h184 | h184
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h185 | h185
                              · linarith only [h140, h144, h177, h185, hlam]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h187 | h187
                                · linarith only [h0, h140, h177, h187, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                · linarith only [h187, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                            · linarith only [h183, h184, hc45, hlam, hphi, ht56, u6elo4]
                          · linarith only [h176, h183, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo3]
                      · linarith only [h0, h180, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h193 | h193
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h194 | h194
                        · linarith only [h0, h140, h144, h179, h194, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h196 | h196
                          · linarith only [h178, h179, h196, hlam]
                          · linarith only [h176, h196, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo3]
                      · linarith only [h0, h140, h177, h193, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
                  · linarith only [h0, h140, h143, h177, h178, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                · linarith only [h0, h140, h142, h177, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h202 | h202
                · rcases m.htr 1 2 4 (by decide) (by decide) with h203 | h203
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h204 | h204
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h205 | h205
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h206 | h206
                        · linarith only [h140, h144, h206, hc04, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h208 | h208
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h209 | h209
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h210 | h210
                              · linarith only [h142, h144, h176, h206, h208, h210, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h212 | h212
                                · linarith only [h0, h140, h202, h212, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                · linarith only [h212, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                            · linarith only [h144, h176, h208, h209, hc03, hc46, hlam, hphi, ht34]
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h216 | h216
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h217 | h217
                              · linarith only [h0, h140, h202, h206, h217, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h219 | h219
                                · linarith only [h0, h140, h202, h219, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                · linarith only [h219, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                            · linarith only [h216, hc14, hlam, hphi, ht45, ht56, u6elo4]
                      · linarith only [h0, h205, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h224 | h224
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h225 | h225
                        · linarith only [h0, h140, h144, h204, h225, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h227 | h227
                          · linarith only [h203, h204, h227, hlam]
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h229 | h229
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h230 | h230
                              · linarith only [h0, h140, h202, h204, h225, h230, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h232 | h232
                                · linarith only [h142, h232, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                · linarith only [h232, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                            · linarith only [h229, hc14, hlam, hphi, ht45, ht56, u6elo4]
                      · linarith only [h0, h224, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                  · linarith only [h0, h140, h143, h202, h203, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo3]
                · linarith only [h0, h142, h202, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h239 | h239
            · linarith only [h0, h140, h143, h239, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h241 | h241
              · rcases m.htr 1 2 3 (by decide) (by decide) with h242 | h242
                · rcases m.htr 1 2 4 (by decide) (by decide) with h243 | h243
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h244 | h244
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h245 | h245
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h246 | h246
                        · linarith only [h0, h140, h143, h239, h246, hc03, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h248 | h248
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h249 | h249
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h250 | h250
                              · linarith only [h0, h140, h143, h242, h243, h246, h250, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h252 | h252
                                · linarith only [h140, h242, h252, hc36, hlam, hphi, ht0b, ht6b, u0elo0]
                                · linarith only [h252, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                            · linarith only [h0, h140, h143, h243, h249, hc13, hc46, hlam, hphi, ht34]
                          · linarith only [h0, h140, h143, h242, h243, h248, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h245, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                    · linarith only [h0, h143, h243, h244, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h259 | h259
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h260 | h260
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h261 | h261
                        · linarith only [h140, h261, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h263 | h263
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h264 | h264
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h265 | h265
                              · linarith only [h0, h142, h143, h243, h261, h265, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo3]
                              · linarith only [h0, h140, h242, h243, h265, hc23, hc34, hlam, hphi]
                            · linarith only [h0, h140, h242, h243, h264, hc23, hc46, hlam, hphi, ht34]
                          · linarith only [h0, h140, h242, h243, h263, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h140, h242, h260, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h271 | h271
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h272 | h272
                        · linarith only [h140, h272, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h274 | h274
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h275 | h275
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h276 | h276
                              · linarith only [h0, h142, h143, h259, h272, h274, h276, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo3]
                              · linarith only [h0, h140, h242, h243, h276, hc23, hc34, hlam, hphi]
                            · linarith only [h0, h140, h242, h259, h274, h275, hc23, hc46, hlam, hphi, ht34]
                          · linarith only [h241, h274, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo3]
                      · linarith only [h0, h140, h242, h271, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
                · linarith only [h0, h142, h143, h242, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h283 | h283
                · rcases m.htr 1 2 4 (by decide) (by decide) with h284 | h284
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h285 | h285
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h286 | h286
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h287 | h287
                        · linarith only [h140, h287, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h289 | h289
                          · linarith only [h0, h140, h143, h241, h287, h289, hc13, hc34, hlam, hphi]
                          · linarith only [h0, h140, h143, h283, h284, h289, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h286, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                    · linarith only [h0, h140, h143, h283, h284, h285, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h294 | h294
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h295 | h295
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h296 | h296
                        · linarith only [h140, h296, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h298 | h298
                          · linarith only [h0, h140, h143, h241, h296, h298, hc13, hc34, hlam, hphi]
                          · linarith only [h0, h140, h283, h284, h298, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h140, h283, h295, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h302 | h302
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h303 | h303
                        · linarith only [h140, h303, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h305 | h305
                          · linarith only [h0, h140, h143, h241, h303, h305, hc13, hc34, hlam, hphi]
                          · linarith only [h0, h140, h283, h284, h305, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h140, h283, h302, hc23, hlam, hphi, ht34, ht45, ht56, u6elo2]
                · linarith only [h0, h142, h143, h241, h283, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo4]
        · linarith only [h0, h140, h142, hlam]
      · linarith only [h140, h141, hc13, hlam, hphi, ht34, ht45, ht56, u6elo1]
    · rcases m.htr 0 1 6 (by decide) (by decide) with h312 | h312
      · rcases m.htr 0 2 3 (by decide) (by decide) with h313 | h313
        · rcases m.htr 0 2 4 (by decide) (by decide) with h314 | h314
          · rcases m.htr 0 3 4 (by decide) (by decide) with h315 | h315
            · rcases m.htr 0 4 5 (by decide) (by decide) with h316 | h316
              · rcases m.htr 1 2 3 (by decide) (by decide) with h317 | h317
                · rcases m.htr 1 2 4 (by decide) (by decide) with h318 | h318
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h319 | h319
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h320 | h320
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h321 | h321
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h322 | h322
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h323 | h323
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h324 | h324
                              · linarith only [h313, h324, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                              · linarith only [h315, h324, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo2]
                            · linarith only [h323, hc14, hlam, hphi, ht45, ht56, u6elo4]
                          · linarith only [h313, h315, h316, h318, h322, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                        · linarith only [h140, h313, h315, h321, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo1]
                      · linarith only [h320, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h331 | h331
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h332 | h332
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h333 | h333
                          · linarith only [h318, h319, h333, hlam]
                          · linarith only [h313, h315, h316, h333, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                        · linarith only [h140, h312, h313, h315, h331, h332, hc26, hlam, hphi, ht0b, ht6b, u0elo1]
                      · linarith only [h140, h317, h331, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                  · linarith only [h140, h312, h314, h317, h318, hc16, hlam, hphi, ht0b, ht6b, u0elo1]
                · linarith only [h313, h317, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h340 | h340
                · rcases m.htr 1 2 4 (by decide) (by decide) with h341 | h341
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h342 | h342
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h343 | h343
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h344 | h344
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h345 | h345
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h346 | h346
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h347 | h347
                              · linarith only [h313, h347, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                              · linarith only [h313, h315, h347, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                            · linarith only [h316, h345, h346, hc04, hc46, hlam, hphi]
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h351 | h351
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h352 | h352
                              · linarith only [h313, h352, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                              · linarith only [h313, h315, h352, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                            · linarith only [h351, hc14, hlam, hphi, ht45, ht56, u6elo4]
                        · linarith only [h140, h312, h315, h343, h344, hc26, hlam, hphi, ht0b, ht6b, u0elo3]
                      · linarith only [h343, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h358 | h358
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h359 | h359
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h360 | h360
                          · linarith only [h340, h342, h359, h360, hlam]
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h362 | h362
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h363 | h363
                              · linarith only [h313, h363, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                              · linarith only [h313, h315, h363, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                            · linarith only [h362, hc14, hlam, hphi, ht45, ht56, u6elo4]
                        · linarith only [h140, h315, h359, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo3]
                      · linarith only [h358, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                  · linarith only [h140, h312, h314, h340, h341, hc16, hlam, hphi, ht0b, ht6b, u0elo1]
                · linarith only [h313, h340, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h371 | h371
              · rcases m.htr 1 2 3 (by decide) (by decide) with h372 | h372
                · rcases m.htr 1 2 4 (by decide) (by decide) with h373 | h373
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h374 | h374
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h375 | h375
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h376 | h376
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h377 | h377
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h378 | h378
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h379 | h379
                              · linarith only [h140, h312, h313, h315, h375, h379, hc26, hlam, hphi, ht0b, ht6b, u0elo1]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h381 | h381
                                · linarith only [h314, h379, h381, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                · linarith only [h381, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                            · linarith only [h140, h312, h315, h375, h376, h378, hc26, hlam, hphi, u6elo4]
                          · linarith only [h140, h312, h314, h315, h371, h375, h376, h377, hc26, hlam, hphi, ht0b, ht6b, u0elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h386 | h386
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h387 | h387
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h388 | h388
                              · linarith only [h140, h312, h375, h376, h388, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h390 | h390
                                · linarith only [h314, h388, h390, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                · linarith only [h390, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                            · linarith only [h140, h312, h375, h376, h387, hc26, hlam, hphi, u6elo4]
                          · linarith only [h140, h312, h314, h371, h375, h376, h386, hc26, hlam, hphi, ht0b, ht6b, u0elo1]
                      · linarith only [h375, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h396 | h396
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h397 | h397
                        · linarith only [h140, h315, h372, h374, h397, hc01, hc25, hlam, hphi, ht12]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h399 | h399
                          · linarith only [h373, h374, h399, hlam]
                          · linarith only [h314, h371, h397, h399, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                      · linarith only [h396, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                  · linarith only [h140, h314, h372, h373, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo1]
                · linarith only [h0, h312, h313, h372, hc16, hlam, hphi, ht0b, ht6b, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h405 | h405
                · rcases m.htr 1 2 4 (by decide) (by decide) with h406 | h406
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h407 | h407
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h408 | h408
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h409 | h409
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h410 | h410
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h411 | h411
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h412 | h412
                              · linarith only [h140, h312, h313, h315, h408, h412, hc26, hlam, hphi, ht0b, ht6b, u0elo1]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h414 | h414
                                · linarith only [h314, h412, h414, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                · linarith only [h414, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                            · linarith only [h371, h410, h411, hc04, hc46, hlam, hphi]
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h418 | h418
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h419 | h419
                              · linarith only [h140, h312, h313, h315, h408, h419, hc26, hlam, hphi, ht0b, ht6b, u0elo1]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h421 | h421
                                · linarith only [h314, h419, h421, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                · linarith only [h421, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                            · linarith only [h140, h312, h315, h408, h409, h418, hc26, hlam, hphi, u6elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h425 | h425
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h426 | h426
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h427 | h427
                              · linarith only [h140, h312, h315, h371, h408, h409, h425, h427, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h429 | h429
                                · linarith only [h314, h427, h429, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                · linarith only [h140, h312, h315, h371, h408, h409, h425, h429, hc23, hc26, hc34, hlam, hphi, u6elo3]
                            · linarith only [h140, h312, h315, h371, h408, h425, h426, hc26, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h433 | h433
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h434 | h434
                              · linarith only [h140, h312, h408, h409, h434, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h436 | h436
                                · linarith only [h314, h434, h436, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                · linarith only [h140, h312, h408, h409, h425, h436, hc23, hc26, hc45, hlam, hphi, ht34, u6elo3]
                            · linarith only [h140, h312, h408, h409, h433, hc26, hlam, hphi, u6elo4]
                      · linarith only [h408, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h441 | h441
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h442 | h442
                        · linarith only [h140, h315, h405, h407, h442, hc01, hc25, hlam, hphi, ht12]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h444 | h444
                          · linarith only [h140, h312, h315, h371, h406, h407, h441, h444, hc25, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h446 | h446
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h447 | h447
                              · linarith only [h140, h312, h313, h441, h442, h444, h447, hc26, hc34, hc45, hlam, hphi, ht0b, ht6b, u0elo1]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h449 | h449
                                · linarith only [h314, h447, h449, hc36, hlam, hphi, ht0b, ht6b, u0elo1]
                                · linarith only [h140, h312, h441, h442, h444, h449, hc23, hc26, hc45, hlam, hphi, ht34, u6elo3]
                            · linarith only [h140, h312, h441, h442, h446, hc26, hlam, hphi, u6elo4]
                      · linarith only [h441, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                  · linarith only [h140, h314, h405, h406, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo1]
                · linarith only [h313, h405, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h456 | h456
            · linarith only [h313, h314, h456, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h458 | h458
              · rcases m.htr 1 2 3 (by decide) (by decide) with h459 | h459
                · rcases m.htr 1 2 4 (by decide) (by decide) with h460 | h460
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h461 | h461
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h462 | h462
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h463 | h463
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h464 | h464
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h465 | h465
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h466 | h466
                              · linarith only [h313, h314, h456, h460, h466, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht56, ht6b]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h468 | h468
                                · linarith only [h313, h314, h459, h463, h466, h468, hc12, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                · linarith only [h468, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                            · linarith only [h465, hc14, hlam, hphi, ht45, ht56, u6elo4]
                          · linarith only [h314, h458, h460, h464, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h473 | h473
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h474 | h474
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h475 | h475
                              · linarith only [h313, h463, h475, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h477 | h477
                                · linarith only [h313, h314, h477, hc36, hlam, hphi, ht0b, ht6b, u0elo3]
                                · linarith only [h477, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                            · linarith only [h314, h460, h474, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo4]
                          · linarith only [h313, h314, h460, h473, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h462, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                    · linarith only [h313, h314, h460, h461, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h484 | h484
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h485 | h485
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h486 | h486
                        · linarith only [h140, h456, h459, h460, h486, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h488 | h488
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h489 | h489
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h490 | h490
                              · linarith only [h313, h486, h490, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo1]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h492 | h492
                                · linarith only [h313, h314, h492, hc36, hlam, hphi, ht0b, ht6b, u0elo3]
                                · linarith only [h492, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                            · linarith only [h140, h312, h459, h460, h485, h489, hc26, hlam, hphi, u6elo4]
                          · linarith only [h140, h312, h458, h459, h460, h485, h488, hc26, hlam, hphi, ht0b, ht6b, u0elo3]
                      · linarith only [h140, h312, h459, h485, hc16, hlam, hphi, u6elo2]
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h498 | h498
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h499 | h499
                        · linarith only [h140, h312, h456, h459, h460, h498, h499, hc24, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h501 | h501
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h502 | h502
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h503 | h503
                              · linarith only [h140, h312, h498, h499, h503, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h505 | h505
                                · linarith only [h313, h314, h505, hc36, hlam, hphi, ht0b, ht6b, u0elo3]
                                · linarith only [h505, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                            · linarith only [h140, h312, h459, h484, h498, h501, h502, hc26, hlam, hphi, u6elo4]
                          · linarith only [h458, h501, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo3]
                      · linarith only [h140, h459, h498, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                · linarith only [h0, h312, h313, h314, h459, hc16, hlam, hphi, ht0b, ht6b, u0elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h512 | h512
                · rcases m.htr 1 2 4 (by decide) (by decide) with h513 | h513
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h514 | h514
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h515 | h515
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h516 | h516
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h517 | h517
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h518 | h518
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h519 | h519
                              · linarith only [h140, h312, h313, h314, h456, h458, h512, h515, h516, h517, h519, hc12, hc26, hlam, hphi, ht01, ht0b, ht6b]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h521 | h521
                                · linarith only [h313, h314, h458, h512, h516, h517, h521, hc12, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                · linarith only [h521, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                            · linarith only [h314, h458, h517, h518, hc02, hc46, hlam, hphi, ht23, ht34]
                          · linarith only [h313, h314, h513, h517, hc23, hc45, hlam, hphi, ht34]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h526 | h526
                          · linarith only [h313, h314, h458, h516, h526, hc23, hc34, hlam, hphi]
                          · linarith only [h313, h314, h513, h526, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h515, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                    · linarith only [h313, h314, h513, h514, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht56, ht6b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h531 | h531
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h532 | h532
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h533 | h533
                        · linarith only [h140, h456, h512, h513, h533, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h535 | h535
                          · linarith only [h313, h314, h458, h533, h535, hc23, hc34, hlam, hphi]
                          · linarith only [h513, h531, h535, hlam]
                      · linarith only [h140, h512, h532, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h539 | h539
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h540 | h540
                        · linarith only [h140, h312, h456, h512, h531, h539, h540, hc25, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h542 | h542
                          · linarith only [h313, h314, h458, h540, h542, hc23, hc34, hlam, hphi]
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h544 | h544
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h545 | h545
                              · linarith only [h313, h314, h458, h545, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo4]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h547 | h547
                                · linarith only [h313, h314, h458, h547, hc36, hlam, hphi, ht0b, ht6b, u0elo4]
                                · linarith only [h140, h312, h512, h513, h539, h542, h547, hc23, hc26, hc45, hlam, hphi, ht34, u6elo3]
                            · linarith only [h140, h312, h512, h513, h539, h544, hc26, hlam, hphi, u6elo4]
                      · linarith only [h140, h512, h539, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                · linarith only [h0, h312, h313, h314, h458, h512, hc16, hlam, hphi, ht0b, ht6b, u0elo4]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h553 | h553
          · rcases m.htr 0 3 4 (by decide) (by decide) with h554 | h554
            · rcases m.htr 0 4 5 (by decide) (by decide) with h555 | h555
              · rcases m.htr 1 2 3 (by decide) (by decide) with h556 | h556
                · rcases m.htr 1 2 4 (by decide) (by decide) with h557 | h557
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h558 | h558
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h559 | h559
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h560 | h560
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h561 | h561
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h562 | h562
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h563 | h563
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h564 | h564
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h565 | h565
                                  · linarith only [h313, h553, h565, hc45, hlam, hphi, ht0b, ht56, ht6b, u0elo2]
                                  · linarith only [h313, h553, h555, h565, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                · linarith only [h313, h564, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo3]
                              · linarith only [h0, h313, h554, h563, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                            · linarith only [h562, hc14, hlam, hphi, ht45, ht56, u6elo4]
                          · linarith only [h553, h555, h557, h561, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                        · linarith only [h0, h313, h554, h556, h560, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                      · linarith only [h559, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                    · linarith only [h313, h553, h555, h556, h558, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                  · linarith only [h313, h553, h555, h556, h557, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht56, ht6b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h576 | h576
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h577 | h577
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h578 | h578
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h579 | h579
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h580 | h580
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h581 | h581
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h582 | h582
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h583 | h583
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h584 | h584
                                  · linarith only [h553, h584, hc45, hlam, hphi, ht0b, ht56, ht6b, u0elo1]
                                  · linarith only [h555, h584, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo3]
                                · linarith only [h583, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                              · linarith only [h0, h556, h582, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h580, h581, hc45, hlam, hphi, ht56, u6elo4]
                          · linarith only [h313, h553, h555, h580, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                        · linarith only [h554, h579, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo2]
                      · linarith only [h0, h578, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h593 | h593
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h594 | h594
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h595 | h595
                          · linarith only [h576, h577, h595, hlam]
                          · linarith only [h313, h553, h555, h595, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                        · linarith only [h0, h312, h554, h556, h593, h594, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                      · linarith only [h0, h593, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                  · linarith only [h0, h312, h313, h553, h576, hc16, hlam, hphi, ht0b, ht6b, u0elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h601 | h601
                · rcases m.htr 1 2 4 (by decide) (by decide) with h602 | h602
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h603 | h603
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h604 | h604
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h605 | h605
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h606 | h606
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h607 | h607
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h608 | h608
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h609 | h609
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h610 | h610
                                  · linarith only [h313, h553, h555, h610, hc04, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h612 | h612
                                    · linarith only [h553, h555, h608, h612, hlam]
                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h614 | h614
                                      · linarith only [h313, h553, h608, h614, hc46, hlam, hphi, ht0b, ht6b, u0elo2]
                                      · linarith only [h614, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                · linarith only [h609, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                              · linarith only [h313, h554, h608, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                            · linarith only [h607, hc14, hlam, hphi, ht45, ht56, u6elo4]
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h620 | h620
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h621 | h621
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h622 | h622
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h623 | h623
                                  · linarith only [h553, h606, h620, h623, hc46, hlam, hphi, ht0b, ht6b, u0elo3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h625 | h625
                                    · linarith only [h554, h555, h625, hc04, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h627 | h627
                                      · linarith only [h553, h621, h627, hc46, hlam, hphi, ht0b, ht6b, u0elo1]
                                      · linarith only [h606, h620, h627, hc34, hc45, hlam, hphi]
                                · linarith only [h313, h622, hc02, hlam, hphi, ht23, ht34, ht45, ht56, u6elo3]
                              · linarith only [h0, h313, h554, h621, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                            · linarith only [h620, hc14, hlam, hphi, ht45, ht56, u6elo4]
                        · linarith only [h0, h312, h313, h554, h601, h604, h605, hc26, hlam, hphi, ht0b, ht6b, u0elo3]
                      · linarith only [h0, h313, h601, h604, hc01, hc26, hlam, hphi, ht12]
                    · linarith only [h313, h553, h601, h603, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                  · linarith only [h313, h553, h601, h602, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h637 | h637
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h638 | h638
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h639 | h639
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h640 | h640
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h641 | h641
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h642 | h642
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h643 | h643
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h644 | h644
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h645 | h645
                                  · linarith only [h553, h555, h645, hc04, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h647 | h647
                                    · linarith only [h553, h555, h643, h647, hlam]
                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h649 | h649
                                      · linarith only [h313, h553, h643, h649, hc46, hlam, hphi, ht0b, ht6b, u0elo2]
                                      · linarith only [h649, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                · linarith only [h553, h555, h601, h637, h641, h643, h644, hc34, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                              · linarith only [h553, h555, h601, h637, h641, h643, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                            · linarith only [h553, h555, h641, h642, hc24, hc46, hlam, hphi]
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h655 | h655
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h656 | h656
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h657 | h657
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h658 | h658
                                  · linarith only [h553, h641, h658, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h660 | h660
                                    · linarith only [h553, h641, h655, h656, h660, hc46, hlam, hphi, ht0b, ht6b, u0elo3]
                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h662 | h662
                                      · linarith only [h313, h553, h656, h662, hc46, hlam, hphi, ht0b, ht6b, u0elo2]
                                      · linarith only [h641, h655, h662, hc34, hc45, hlam, hphi]
                                · linarith only [h0, h601, h657, hc01, hc36, hlam, hphi, ht12, ht23]
                              · linarith only [h0, h312, h601, h639, h656, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                            · linarith only [h655, hc14, hlam, hphi, ht45, ht56, u6elo4]
                        · linarith only [h0, h312, h554, h601, h639, h640, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                      · linarith only [h0, h639, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h670 | h670
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h671 | h671
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h672 | h672
                          · linarith only [h637, h638, h672, hlam]
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h674 | h674
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h675 | h675
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h676 | h676
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h677 | h677
                                  · linarith only [h553, h672, h677, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h679 | h679
                                    · linarith only [h0, h312, h638, h670, h676, h677, h679, hc34, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h681 | h681
                                      · linarith only [h313, h553, h675, h681, hc46, hlam, hphi, ht0b, ht6b, u0elo2]
                                      · linarith only [h0, h312, h638, h670, h676, h677, h681, hc34, hc36, hc45, hlam, hphi, u6elo4]
                                · linarith only [h0, h601, h676, hc01, hc36, hlam, hphi, ht12, ht23]
                              · linarith only [h0, h312, h601, h674, h675, hc34, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                            · linarith only [h674, hc14, hlam, hphi, ht45, ht56, u6elo4]
                        · linarith only [h0, h312, h554, h601, h670, h671, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                      · linarith only [h0, h670, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                  · linarith only [h0, h312, h313, h553, h637, hc16, hlam, hphi, ht0b, ht6b, u0elo2]
            · linarith only [h313, h553, h554, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h691 | h691
            · rcases m.htr 0 4 5 (by decide) (by decide) with h692 | h692
              · rcases m.htr 1 2 3 (by decide) (by decide) with h693 | h693
                · rcases m.htr 1 2 4 (by decide) (by decide) with h694 | h694
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h695 | h695
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h696 | h696
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h697 | h697
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h698 | h698
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h699 | h699
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h700 | h700
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h701 | h701
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h702 | h702
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h703 | h703
                                    · linarith only [h691, h703, hc45, hlam, hphi, ht0b, ht56, ht6b, u0elo2]
                                    · linarith only [h691, h692, h703, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                  · linarith only [h553, h691, h692, h702, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                                · linarith only [h701, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                              · linarith only [h0, h313, h691, h700, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                            · linarith only [h0, h312, h553, h694, h696, h699, hc26, hlam, hphi, u6elo4]
                          · linarith only [h0, h312, h553, h691, h692, h694, h696, h698, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                        · linarith only [h691, h697, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo2]
                      · linarith only [h696, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                    · linarith only [h0, h313, h693, h695, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h312, h313, h693, h694, hc16, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h715 | h715
                  · linarith only [h0, h312, h553, h693, h715, hc16, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h717 | h717
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h718 | h718
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h719 | h719
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h720 | h720
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h721 | h721
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h722 | h722
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h723 | h723
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h724 | h724
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h725 | h725
                                    · linarith only [h691, h725, hc45, hlam, hphi, ht0b, ht56, ht6b, u0elo2]
                                    · linarith only [h691, h692, h725, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                  · linarith only [h691, h692, h715, h724, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                                · linarith only [h723, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                              · linarith only [h0, h693, h722, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h312, h715, h718, h721, hc26, hlam, hphi, u6elo4]
                          · linarith only [h0, h312, h691, h692, h715, h718, h720, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                        · linarith only [h691, h719, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo2]
                      · linarith only [h0, h718, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h735 | h735
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h736 | h736
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h737 | h737
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h738 | h738
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h739 | h739
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h740 | h740
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h741 | h741
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h742 | h742
                                    · linarith only [h691, h742, hc45, hlam, hphi, ht0b, ht56, ht6b, u0elo2]
                                    · linarith only [h691, h692, h742, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                  · linarith only [h691, h692, h741, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                                · linarith only [h0, h715, h739, h740, hc01, hc36, hlam, hphi, ht12, ht23]
                              · linarith only [h691, h739, hc23, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo2]
                            · linarith only [h0, h312, h717, h735, h737, h738, hc26, hlam, hphi, u6elo4]
                          · linarith only [h691, h692, h737, hc14, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo2]
                        · linarith only [h0, h312, h691, h693, h735, h736, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                      · linarith only [h0, h735, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h752 | h752
                · rcases m.htr 1 2 4 (by decide) (by decide) with h753 | h753
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h754 | h754
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h755 | h755
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h756 | h756
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h757 | h757
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h758 | h758
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h759 | h759
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h760 | h760
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h761 | h761
                                  · linarith only [h0, h312, h553, h692, h752, h755, h759, h760, h761, hc12, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                  · linarith only [h0, h312, h553, h755, h756, h757, h760, h761, hc13, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                · linarith only [h760, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                              · linarith only [h0, h313, h691, h759, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                            · linarith only [h758, hc14, hlam, hphi, ht45, ht56, u6elo4]
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h767 | h767
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h768 | h768
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h769 | h769
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h770 | h770
                                  · linarith only [h753, h757, h770, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h772 | h772
                                    · linarith only [h0, h312, h553, h691, h753, h755, h757, h769, h772, hc36, hlam, hphi, ht0b, ht6b, u0elo2]
                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h774 | h774
                                      · linarith only [h691, h774, hc46, hlam, hphi, ht0b, ht6b, u0elo2]
                                      · linarith only [h0, h312, h553, h753, h755, h757, h769, h774, hc34, hc36, hc45, hlam, hphi, u6elo4]
                                · linarith only [h0, h553, h768, h769, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                              · linarith only [h0, h312, h313, h691, h755, h768, hc26, hlam, hphi, ht0b, ht6b, u0elo2]
                            · linarith only [h0, h312, h553, h753, h755, h767, hc26, hlam, hphi, u6elo4]
                        · linarith only [h691, h756, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo2]
                      · linarith only [h755, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                    · linarith only [h0, h312, h553, h753, h754, hc16, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b]
                  · linarith only [h0, h312, h313, h752, h753, hc16, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h784 | h784
                  · linarith only [h0, h312, h553, h752, h784, hc16, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h786 | h786
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h787 | h787
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h788 | h788
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h789 | h789
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h790 | h790
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h791 | h791
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h792 | h792
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h793 | h793
                                  · linarith only [h0, h312, h553, h692, h784, h786, h787, h791, h792, h793, hc23, hc36, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                  · linarith only [h784, h786, h788, h789, h793, hc13, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b]
                                · linarith only [h752, h792, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                              · linarith only [h0, h553, h691, h692, h752, h786, h789, h791, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                            · linarith only [h0, h312, h553, h692, h787, h789, h790, hc26, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                          · linarith only [h784, h786, h789, hlam]
                        · linarith only [h691, h752, h788, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                      · linarith only [h0, h312, h787, hc16, hlam, hphi, u6elo2]
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h802 | h802
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h803 | h803
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h804 | h804
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h805 | h805
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h806 | h806
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h807 | h807
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h808 | h808
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h809 | h809
                                    · linarith only [h0, h312, h553, h691, h692, h802, h807, h809, hc36, hlam, hphi, ht0b, ht6b, u0elo2]
                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h811 | h811
                                      · linarith only [h691, h811, hc46, hlam, hphi, ht0b, ht6b, u0elo2]
                                      · linarith only [h811, hc34, hlam, hphi, ht45, ht56, u6elo4]
                                  · linarith only [h784, h804, h808, hlam]
                                · linarith only [h0, h553, h692, h752, h803, h804, h807, hc01, hc36, hlam, hphi, ht12, ht23]
                              · linarith only [h0, h312, h553, h692, h752, h802, h803, h804, h806, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                            · linarith only [h0, h312, h553, h692, h802, h804, h805, hc26, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h818 | h818
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h819 | h819
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h820 | h820
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h821 | h821
                                  · linarith only [h0, h312, h784, h802, h804, h820, h821, hc24, hc36, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                  · linarith only [h0, h312, h784, h802, h820, h821, hc36, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                · linarith only [h820, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                              · linarith only [h0, h691, h752, h819, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                            · linarith only [h0, h312, h784, h802, h818, hc26, hlam, hphi, u6elo4]
                        · linarith only [h691, h803, hc13, hlam, hphi, ht0b, ht34, ht45, ht56, ht6b, u0elo2]
                      · linarith only [h0, h802, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h829 | h829
              · rcases m.htr 1 2 3 (by decide) (by decide) with h830 | h830
                · rcases m.htr 1 2 4 (by decide) (by decide) with h831 | h831
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h832 | h832
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h833 | h833
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h834 | h834
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h835 | h835
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h836 | h836
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h837 | h837
                              · linarith only [h0, h312, h313, h691, h830, h833, h837, hc12, hc26, hlam, hphi, ht01, ht0b, ht6b]
                              · linarith only [h0, h312, h313, h833, h834, h837, hc13, hc26, hlam, hphi, ht01, ht0b, ht6b]
                            · linarith only [h836, hc14, hlam, hphi, ht45, ht56, u6elo4]
                          · linarith only [h0, h312, h313, h691, h829, h833, h834, h835, hc26, hlam, hphi, ht0b, ht6b, u0elo3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h842 | h842
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h843 | h843
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h844 | h844
                              · linarith only [h140, h312, h833, h834, h844, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h846 | h846
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h847 | h847
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h848 | h848
                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h849 | h849
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h850 | h850
                                        · linarith only [h829, h850, hc56, hlam, hphi, ht0b, ht6b, u0elo3]
                                        · linarith only [h850, hc45, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h0, h312, h313, h830, h833, h834, h846, h849, hc36, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                    · linarith only [h0, h312, h313, h830, h833, h834, h846, h848, hc36, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                  · linarith only [h0, h312, h313, h829, h833, h844, h846, h847, hc36, hlam, hphi, ht0b, ht6b, u0elo3]
                                · linarith only [h0, h313, h846, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                            · linarith only [h0, h312, h313, h830, h833, h834, h843, hc26, hlam, hphi, u6elo4]
                          · linarith only [h0, h312, h313, h829, h830, h833, h834, h842, hc26, hlam, hphi, ht0b, ht6b, u0elo3]
                      · linarith only [h833, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                    · linarith only [h0, h313, h830, h832, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h312, h313, h830, h831, hc16, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h862 | h862
                  · linarith only [h0, h312, h553, h830, h862, hc16, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h864 | h864
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h865 | h865
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h866 | h866
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h867 | h867
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h868 | h868
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h869 | h869
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h870 | h870
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h871 | h871
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h872 | h872
                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h873 | h873
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h874 | h874
                                        · linarith only [h829, h874, hc56, hlam, hphi, ht0b, ht6b, u0elo3]
                                        · linarith only [h874, hc45, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h0, h312, h313, h691, h865, h870, h873, hc36, hlam, hphi, u6elo4]
                                    · linarith only [h0, h312, h313, h691, h829, h865, h870, h872, hc36, hlam, hphi, ht0b, ht6b, u0elo3]
                                  · linarith only [h829, h862, h871, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo3]
                                · linarith only [h870, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                              · linarith only [h830, h866, h869, hlam]
                            · linarith only [h0, h312, h313, h691, h865, h866, h868, hc26, hlam, hphi, u6elo4]
                          · linarith only [h0, h312, h313, h691, h829, h865, h866, h867, hc26, hlam, hphi, ht0b, ht6b, u0elo3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h884 | h884
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h885 | h885
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h886 | h886
                              · linarith only [h140, h312, h865, h866, h886, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                              · linarith only [h0, h312, h830, h865, h886, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                            · linarith only [h885, hc14, hlam, hphi, ht45, ht56, u6elo4]
                          · linarith only [h0, h312, h829, h830, h865, h866, h884, hc26, hlam, hphi, ht0b, ht6b, u0elo3]
                      · linarith only [h0, h865, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h892 | h892
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h893 | h893
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h894 | h894
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h895 | h895
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h896 | h896
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h897 | h897
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h898 | h898
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h899 | h899
                                    · rcases m.htr 3 4 6 (by decide) (by decide) with h900 | h900
                                      · rcases m.htr 4 5 6 (by decide) (by decide) with h901 | h901
                                        · linarith only [h829, h901, hc56, hlam, hphi, ht0b, ht6b, u0elo3]
                                        · linarith only [h901, hc45, hlam, hphi, ht56, u6elo5]
                                      · linarith only [h0, h312, h313, h691, h892, h897, h900, hc36, hlam, hphi, u6elo4]
                                    · linarith only [h0, h312, h313, h691, h829, h892, h897, h899, hc36, hlam, hphi, ht0b, ht6b, u0elo3]
                                  · linarith only [h829, h898, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo3]
                                · linarith only [h0, h313, h691, h830, h893, h897, hc01, hc36, hlam, hphi, ht12, ht23]
                              · linarith only [h830, h893, h896, hlam]
                            · linarith only [h0, h312, h313, h691, h892, h893, h895, hc26, hlam, hphi, u6elo4]
                          · linarith only [h0, h312, h313, h691, h829, h892, h893, h894, hc26, hlam, hphi, ht0b, ht6b, u0elo3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h911 | h911
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h912 | h912
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h913 | h913
                              · linarith only [h140, h312, h892, h893, h913, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                              · linarith only [h0, h312, h830, h892, h913, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                            · linarith only [h0, h312, h830, h892, h893, h912, hc26, hlam, hphi, u6elo4]
                          · linarith only [h0, h312, h829, h830, h892, h893, h911, hc26, hlam, hphi, ht0b, ht6b, u0elo3]
                      · linarith only [h0, h892, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h919 | h919
                · rcases m.htr 1 2 4 (by decide) (by decide) with h920 | h920
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h921 | h921
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h922 | h922
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h923 | h923
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h924 | h924
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h925 | h925
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h926 | h926
                              · linarith only [h0, h312, h313, h691, h919, h922, h926, hc12, hc26, hlam, hphi, ht01, ht0b, ht6b]
                              · linarith only [h0, h312, h313, h919, h922, h923, h926, hc12, hc26, hlam, hphi, ht01, ht0b, ht6b]
                            · linarith only [h829, h924, h925, hc04, hc46, hlam, hphi]
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h930 | h930
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h931 | h931
                              · linarith only [h0, h312, h313, h691, h919, h922, h931, hc12, hc26, hlam, hphi, ht01, ht0b, ht6b]
                              · linarith only [h0, h312, h313, h922, h923, h931, hc13, hc26, hlam, hphi, ht01, ht0b, ht6b]
                            · linarith only [h930, hc14, hlam, hphi, ht45, ht56, u6elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h935 | h935
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h936 | h936
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h937 | h937
                              · linarith only [h140, h312, h922, h923, h937, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h939 | h939
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h940 | h940
                                  · linarith only [h0, h312, h313, h691, h829, h920, h922, h939, h940, hc12, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                  · linarith only [h0, h312, h553, h922, h935, h939, h940, hc14, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                · linarith only [h0, h313, h939, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                            · linarith only [h936, hc14, hlam, hphi, ht45, ht56, u6elo4]
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h945 | h945
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h946 | h946
                              · linarith only [h0, h312, h313, h691, h919, h922, h923, h935, h946, hc26, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h948 | h948
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h949 | h949
                                  · linarith only [h140, h312, h922, h923, h935, h948, h949, hc24, hc36, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h951 | h951
                                    · linarith only [h0, h312, h313, h919, h922, h923, h935, h948, h951, hc34, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                                    · linarith only [h0, h312, h313, h919, h922, h923, h948, h951, hc36, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                · linarith only [h0, h313, h948, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                            · linarith only [h0, h312, h313, h919, h922, h923, h945, hc26, hlam, hphi, u6elo4]
                      · linarith only [h922, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo2]
                    · linarith only [h0, h312, h313, h919, h921, hc16, hc25, hlam, hphi, ht01, ht0b, ht12, ht6b]
                  · linarith only [h0, h312, h313, h919, h920, hc16, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h959 | h959
                  · linarith only [h0, h312, h553, h919, h959, hc16, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h961 | h961
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h962 | h962
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h963 | h963
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h964 | h964
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h965 | h965
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h966 | h966
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h967 | h967
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h968 | h968
                                  · linarith only [h0, h312, h313, h691, h829, h959, h961, h962, h966, h967, h968, hc23, hc36, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                  · linarith only [h959, h961, h963, h964, h968, hc13, hc25, hlam, hphi, ht01, ht0b, ht56, ht6b]
                                · linarith only [h313, h691, h829, h959, h961, h964, h966, h967, hc02, hc36, hlam, hphi, ht23]
                              · linarith only [h0, h313, h691, h829, h919, h961, h964, h966, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h965, hc14, hlam, hphi, ht45, ht56, u6elo4]
                          · linarith only [h959, h961, h964, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h975 | h975
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h976 | h976
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h977 | h977
                              · linarith only [h140, h312, h962, h963, h977, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                              · linarith only [h0, h312, h919, h962, h977, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                            · linarith only [h976, hc14, hlam, hphi, ht45, ht56, u6elo4]
                          · linarith only [h919, h961, h963, h975, hlam]
                      · linarith only [h0, h962, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                    · rcases m.htr 1 2 6 (by decide) (by decide) with h983 | h983
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h984 | h984
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h985 | h985
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h986 | h986
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h987 | h987
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h988 | h988
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h989 | h989
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h990 | h990
                                    · linarith only [h0, h312, h313, h691, h829, h983, h984, h988, h990, hc13, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                    · linarith only [h0, h312, h313, h691, h983, h985, h988, h990, hc14, hc36, hlam, hphi, ht01, ht0b, ht6b]
                                  · linarith only [h959, h985, h989, hlam]
                                · linarith only [h919, h988, hc13, hlam, hphi, ht34, ht45, ht56, u6elo3]
                              · linarith only [h0, h313, h691, h829, h919, h984, h985, h987, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h312, h313, h691, h829, h983, h985, h986, hc26, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h997 | h997
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h998 | h998
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h999 | h999
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1000 | h1000
                                  · linarith only [h0, h1000, h312, h959, h983, h985, h999, hc24, hc36, hlam, hphi, ht01, ht0b, ht12, ht6b]
                                  · linarith only [h0, h1000, h312, h959, h983, h999, hc36, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                                · linarith only [h999, hc23, hlam, hphi, ht34, ht45, ht56, u6elo3]
                              · linarith only [h919, h984, h998, hlam]
                            · linarith only [h0, h313, h691, h984, h997, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1006 | h1006
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h1007 | h1007
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1008 | h1008
                              · linarith only [h1008, h140, h312, h983, h984, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                              · linarith only [h0, h1008, h312, h919, h983, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                            · linarith only [h0, h1006, h1007, h312, h313, h691, h829, h983, hc26, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b]
                          · rcases m.htr 1 4 6 (by decide) (by decide) with h1012 | h1012
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1013 | h1013
                              · linarith only [h0, h1013, h312, h919, h983, h984, hc23, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b]
                              · linarith only [h0, h1013, h312, h919, h983, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b]
                            · linarith only [h1012, hc14, hlam, hphi, ht45, ht56, u6elo4]
                      · linarith only [h0, h983, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
      · linarith only [h312, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo1]

theorem n8l_sBT8_H_L_H_R (m : N8Model)
    (hb0 : CMSig2_8_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_H_R m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have h0elo := hb0.1
  have h6ehi := hb6.1
  have u0elo5 := h0elo (m.d 0 6) (by simp)
  have u6ehi0 := h6ehi (m.d 0 6) (by simp)
  linarith only [hlam, hphi, ht0b, ht6b, u0elo5, u6ehi0]

theorem n8l_sBT8_H_L_M_LI (m : N8Model)
    (hb0 : CMSig2_8_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_M_LI m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc06 := m.hcor 0 6 (by decide)
  have hc16 := m.hcor 1 6 (by decide)
  have hc26 := m.hcor 2 6 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have h0elo := hb0.1
  have h6elo := hb6.1
  have h6bigk := hb6.2.2.2
  have u0elo5 := h0elo (m.d 0 6) (by simp)
  have u6elo1 := h6elo (m.d 1 6) (by simp)
  have u6elo2 := h6elo (m.d 2 6) (by simp)
  have u6elo3 := h6elo (m.d 3 6) (by simp)
  have u6elo4 := h6elo (m.d 4 6) (by simp)
  have u6elo5 := h6elo (m.d 5 6) (by simp)
  rcases h6bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc26, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc36, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc46, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u6elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc26, hlam, hphi, p0_1, u6elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc36, hlam, hphi, p0_1, u6elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc46, hlam, hphi, p0_1, u6elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, p0_1, u6elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u6elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u6elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc36, hlam, hphi, p0_1, u6elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc46, hlam, hphi, p0_1, u6elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, p0_1, u6elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u6elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u6elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc26, hlam, hphi, p0_1, u6elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc46, hlam, hphi, p0_1, u6elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, p0_1, u6elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u6elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u6elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc26, hlam, hphi, p0_1, u6elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc36, hlam, hphi, p0_1, u6elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, p0_1, u6elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u6elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u6elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc26, hlam, hphi, p0_1, u6elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc36, hlam, hphi, p0_1, u6elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc46, hlam, hphi, p0_1, u6elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n8l_sBT8_H_L_M_LR (m : N8Model)
    (hb0 : CMSig2_8_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_M_LR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0elo := hb0.1
  have h6elo := hb6.1
  have h6ehi := hb6.2.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u6elo1 := h6elo (m.d 1 6) (by simp)
  have u6elo2 := h6elo (m.d 2 6) (by simp)
  have u6elo3 := h6elo (m.d 3 6) (by simp)
  have u6elo4 := h6elo (m.d 4 6) (by simp)
  have u6elo5 := h6elo (m.d 5 6) (by simp)
  have u6ehi7 := h6ehi (m.d 1 6) (by simp)
  have u6ehi8 := h6ehi (m.d 2 6) (by simp)
  have u6ehi9 := h6ehi (m.d 3 6) (by simp)
  have u6ehi10 := h6ehi (m.d 4 6) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 6 (by decide) (by decide) with h3 | h3
        · linarith only [h3, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi7]
        · linarith only [h0, h3, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo1]
      · rcases m.htr 0 1 6 (by decide) (by decide) with h6 | h6
        · linarith only [h6, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi7]
        · linarith only [h1, h6, hc13, hlam, hphi, ht34, ht45, ht56, u6elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h9 | h9
      · rcases m.htr 0 1 6 (by decide) (by decide) with h10 | h10
        · linarith only [h10, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi7]
        · linarith only [h10, h9, hc15, hlam, hphi, ht56, u6elo1]
      · rcases m.htr 0 1 6 (by decide) (by decide) with h13 | h13
        · linarith only [h13, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi7]
        · linarith only [h0, h13, hc12, hlam, hphi, ht23, ht34, ht45, ht56, u6elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h16 | h16
    · rcases m.htr 0 1 5 (by decide) (by decide) with h17 | h17
      · rcases m.htr 0 1 6 (by decide) (by decide) with h18 | h18
        · linarith only [h18, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi7]
        · linarith only [h17, h18, hc15, hlam, hphi, ht56, u6elo1]
      · rcases m.htr 0 1 6 (by decide) (by decide) with h21 | h21
        · linarith only [h21, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi7]
        · linarith only [h16, h21, hc13, hlam, hphi, ht34, ht45, ht56, u6elo1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h24 | h24
      · rcases m.htr 0 1 6 (by decide) (by decide) with h25 | h25
        · linarith only [h25, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi7]
        · linarith only [h24, h25, hc15, hlam, hphi, ht56, u6elo1]
      · rcases m.htr 0 1 6 (by decide) (by decide) with h28 | h28
        · linarith only [h28, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi7]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h30 | h30
          · rcases m.htr 0 3 5 (by decide) (by decide) with h31 | h31
            · rcases m.htr 0 3 6 (by decide) (by decide) with h32 | h32
              · linarith only [h32, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi9]
              · linarith only [h30, h32, hc34, hlam, hphi, ht45, ht56, u6elo3]
            · rcases m.htr 0 3 6 (by decide) (by decide) with h35 | h35
              · linarith only [h35, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi9]
              · linarith only [h30, h35, hc34, hlam, hphi, ht45, ht56, u6elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h38 | h38
            · rcases m.htr 0 3 6 (by decide) (by decide) with h39 | h39
              · linarith only [h39, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi9]
              · linarith only [h38, h39, hc35, hlam, hphi, ht56, u6elo3]
            · rcases m.htr 0 3 6 (by decide) (by decide) with h42 | h42
              · linarith only [h42, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi9]
              · rcases m.htr 0 4 6 (by decide) (by decide) with h44 | h44
                · linarith only [h44, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi10]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h46 | h46
                  · rcases m.htr 1 2 6 (by decide) (by decide) with h47 | h47
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h48 | h48
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h49 | h49
                        · rcases m.htr 1 3 6 (by decide) (by decide) with h50 | h50
                          · rcases m.htr 1 5 6 (by decide) (by decide) with h51 | h51
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h52 | h52
                              · linarith only [h16, h38, h46, h52, hc01, hc12, hlam, hphi]
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h54 | h54
                                · linarith only [h16, h42, h52, h54, hc01, hc35, hlam, hphi, ht12, ht23]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h56 | h56
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h57 | h57
                                    · linarith only [h16, h30, h44, h48, h57, hc01, hc13, hlam, hphi]
                                    · linarith only [h56, h57, hc45, hlam, hphi, ht56, u6elo4]
                                  · rcases m.htr 3 4 6 (by decide) (by decide) with h60 | h60
                                    · linarith only [h16, h30, h44, h56, h60, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                    · linarith only [h16, h30, h60, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo4]
                            · linarith only [h16, h38, h49, h51, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo5]
                          · linarith only [h16, h50, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                        · linarith only [h16, h30, h48, h49, hc01, hc35, hlam, hphi, ht12, ht23]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h66 | h66
                        · linarith only [h16, h38, h48, h66, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases m.htr 1 3 6 (by decide) (by decide) with h68 | h68
                          · linarith only [h16, h42, h48, h68, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h16, h68, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                    · linarith only [h0, h47, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]
                  · rcases m.htr 1 2 6 (by decide) (by decide) with h72 | h72
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h73 | h73
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h74 | h74
                        · rcases m.htr 1 3 6 (by decide) (by decide) with h75 | h75
                          · rcases m.htr 1 5 6 (by decide) (by decide) with h76 | h76
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h77 | h77
                              · rcases m.htr 2 3 6 (by decide) (by decide) with h78 | h78
                                · linarith only [h16, h42, h46, h72, h78, hc01, hc23, hlam, hphi, ht12]
                                · linarith only [h46, h72, h78, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi8]
                              · linarith only [h16, h30, h44, h46, h72, h77, hc01, hc35, hlam, hphi, ht12, ht23, u6ehi8, u6elo4]
                            · linarith only [h24, h76, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo5]
                          · linarith only [h16, h30, h73, h75, hc01, hc36, hlam, hphi, ht12, ht23]
                        · linarith only [h16, h30, h73, h74, hc01, hc35, hlam, hphi, ht12, ht23]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h85 | h85
                        · linarith only [h16, h38, h73, h85, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases m.htr 1 3 6 (by decide) (by decide) with h87 | h87
                          · linarith only [h16, h42, h73, h87, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h16, h87, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo3]
                    · linarith only [h0, h72, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, u6elo2]

theorem n8l_sBT8_H_R_H_L (m : N8Model)
    (hb0 : CMSig2_8_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_H_L m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0ehi := hb0.1
  have h6elo := hb6.1
  have u0ehi5 := h0ehi (m.d 0 6) (by simp)
  have u6elo0 := h6elo (m.d 0 6) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi5, u6elo0]

theorem n8l_sBT8_H_R_H_R (m : N8Model)
    (hb0 : CMSig2_8_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_H_R m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc26 := m.hcor 2 6 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0ehi := hb0.1
  have h6ehi := hb6.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u6ehi2 := h6ehi (m.d 2 6) (by simp)
  have u6ehi3 := h6ehi (m.d 3 6) (by simp)
  have u6ehi4 := h6ehi (m.d 4 6) (by simp)
  have u6ehi5 := h6ehi (m.d 5 6) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 6 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht6b, u6ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 2 3 6 (by decide) (by decide) with h10 | h10
                    · linarith only [h10, h4, h6, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                        · linarith only [h10, h13, h4, h6, h8, hc36, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b]
                        · linarith only [h10, h12, h13, h4, h6, h8, hc34, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                        · linarith only [h10, h12, h16, h4, h6, h8, hc24, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                        · rcases m.htr 3 4 6 (by decide) (by decide) with h18 | h18
                          · linarith only [h0, h1, h18, h2, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                          · linarith only [h10, h16, h18, h4, h6, h9, hc34, hc46, hlam, hphi]
                  · rcases m.htr 2 3 6 (by decide) (by decide) with h21 | h21
                    · linarith only [h21, h4, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h23 | h23
                      · linarith only [h23, h8, h9, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h25 | h25
                        · linarith only [h23, h25, h8, h9, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                        · rcases m.htr 3 4 6 (by decide) (by decide) with h27 | h27
                          · linarith only [h0, h1, h2, h27, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                          · linarith only [h21, h27, h4, h6, h8, hc34, hc46, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h30 | h30
                  · rcases m.htr 2 3 6 (by decide) (by decide) with h31 | h31
                    · linarith only [h31, h5, h8, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h33 | h33
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h34 | h34
                        · rcases m.htr 3 4 6 (by decide) (by decide) with h35 | h35
                          · linarith only [h0, h1, h2, h35, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                          · rcases m.htr 3 5 6 (by decide) (by decide) with h37 | h37
                            · linarith only [h30, h31, h35, h37, h5, h6, h8, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi5]
                            · linarith only [h30, h31, h37, h5, h6, h8, hc35, hc56, hlam, hphi]
                        · linarith only [h31, h33, h34, h5, h6, hc34, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                      · linarith only [h30, h33, h8, hlam]
                  · rcases m.htr 2 3 6 (by decide) (by decide) with h42 | h42
                    · linarith only [h42, h5, h8, hc12, hlam, hphi, ht01, ht0b, ht6b, u6ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h44 | h44
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h45 | h45
                        · rcases m.htr 3 4 6 (by decide) (by decide) with h46 | h46
                          · linarith only [h0, h1, h2, h46, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                          · rcases m.htr 3 5 6 (by decide) (by decide) with h48 | h48
                            · linarith only [h0, h1, h3, h48, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                            · linarith only [h42, h44, h48, h5, h6, hc45, hc56, hlam, hphi]
                        · linarith only [h44, h45, h5, h6, hc26, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h52 | h52
                        · rcases m.htr 3 4 6 (by decide) (by decide) with h53 | h53
                          · linarith only [h0, h1, h2, h53, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                          · linarith only [h44, h52, h53, hc24, hc46, hlam, hphi]
                        · rcases m.htr 3 4 6 (by decide) (by decide) with h56 | h56
                          · linarith only [h52, h56, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi4]
                          · rcases m.htr 3 5 6 (by decide) (by decide) with h58 | h58
                            · linarith only [h0, h1, h3, h58, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                            · rcases m.htr 4 5 6 (by decide) (by decide) with h60 | h60
                              · linarith only [h52, h58, h60, h8, hc23, hc45, hlam, hphi, ht34]
                              · linarith only [h52, h60, h8, hc23, hc56, hlam, hphi, ht34, ht45]
            · rcases m.htr 1 2 6 (by decide) (by decide) with h63 | h63
              · linarith only [h5, h63, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h65 | h65
                · linarith only [h4, h5, h65, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h67 | h67
                  · linarith only [h0, h1, h2, h4, h5, h65, h67, hc01, hc35, hlam, hphi, ht0b, ht56, ht6b]
                  · rcases m.htr 2 3 6 (by decide) (by decide) with h69 | h69
                    · linarith only [h0, h1, h2, h4, h5, h65, h69, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h71 | h71
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h72 | h72
                        · rcases m.htr 3 4 6 (by decide) (by decide) with h73 | h73
                          · linarith only [h0, h1, h2, h73, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                          · linarith only [h4, h5, h65, h73, hc23, hc46, hlam, hphi, ht34]
                        · linarith only [h4, h5, h65, h72, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h4, h5, h71, hc23, hc45, hlam, hphi, ht34]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h78 | h78
            · rcases m.htr 1 2 6 (by decide) (by decide) with h79 | h79
              · linarith only [h4, h79, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h81 | h81
                · rcases m.htr 2 3 5 (by decide) (by decide) with h82 | h82
                  · rcases m.htr 2 3 6 (by decide) (by decide) with h83 | h83
                    · linarith only [h0, h1, h83, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h85 | h85
                      · linarith only [h4, h78, h83, h85, hc36, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h87 | h87
                        · linarith only [h81, h85, h87, hlam]
                        · rcases m.htr 3 4 6 (by decide) (by decide) with h89 | h89
                          · linarith only [h4, h78, h81, h83, h89, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi4]
                          · linarith only [h4, h78, h81, h83, h89, hc34, hc46, hlam, hphi]
                  · linarith only [h0, h1, h3, h4, h78, h81, h82, hc01, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b]
                · linarith only [h0, h1, h2, h4, h78, h81, hc01, hc24, hlam, hphi, ht0b, ht45, ht56, ht6b]
            · rcases m.htr 1 2 6 (by decide) (by decide) with h94 | h94
              · linarith only [h4, h94, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h96 | h96
                · rcases m.htr 2 3 5 (by decide) (by decide) with h97 | h97
                  · rcases m.htr 2 3 6 (by decide) (by decide) with h98 | h98
                    · linarith only [h0, h1, h98, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h100 | h100
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h101 | h101
                        · rcases m.htr 3 4 6 (by decide) (by decide) with h102 | h102
                          · linarith only [h102, h96, h98, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi4]
                          · rcases m.htr 3 5 6 (by decide) (by decide) with h104 | h104
                            · linarith only [h101, h102, h104, h96, h98, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi5]
                            · linarith only [h101, h104, h96, h98, hc45, hc56, hlam, hphi]
                        · rcases m.htr 3 4 6 (by decide) (by decide) with h107 | h107
                          · linarith only [h100, h101, h107, h96, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi4]
                          · linarith only [h100, h101, h107, h96, h98, hc34, hc46, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h110 | h110
                        · linarith only [h100, h110, h78, hc12, hc34, hlam, hphi, ht23]
                        · rcases m.htr 3 4 6 (by decide) (by decide) with h112 | h112
                          · linarith only [h0, h1, h112, h2, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                          · rcases m.htr 3 5 6 (by decide) (by decide) with h114 | h114
                            · linarith only [h112, h114, h97, h98, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi5]
                            · rcases m.htr 4 5 6 (by decide) (by decide) with h116 | h116
                              · linarith only [h110, h114, h116, h97, h98, hc34, hc45, hlam, hphi]
                              · linarith only [h100, h116, h78, hc12, hc56, hlam, hphi, ht23, ht34, ht45]
                  · rcases m.htr 2 3 6 (by decide) (by decide) with h119 | h119
                    · linarith only [h119, h97, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h121 | h121
                      · linarith only [h121, h96, h97, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h123 | h123
                        · linarith only [h121, h123, h78, hc12, hc34, hlam, hphi, ht23]
                        · rcases m.htr 3 4 6 (by decide) (by decide) with h125 | h125
                          · linarith only [h0, h1, h125, h3, h96, h97, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                          · rcases m.htr 3 5 6 (by decide) (by decide) with h127 | h127
                            · linarith only [h0, h1, h127, h3, hc01, hlam, hphi, ht0b, ht6b, u6ehi5]
                            · linarith only [h127, h78, h96, h97, hc12, hc56, hlam, hphi, ht23, ht34, ht45]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h130 | h130
                  · rcases m.htr 2 3 6 (by decide) (by decide) with h131 | h131
                    · linarith only [h0, h1, h131, h2, h96, hc01, hlam, hphi, ht0b, ht6b, u6ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h133 | h133
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h134 | h134
                        · rcases m.htr 3 4 6 (by decide) (by decide) with h135 | h135
                          · linarith only [h0, h1, h135, h2, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                          · linarith only [h135, h4, h96, hc12, hc46, hlam, hphi, ht23, ht34]
                        · linarith only [h134, h4, h96, hc12, hc45, hlam, hphi, ht23, ht34]
                      · linarith only [h130, h133, h96, hlam]
                  · rcases m.htr 2 3 6 (by decide) (by decide) with h140 | h140
                    · linarith only [h140, h96, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h142 | h142
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h143 | h143
                        · rcases m.htr 3 4 6 (by decide) (by decide) with h144 | h144
                          · linarith only [h0, h1, h144, h2, hc01, hlam, hphi, ht0b, ht6b, u6ehi4]
                          · linarith only [h130, h143, h144, h4, hc12, hc46, hlam, hphi, ht23, ht34]
                        · linarith only [h142, h143, h96, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h148 | h148
                        · linarith only [h0, h1, h142, h148, h2, h78, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b]
                        · linarith only [h148, h4, h96, hc12, hc45, hlam, hphi, ht23, ht34]
        · linarith only [h3, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
      · linarith only [h2, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
    · linarith only [h1, hc23, hlam, hphi, ht01, ht12, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem n8l_sBT8_H_R_M_LI (m : N8Model)
    (hb0 : CMSig2_8_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_M_LI m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0ehi := hb0.1
  have h6elo := hb6.1
  have u0ehi5 := h0ehi (m.d 0 6) (by simp)
  have u6elo0 := h6elo (m.d 0 6) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi5, u6elo0]

theorem n8l_sBT8_H_R_M_LR (m : N8Model)
    (hb0 : CMSig2_8_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_M_LR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0ehi := hb0.1
  have h6elo := hb6.1
  have u0ehi5 := h0ehi (m.d 0 6) (by simp)
  have u6elo0 := h6elo (m.d 0 6) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi5, u6elo0]

theorem n8l_sBT8_M_IR_H_I (m : N8Model)
    (hb0 : CMSig2_8_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_H_I m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc06 := m.hcor 0 6 (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u0ehi5 := h0ehi (m.d 0 6) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n8l_sBT8_M_IR_H_L (m : N8Model)
    (hb0 : CMSig2_8_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_H_L m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h6elo := hb6.1
  have u0ehi5 := h0ehi (m.d 0 6) (by simp)
  have u6elo0 := h6elo (m.d 0 6) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi5, u6elo0]

theorem n8l_sBT8_M_IR_H_R (m : N8Model)
    (hb0 : CMSig2_8_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_H_R m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc06 := m.hcor 0 6 (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h6ehi := hb6.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u6ehi0 := h6ehi (m.d 0 6) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, ht0b, ht6b, p0_1, u6ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n8l_sBT8_M_IR_M_IR (m : N8Model)
    (hb0 : CMSig2_8_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_M_IR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc06 := m.hcor 0 6 (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u0ehi5 := h0ehi (m.d 0 6) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n8l_sBT8_M_IR_M_LI (m : N8Model)
    (hb0 : CMSig2_8_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_M_LI m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc06 := m.hcor 0 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h6elo := hb6.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u0ehi5 := h0ehi (m.d 0 6) (by simp)
  have u6elo0 := h6elo (m.d 0 6) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, p0_1, u0ehi1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, p0_1, u0ehi2, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, p0_1, u0ehi3, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, ht56, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n8l_sBT8_M_IR_M_LR (m : N8Model)
    (hb0 : CMSig2_8_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_M_LR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc06 := m.hcor 0 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h6elo := hb6.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u0ehi5 := h0ehi (m.d 0 6) (by simp)
  have u6elo0 := h6elo (m.d 0 6) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, p0_1, u0ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u0ehi0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, p0_1, u0ehi1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, p0_1, u0ehi2, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, p0_1, u0ehi3, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, ht56, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n8l_sBT8_M_LI_M_LI (m : N8Model)
    (hb0 : CMSig2_8_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_M_LI m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc06 := m.hcor 0 6 (by decide)
  have hc16 := m.hcor 1 6 (by decide)
  have hc26 := m.hcor 2 6 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have h6elo := hb6.1
  have h6bigk := hb6.2.2.2
  have u6elo0 := h6elo (m.d 0 6) (by simp)
  have u6elo1 := h6elo (m.d 1 6) (by simp)
  have u6elo2 := h6elo (m.d 2 6) (by simp)
  have u6elo3 := h6elo (m.d 3 6) (by simp)
  have u6elo4 := h6elo (m.d 4 6) (by simp)
  have u6elo5 := h6elo (m.d 5 6) (by simp)
  rcases h6bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc26, hlam, hphi, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc36, hlam, hphi, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc46, hlam, hphi, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u6elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc26, hlam, hphi, p0_1, u6elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc36, hlam, hphi, p0_1, u6elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc46, hlam, hphi, p0_1, u6elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, p0_1, u6elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u6elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u6elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc36, hlam, hphi, p0_1, u6elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc46, hlam, hphi, p0_1, u6elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, p0_1, u6elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u6elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u6elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc26, hlam, hphi, p0_1, u6elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc46, hlam, hphi, p0_1, u6elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, p0_1, u6elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u6elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u6elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc26, hlam, hphi, p0_1, u6elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc36, hlam, hphi, p0_1, u6elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, p0_1, u6elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc06, hlam, hphi, p0_1, u6elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u6elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc26, hlam, hphi, p0_1, u6elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc36, hlam, hphi, p0_1, u6elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc46, hlam, hphi, p0_1, u6elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n8l_sBT8_M_LI_M_LR (m : N8Model)
    (hb0 : CMSig2_8_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_M_LR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h6elo := hb6.1
  have h6ehi := hb6.2.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u6elo0 := h6elo (m.d 0 6) (by simp)
  have u6ehi6 := h6ehi (m.d 0 6) (by simp)
  rcases h0bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h2 | h2
    · rcases p0_3 (m.d 0 2) (by simp) with h3 | h3
      · linarith only [h3, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h5 | h5
        · rcases p0_3 (m.d 0 4) (by simp) with h6 | h6
          · rcases p0_3 (m.d 0 5) (by simp) with h7 | h7
            · rcases p0_3 (m.d 0 6) (by simp) with h8 | h8
              · linarith only [h8, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h8, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h11 | h11
              · linarith only [h11, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h11, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h14 | h14
            · rcases p0_3 (m.d 0 6) (by simp) with h15 | h15
              · linarith only [h15, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h15, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h18 | h18
              · linarith only [h18, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h18, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
        · rcases p0_3 (m.d 0 4) (by simp) with h21 | h21
          · rcases p0_3 (m.d 0 5) (by simp) with h22 | h22
            · rcases p0_3 (m.d 0 6) (by simp) with h23 | h23
              · linarith only [h23, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h23, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h26 | h26
              · linarith only [h26, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h26, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h29 | h29
            · rcases p0_3 (m.d 0 6) (by simp) with h30 | h30
              · linarith only [h30, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h30, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h33 | h33
              · linarith only [h33, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h33, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
    · linarith only [h2, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h37 | h37
    · rcases p0_3 (m.d 0 2) (by simp) with h38 | h38
      · rcases p0_3 (m.d 0 3) (by simp) with h39 | h39
        · linarith only [h39, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h41 | h41
          · rcases p0_3 (m.d 0 5) (by simp) with h42 | h42
            · rcases p0_3 (m.d 0 6) (by simp) with h43 | h43
              · linarith only [h43, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h43, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h46 | h46
              · linarith only [h46, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h46, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h49 | h49
            · rcases p0_3 (m.d 0 6) (by simp) with h50 | h50
              · linarith only [h50, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h50, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h53 | h53
              · linarith only [h53, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h53, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
      · rcases p0_3 (m.d 0 3) (by simp) with h56 | h56
        · linarith only [h56, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h58 | h58
          · rcases p0_3 (m.d 0 5) (by simp) with h59 | h59
            · rcases p0_3 (m.d 0 6) (by simp) with h60 | h60
              · linarith only [h38, h60, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h60, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h63 | h63
              · linarith only [h63, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h63, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h66 | h66
            · rcases p0_3 (m.d 0 6) (by simp) with h67 | h67
              · linarith only [h67, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h67, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h70 | h70
              · linarith only [h70, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h70, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
    · linarith only [h37, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h74 | h74
    · rcases p0_3 (m.d 0 2) (by simp) with h75 | h75
      · rcases p0_3 (m.d 0 3) (by simp) with h76 | h76
        · rcases p0_3 (m.d 0 4) (by simp) with h77 | h77
          · linarith only [h77, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h79 | h79
            · rcases p0_3 (m.d 0 6) (by simp) with h80 | h80
              · linarith only [h80, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h80, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h83 | h83
              · linarith only [h83, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h83, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
        · rcases p0_3 (m.d 0 4) (by simp) with h86 | h86
          · linarith only [h86, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h88 | h88
            · rcases p0_3 (m.d 0 6) (by simp) with h89 | h89
              · linarith only [h76, h89, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h89, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h92 | h92
              · linarith only [h76, h92, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h92, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
      · rcases p0_3 (m.d 0 3) (by simp) with h95 | h95
        · rcases p0_3 (m.d 0 4) (by simp) with h96 | h96
          · linarith only [h96, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h98 | h98
            · rcases p0_3 (m.d 0 6) (by simp) with h99 | h99
              · linarith only [h75, h99, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h99, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h102 | h102
              · linarith only [h102, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h102, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
        · rcases p0_3 (m.d 0 4) (by simp) with h105 | h105
          · linarith only [h105, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h107 | h107
            · rcases p0_3 (m.d 0 6) (by simp) with h108 | h108
              · linarith only [h108, h95, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h108, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h111 | h111
              · linarith only [h111, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h111, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
    · linarith only [h74, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h115 | h115
    · rcases p0_3 (m.d 0 2) (by simp) with h116 | h116
      · rcases p0_3 (m.d 0 3) (by simp) with h117 | h117
        · rcases p0_3 (m.d 0 4) (by simp) with h118 | h118
          · rcases p0_3 (m.d 0 5) (by simp) with h119 | h119
            · linarith only [h119, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h121 | h121
              · linarith only [h121, hc05, hlam, hphi, ht56, p0_1, u6elo0]
              · linarith only [h121, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h124 | h124
            · linarith only [h124, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h126 | h126
              · linarith only [h118, h126, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h126, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
        · rcases p0_3 (m.d 0 4) (by simp) with h129 | h129
          · rcases p0_3 (m.d 0 5) (by simp) with h130 | h130
            · linarith only [h130, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h132 | h132
              · linarith only [h117, h132, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h132, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h135 | h135
            · linarith only [h135, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h137 | h137
              · linarith only [h129, h137, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h137, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
      · rcases p0_3 (m.d 0 3) (by simp) with h140 | h140
        · rcases p0_3 (m.d 0 4) (by simp) with h141 | h141
          · rcases p0_3 (m.d 0 5) (by simp) with h142 | h142
            · linarith only [h142, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h144 | h144
              · linarith only [h116, h144, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h144, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h147 | h147
            · linarith only [h147, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h149 | h149
              · linarith only [h141, h149, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h149, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
        · rcases p0_3 (m.d 0 4) (by simp) with h152 | h152
          · rcases p0_3 (m.d 0 5) (by simp) with h153 | h153
            · linarith only [h153, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h155 | h155
              · linarith only [h140, h155, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h155, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h158 | h158
            · linarith only [h158, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h160 | h160
              · linarith only [h140, h160, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h160, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
    · linarith only [h115, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h165 | h165
    · linarith only [h165, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h167 | h167
      · rcases p0_3 (m.d 0 3) (by simp) with h168 | h168
        · rcases p0_3 (m.d 0 4) (by simp) with h169 | h169
          · rcases p0_3 (m.d 0 5) (by simp) with h170 | h170
            · rcases p0_3 (m.d 0 6) (by simp) with h171 | h171
              · linarith only [h171, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h171, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h174 | h174
              · linarith only [h174, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h174, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h177 | h177
            · rcases p0_3 (m.d 0 6) (by simp) with h178 | h178
              · linarith only [h178, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h178, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h181 | h181
              · linarith only [h181, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h181, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
        · rcases p0_3 (m.d 0 4) (by simp) with h184 | h184
          · rcases p0_3 (m.d 0 5) (by simp) with h185 | h185
            · rcases p0_3 (m.d 0 6) (by simp) with h186 | h186
              · linarith only [h186, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h186, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h189 | h189
              · linarith only [h189, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h189, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h192 | h192
            · rcases p0_3 (m.d 0 6) (by simp) with h193 | h193
              · linarith only [h193, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h193, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h196 | h196
              · linarith only [h196, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h196, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
      · linarith only [h167, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h201 | h201
    · rcases p0_3 (m.d 0 2) (by simp) with h202 | h202
      · rcases p0_3 (m.d 0 3) (by simp) with h203 | h203
        · linarith only [h203, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h205 | h205
          · rcases p0_3 (m.d 0 5) (by simp) with h206 | h206
            · rcases p0_3 (m.d 0 6) (by simp) with h207 | h207
              · linarith only [h207, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h201, h207, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h210 | h210
              · linarith only [h210, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h210, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h213 | h213
            · rcases p0_3 (m.d 0 6) (by simp) with h214 | h214
              · linarith only [h214, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h214, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h217 | h217
              · linarith only [h217, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h217, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
      · linarith only [h202, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h221 | h221
      · rcases p0_3 (m.d 0 3) (by simp) with h222 | h222
        · linarith only [h222, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h224 | h224
          · rcases p0_3 (m.d 0 5) (by simp) with h225 | h225
            · rcases p0_3 (m.d 0 6) (by simp) with h226 | h226
              · linarith only [h201, h226, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h226, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h229 | h229
              · linarith only [h201, h229, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h229, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h232 | h232
            · rcases p0_3 (m.d 0 6) (by simp) with h233 | h233
              · linarith only [h233, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h233, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h236 | h236
              · linarith only [h201, h236, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h236, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
      · linarith only [h221, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h240 | h240
    · rcases p0_3 (m.d 0 2) (by simp) with h241 | h241
      · rcases p0_3 (m.d 0 3) (by simp) with h242 | h242
        · rcases p0_3 (m.d 0 4) (by simp) with h243 | h243
          · linarith only [h243, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h245 | h245
            · rcases p0_3 (m.d 0 6) (by simp) with h246 | h246
              · linarith only [h246, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h240, h246, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h249 | h249
              · linarith only [h249, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h249, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
        · rcases p0_3 (m.d 0 4) (by simp) with h252 | h252
          · linarith only [h252, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h254 | h254
            · rcases p0_3 (m.d 0 6) (by simp) with h255 | h255
              · linarith only [h242, h255, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h255, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h258 | h258
              · linarith only [h242, h258, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h258, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
      · linarith only [h241, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h262 | h262
      · rcases p0_3 (m.d 0 3) (by simp) with h263 | h263
        · rcases p0_3 (m.d 0 4) (by simp) with h264 | h264
          · linarith only [h264, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h266 | h266
            · rcases p0_3 (m.d 0 6) (by simp) with h267 | h267
              · linarith only [h240, h267, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h267, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h270 | h270
              · linarith only [h240, h270, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h270, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
        · rcases p0_3 (m.d 0 4) (by simp) with h273 | h273
          · linarith only [h273, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h275 | h275
            · rcases p0_3 (m.d 0 6) (by simp) with h276 | h276
              · linarith only [h240, h276, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h276, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h279 | h279
              · linarith only [h240, h279, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h279, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
      · linarith only [h262, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h283 | h283
    · rcases p0_3 (m.d 0 2) (by simp) with h284 | h284
      · rcases p0_3 (m.d 0 3) (by simp) with h285 | h285
        · rcases p0_3 (m.d 0 4) (by simp) with h286 | h286
          · rcases p0_3 (m.d 0 5) (by simp) with h287 | h287
            · linarith only [h287, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h289 | h289
              · linarith only [h289, hc05, hlam, hphi, ht56, p0_1, u6elo0]
              · linarith only [h283, h289, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h292 | h292
            · linarith only [h292, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h294 | h294
              · linarith only [h286, h294, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h294, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
        · rcases p0_3 (m.d 0 4) (by simp) with h297 | h297
          · rcases p0_3 (m.d 0 5) (by simp) with h298 | h298
            · linarith only [h298, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h300 | h300
              · linarith only [h285, h300, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h300, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h303 | h303
            · linarith only [h303, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h305 | h305
              · linarith only [h297, h305, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h305, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
      · linarith only [h284, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h309 | h309
      · rcases p0_3 (m.d 0 3) (by simp) with h310 | h310
        · rcases p0_3 (m.d 0 4) (by simp) with h311 | h311
          · rcases p0_3 (m.d 0 5) (by simp) with h312 | h312
            · linarith only [h312, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h314 | h314
              · linarith only [h283, h314, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h314, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h317 | h317
            · linarith only [h317, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h319 | h319
              · linarith only [h311, h319, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h319, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
        · rcases p0_3 (m.d 0 4) (by simp) with h322 | h322
          · rcases p0_3 (m.d 0 5) (by simp) with h323 | h323
            · linarith only [h323, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h325 | h325
              · linarith only [h310, h325, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h325, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h328 | h328
            · linarith only [h328, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h330 | h330
              · linarith only [h310, h330, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h330, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
      · linarith only [h309, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h335 | h335
    · linarith only [h335, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h337 | h337
      · rcases p0_3 (m.d 0 3) (by simp) with h338 | h338
        · rcases p0_3 (m.d 0 4) (by simp) with h339 | h339
          · rcases p0_3 (m.d 0 5) (by simp) with h340 | h340
            · rcases p0_3 (m.d 0 6) (by simp) with h341 | h341
              · linarith only [h341, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h341, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h344 | h344
              · linarith only [h344, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h344, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h347 | h347
            · rcases p0_3 (m.d 0 6) (by simp) with h348 | h348
              · linarith only [h348, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h348, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h351 | h351
              · linarith only [h351, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h351, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
        · linarith only [h338, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h355 | h355
        · rcases p0_3 (m.d 0 4) (by simp) with h356 | h356
          · rcases p0_3 (m.d 0 5) (by simp) with h357 | h357
            · rcases p0_3 (m.d 0 6) (by simp) with h358 | h358
              · linarith only [h358, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h358, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h361 | h361
              · linarith only [h361, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h361, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h364 | h364
            · rcases p0_3 (m.d 0 6) (by simp) with h365 | h365
              · linarith only [h365, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h365, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h368 | h368
              · linarith only [h368, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h368, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
        · linarith only [h355, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h372 | h372
    · rcases p0_3 (m.d 0 2) (by simp) with h373 | h373
      · linarith only [h373, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h375 | h375
        · rcases p0_3 (m.d 0 4) (by simp) with h376 | h376
          · rcases p0_3 (m.d 0 5) (by simp) with h377 | h377
            · rcases p0_3 (m.d 0 6) (by simp) with h378 | h378
              · linarith only [h378, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h372, h378, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h381 | h381
              · linarith only [h381, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h381, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h384 | h384
            · rcases p0_3 (m.d 0 6) (by simp) with h385 | h385
              · linarith only [h385, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h385, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h388 | h388
              · linarith only [h388, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h388, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
        · linarith only [h375, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h392 | h392
      · linarith only [h392, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h394 | h394
        · rcases p0_3 (m.d 0 4) (by simp) with h395 | h395
          · rcases p0_3 (m.d 0 5) (by simp) with h396 | h396
            · rcases p0_3 (m.d 0 6) (by simp) with h397 | h397
              · linarith only [h372, h397, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h397, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h400 | h400
              · linarith only [h372, h400, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h400, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h403 | h403
            · rcases p0_3 (m.d 0 6) (by simp) with h404 | h404
              · linarith only [h372, h404, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h404, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h407 | h407
              · linarith only [h372, h407, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h407, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
        · linarith only [h394, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h412 | h412
    · rcases p0_3 (m.d 0 2) (by simp) with h413 | h413
      · rcases p0_3 (m.d 0 3) (by simp) with h414 | h414
        · rcases p0_3 (m.d 0 4) (by simp) with h415 | h415
          · linarith only [h415, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h417 | h417
            · rcases p0_3 (m.d 0 6) (by simp) with h418 | h418
              · linarith only [h418, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h412, h418, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h421 | h421
              · linarith only [h421, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h421, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
        · linarith only [h414, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h425 | h425
        · rcases p0_3 (m.d 0 4) (by simp) with h426 | h426
          · linarith only [h426, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h428 | h428
            · rcases p0_3 (m.d 0 6) (by simp) with h429 | h429
              · linarith only [h413, h429, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h429, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h432 | h432
              · linarith only [h413, h432, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h432, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
        · linarith only [h425, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h436 | h436
      · rcases p0_3 (m.d 0 3) (by simp) with h437 | h437
        · rcases p0_3 (m.d 0 4) (by simp) with h438 | h438
          · linarith only [h438, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h440 | h440
            · rcases p0_3 (m.d 0 6) (by simp) with h441 | h441
              · linarith only [h412, h441, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h436, h441, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h444 | h444
              · linarith only [h412, h444, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h436, h444, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
        · linarith only [h437, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h448 | h448
        · rcases p0_3 (m.d 0 4) (by simp) with h449 | h449
          · linarith only [h449, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h451 | h451
            · rcases p0_3 (m.d 0 6) (by simp) with h452 | h452
              · linarith only [h412, h452, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h452, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h455 | h455
              · linarith only [h412, h455, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h455, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
        · linarith only [h448, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h459 | h459
    · rcases p0_3 (m.d 0 2) (by simp) with h460 | h460
      · rcases p0_3 (m.d 0 3) (by simp) with h461 | h461
        · rcases p0_3 (m.d 0 4) (by simp) with h462 | h462
          · rcases p0_3 (m.d 0 5) (by simp) with h463 | h463
            · linarith only [h463, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h465 | h465
              · linarith only [h465, hc05, hlam, hphi, ht56, p0_1, u6elo0]
              · linarith only [h459, h465, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h468 | h468
            · linarith only [h468, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h470 | h470
              · linarith only [h462, h470, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h460, h470, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
        · linarith only [h461, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h474 | h474
        · rcases p0_3 (m.d 0 4) (by simp) with h475 | h475
          · rcases p0_3 (m.d 0 5) (by simp) with h476 | h476
            · linarith only [h476, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h478 | h478
              · linarith only [h460, h478, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h478, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h481 | h481
            · linarith only [h481, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h483 | h483
              · linarith only [h475, h483, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h483, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
        · linarith only [h474, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h487 | h487
      · rcases p0_3 (m.d 0 3) (by simp) with h488 | h488
        · rcases p0_3 (m.d 0 4) (by simp) with h489 | h489
          · rcases p0_3 (m.d 0 5) (by simp) with h490 | h490
            · linarith only [h490, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h492 | h492
              · linarith only [h459, h492, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h487, h492, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h495 | h495
            · linarith only [h495, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h497 | h497
              · linarith only [h489, h497, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h497, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
        · linarith only [h488, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h501 | h501
        · rcases p0_3 (m.d 0 4) (by simp) with h502 | h502
          · rcases p0_3 (m.d 0 5) (by simp) with h503 | h503
            · linarith only [h503, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h505 | h505
              · linarith only [h487, h505, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h505, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
          · rcases p0_3 (m.d 0 5) (by simp) with h508 | h508
            · linarith only [h508, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h510 | h510
              · linarith only [h487, h510, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h510, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
        · linarith only [h501, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h515 | h515
    · linarith only [h515, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h517 | h517
      · rcases p0_3 (m.d 0 3) (by simp) with h518 | h518
        · rcases p0_3 (m.d 0 4) (by simp) with h519 | h519
          · rcases p0_3 (m.d 0 5) (by simp) with h520 | h520
            · rcases p0_3 (m.d 0 6) (by simp) with h521 | h521
              · linarith only [h521, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h517, h521, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h524 | h524
              · linarith only [h524, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h524, hlam, hphi, ht0b, ht6b, p0_1, u0elo3, u6ehi6]
          · linarith only [h519, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h528 | h528
          · rcases p0_3 (m.d 0 5) (by simp) with h529 | h529
            · rcases p0_3 (m.d 0 6) (by simp) with h530 | h530
              · linarith only [h530, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h530, hlam, hphi, ht0b, ht6b, p0_1, u0elo3, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h533 | h533
              · linarith only [h533, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h533, hlam, hphi, ht0b, ht6b, p0_1, u0elo3, u6ehi6]
          · linarith only [h528, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h537 | h537
        · rcases p0_3 (m.d 0 4) (by simp) with h538 | h538
          · rcases p0_3 (m.d 0 5) (by simp) with h539 | h539
            · rcases p0_3 (m.d 0 6) (by simp) with h540 | h540
              · linarith only [h540, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h537, h540, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h543 | h543
              · linarith only [h543, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h543, hlam, hphi, ht0b, ht6b, p0_1, u0elo3, u6ehi6]
          · linarith only [h538, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h547 | h547
          · rcases p0_3 (m.d 0 5) (by simp) with h548 | h548
            · rcases p0_3 (m.d 0 6) (by simp) with h549 | h549
              · linarith only [h549, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h549, hlam, hphi, ht0b, ht6b, p0_1, u0elo3, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h552 | h552
              · linarith only [h552, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h552, hlam, hphi, ht0b, ht6b, p0_1, u0elo3, u6ehi6]
          · linarith only [h547, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h556 | h556
    · rcases p0_3 (m.d 0 2) (by simp) with h557 | h557
      · linarith only [h557, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h559 | h559
        · rcases p0_3 (m.d 0 4) (by simp) with h560 | h560
          · rcases p0_3 (m.d 0 5) (by simp) with h561 | h561
            · rcases p0_3 (m.d 0 6) (by simp) with h562 | h562
              · linarith only [h562, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h556, h562, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h565 | h565
              · linarith only [h565, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h556, h565, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
          · linarith only [h560, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h569 | h569
          · rcases p0_3 (m.d 0 5) (by simp) with h570 | h570
            · rcases p0_3 (m.d 0 6) (by simp) with h571 | h571
              · linarith only [h571, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h556, h571, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h574 | h574
              · linarith only [h574, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h556, h574, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
          · linarith only [h569, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h578 | h578
      · linarith only [h578, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h580 | h580
        · rcases p0_3 (m.d 0 4) (by simp) with h581 | h581
          · rcases p0_3 (m.d 0 5) (by simp) with h582 | h582
            · rcases p0_3 (m.d 0 6) (by simp) with h583 | h583
              · linarith only [h556, h583, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h580, h583, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h586 | h586
              · linarith only [h556, h586, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h580, h586, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
          · linarith only [h581, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h590 | h590
          · rcases p0_3 (m.d 0 5) (by simp) with h591 | h591
            · rcases p0_3 (m.d 0 6) (by simp) with h592 | h592
              · linarith only [h556, h592, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h592, hlam, hphi, ht0b, ht6b, p0_1, u0elo3, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h595 | h595
              · linarith only [h595, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h595, hlam, hphi, ht0b, ht6b, p0_1, u0elo3, u6ehi6]
          · linarith only [h590, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h599 | h599
    · rcases p0_3 (m.d 0 2) (by simp) with h600 | h600
      · rcases p0_3 (m.d 0 3) (by simp) with h601 | h601
        · linarith only [h601, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h603 | h603
          · rcases p0_3 (m.d 0 5) (by simp) with h604 | h604
            · rcases p0_3 (m.d 0 6) (by simp) with h605 | h605
              · linarith only [h605, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h599, h605, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h608 | h608
              · linarith only [h608, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h600, h608, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
          · linarith only [h603, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h612 | h612
        · linarith only [h612, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h614 | h614
          · rcases p0_3 (m.d 0 5) (by simp) with h615 | h615
            · rcases p0_3 (m.d 0 6) (by simp) with h616 | h616
              · linarith only [h600, h616, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h616, hlam, hphi, ht0b, ht6b, p0_1, u0elo3, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h619 | h619
              · linarith only [h600, h619, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h619, hlam, hphi, ht0b, ht6b, p0_1, u0elo3, u6ehi6]
          · linarith only [h614, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h623 | h623
      · rcases p0_3 (m.d 0 3) (by simp) with h624 | h624
        · linarith only [h624, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h626 | h626
          · rcases p0_3 (m.d 0 5) (by simp) with h627 | h627
            · rcases p0_3 (m.d 0 6) (by simp) with h628 | h628
              · linarith only [h599, h628, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h623, h628, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h631 | h631
              · linarith only [h599, h631, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h623, h631, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
          · linarith only [h626, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h635 | h635
        · linarith only [h635, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h637 | h637
          · rcases p0_3 (m.d 0 5) (by simp) with h638 | h638
            · rcases p0_3 (m.d 0 6) (by simp) with h639 | h639
              · linarith only [h599, h639, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h639, hlam, hphi, ht0b, ht6b, p0_1, u0elo3, u6ehi6]
            · rcases p0_3 (m.d 0 6) (by simp) with h642 | h642
              · linarith only [h599, h642, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h642, hlam, hphi, ht0b, ht6b, p0_1, u0elo3, u6ehi6]
          · linarith only [h637, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h647 | h647
    · rcases p0_3 (m.d 0 2) (by simp) with h648 | h648
      · rcases p0_3 (m.d 0 3) (by simp) with h649 | h649
        · rcases p0_3 (m.d 0 4) (by simp) with h650 | h650
          · rcases p0_3 (m.d 0 5) (by simp) with h651 | h651
            · linarith only [h651, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h653 | h653
              · linarith only [h653, hc05, hlam, hphi, ht56, p0_1, u6elo0]
              · linarith only [h647, h653, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
          · linarith only [h650, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h657 | h657
          · rcases p0_3 (m.d 0 5) (by simp) with h658 | h658
            · linarith only [h658, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h660 | h660
              · linarith only [h649, h660, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h648, h660, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
          · linarith only [h657, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h664 | h664
        · rcases p0_3 (m.d 0 4) (by simp) with h665 | h665
          · rcases p0_3 (m.d 0 5) (by simp) with h666 | h666
            · linarith only [h666, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h668 | h668
              · linarith only [h648, h668, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h664, h668, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
          · linarith only [h665, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h672 | h672
          · rcases p0_3 (m.d 0 5) (by simp) with h673 | h673
            · linarith only [h673, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h675 | h675
              · linarith only [h648, h675, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h675, hlam, hphi, ht0b, ht6b, p0_1, u0elo3, u6ehi6]
          · linarith only [h672, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h679 | h679
      · rcases p0_3 (m.d 0 3) (by simp) with h680 | h680
        · rcases p0_3 (m.d 0 4) (by simp) with h681 | h681
          · rcases p0_3 (m.d 0 5) (by simp) with h682 | h682
            · linarith only [h682, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h684 | h684
              · linarith only [h647, h684, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h679, h684, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
          · linarith only [h681, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h688 | h688
          · rcases p0_3 (m.d 0 5) (by simp) with h689 | h689
            · linarith only [h689, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h691 | h691
              · linarith only [h647, h691, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h679, h691, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
          · linarith only [h688, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h695 | h695
        · rcases p0_3 (m.d 0 4) (by simp) with h696 | h696
          · rcases p0_3 (m.d 0 5) (by simp) with h697 | h697
            · linarith only [h697, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h699 | h699
              · linarith only [h647, h699, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h695, h699, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
          · linarith only [h696, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h703 | h703
          · rcases p0_3 (m.d 0 5) (by simp) with h704 | h704
            · linarith only [h704, hlam, p0_0]
            · rcases p0_3 (m.d 0 6) (by simp) with h706 | h706
              · linarith only [h647, h706, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h706, hlam, hphi, ht0b, ht6b, p0_1, u0elo3, u6ehi6]
          · linarith only [h703, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht6b, p0_1, u0elo3, u6ehi6]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h711 | h711
    · linarith only [h711, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h713 | h713
      · rcases p0_3 (m.d 0 3) (by simp) with h714 | h714
        · rcases p0_3 (m.d 0 4) (by simp) with h715 | h715
          · rcases p0_3 (m.d 0 5) (by simp) with h716 | h716
            · rcases p0_3 (m.d 0 6) (by simp) with h717 | h717
              · linarith only [h717, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h713, h717, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
            · linarith only [h716, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h721 | h721
            · rcases p0_3 (m.d 0 6) (by simp) with h722 | h722
              · linarith only [h722, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h713, h722, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
            · linarith only [h721, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h726 | h726
          · rcases p0_3 (m.d 0 5) (by simp) with h727 | h727
            · rcases p0_3 (m.d 0 6) (by simp) with h728 | h728
              · linarith only [h728, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h726, h728, hlam, hphi, ht0b, ht6b, p0_1, u0elo3, u6ehi6]
            · linarith only [h727, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h732 | h732
            · rcases p0_3 (m.d 0 6) (by simp) with h733 | h733
              · linarith only [h733, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h733, hlam, hphi, ht0b, ht6b, p0_1, u0elo4, u6ehi6]
            · linarith only [h732, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h737 | h737
        · rcases p0_3 (m.d 0 4) (by simp) with h738 | h738
          · rcases p0_3 (m.d 0 5) (by simp) with h739 | h739
            · rcases p0_3 (m.d 0 6) (by simp) with h740 | h740
              · linarith only [h740, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h737, h740, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
            · linarith only [h739, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h744 | h744
            · rcases p0_3 (m.d 0 6) (by simp) with h745 | h745
              · linarith only [h745, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h737, h745, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
            · linarith only [h744, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h749 | h749
          · rcases p0_3 (m.d 0 5) (by simp) with h750 | h750
            · rcases p0_3 (m.d 0 6) (by simp) with h751 | h751
              · linarith only [h751, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h749, h751, hlam, hphi, ht0b, ht6b, p0_1, u0elo3, u6ehi6]
            · linarith only [h750, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h755 | h755
            · rcases p0_3 (m.d 0 6) (by simp) with h756 | h756
              · linarith only [h756, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h756, hlam, hphi, ht0b, ht6b, p0_1, u0elo4, u6ehi6]
            · linarith only [h755, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h760 | h760
    · rcases p0_3 (m.d 0 2) (by simp) with h761 | h761
      · linarith only [h761, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h763 | h763
        · rcases p0_3 (m.d 0 4) (by simp) with h764 | h764
          · rcases p0_3 (m.d 0 5) (by simp) with h765 | h765
            · rcases p0_3 (m.d 0 6) (by simp) with h766 | h766
              · linarith only [h766, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h760, h766, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
            · linarith only [h765, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h770 | h770
            · rcases p0_3 (m.d 0 6) (by simp) with h771 | h771
              · linarith only [h771, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h763, h771, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
            · linarith only [h770, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h775 | h775
          · rcases p0_3 (m.d 0 5) (by simp) with h776 | h776
            · rcases p0_3 (m.d 0 6) (by simp) with h777 | h777
              · linarith only [h777, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h775, h777, hlam, hphi, ht0b, ht6b, p0_1, u0elo3, u6ehi6]
            · linarith only [h776, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h781 | h781
            · rcases p0_3 (m.d 0 6) (by simp) with h782 | h782
              · linarith only [h782, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h782, hlam, hphi, ht0b, ht6b, p0_1, u0elo4, u6ehi6]
            · linarith only [h781, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h786 | h786
      · linarith only [h786, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h788 | h788
        · rcases p0_3 (m.d 0 4) (by simp) with h789 | h789
          · rcases p0_3 (m.d 0 5) (by simp) with h790 | h790
            · rcases p0_3 (m.d 0 6) (by simp) with h791 | h791
              · linarith only [h760, h791, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h788, h791, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
            · linarith only [h790, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h795 | h795
            · rcases p0_3 (m.d 0 6) (by simp) with h796 | h796
              · linarith only [h796, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h788, h796, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
            · linarith only [h795, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h800 | h800
          · rcases p0_3 (m.d 0 5) (by simp) with h801 | h801
            · rcases p0_3 (m.d 0 6) (by simp) with h802 | h802
              · linarith only [h802, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h800, h802, hlam, hphi, ht0b, ht6b, p0_1, u0elo3, u6ehi6]
            · linarith only [h801, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h806 | h806
            · rcases p0_3 (m.d 0 6) (by simp) with h807 | h807
              · linarith only [h807, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h807, hlam, hphi, ht0b, ht6b, p0_1, u0elo4, u6ehi6]
            · linarith only [h806, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h811 | h811
    · rcases p0_3 (m.d 0 2) (by simp) with h812 | h812
      · rcases p0_3 (m.d 0 3) (by simp) with h813 | h813
        · linarith only [h813, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h815 | h815
          · rcases p0_3 (m.d 0 5) (by simp) with h816 | h816
            · rcases p0_3 (m.d 0 6) (by simp) with h817 | h817
              · linarith only [h817, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h811, h817, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
            · linarith only [h816, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h821 | h821
            · rcases p0_3 (m.d 0 6) (by simp) with h822 | h822
              · linarith only [h822, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h822, hlam, hphi, ht0b, ht6b, p0_1, u0elo4, u6ehi6]
            · linarith only [h821, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h826 | h826
        · linarith only [h826, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h828 | h828
          · rcases p0_3 (m.d 0 5) (by simp) with h829 | h829
            · rcases p0_3 (m.d 0 6) (by simp) with h830 | h830
              · linarith only [h812, h830, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h828, h830, hlam, hphi, ht0b, ht6b, p0_1, u0elo3, u6ehi6]
            · linarith only [h829, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h834 | h834
            · rcases p0_3 (m.d 0 6) (by simp) with h835 | h835
              · linarith only [h835, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h835, hlam, hphi, ht0b, ht6b, p0_1, u0elo4, u6ehi6]
            · linarith only [h834, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h839 | h839
      · rcases p0_3 (m.d 0 3) (by simp) with h840 | h840
        · linarith only [h840, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h842 | h842
          · rcases p0_3 (m.d 0 5) (by simp) with h843 | h843
            · rcases p0_3 (m.d 0 6) (by simp) with h844 | h844
              · linarith only [h811, h844, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h839, h844, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
            · linarith only [h843, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h848 | h848
            · rcases p0_3 (m.d 0 6) (by simp) with h849 | h849
              · linarith only [h811, h849, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h849, hlam, hphi, ht0b, ht6b, p0_1, u0elo4, u6ehi6]
            · linarith only [h848, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h853 | h853
        · linarith only [h853, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h855 | h855
          · rcases p0_3 (m.d 0 5) (by simp) with h856 | h856
            · rcases p0_3 (m.d 0 6) (by simp) with h857 | h857
              · linarith only [h811, h857, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h855, h857, hlam, hphi, ht0b, ht6b, p0_1, u0elo3, u6ehi6]
            · linarith only [h856, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h861 | h861
            · rcases p0_3 (m.d 0 6) (by simp) with h862 | h862
              · linarith only [h811, h862, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h862, hlam, hphi, ht0b, ht6b, p0_1, u0elo4, u6ehi6]
            · linarith only [h861, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 1) (by simp) with h866 | h866
    · rcases p0_3 (m.d 0 2) (by simp) with h867 | h867
      · rcases p0_3 (m.d 0 3) (by simp) with h868 | h868
        · rcases p0_3 (m.d 0 4) (by simp) with h869 | h869
          · linarith only [h869, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h871 | h871
            · rcases p0_3 (m.d 0 6) (by simp) with h872 | h872
              · linarith only [h872, hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
              · linarith only [h866, h872, hlam, hphi, ht0b, ht6b, p0_1, u0elo0, u6ehi6]
            · linarith only [h871, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h876 | h876
          · linarith only [h876, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h878 | h878
            · rcases p0_3 (m.d 0 6) (by simp) with h879 | h879
              · linarith only [h868, h879, hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h879, hlam, hphi, ht0b, ht6b, p0_1, u0elo4, u6ehi6]
            · linarith only [h878, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h883 | h883
        · rcases p0_3 (m.d 0 4) (by simp) with h884 | h884
          · linarith only [h884, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h886 | h886
            · rcases p0_3 (m.d 0 6) (by simp) with h887 | h887
              · linarith only [h867, h887, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h883, h887, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
            · linarith only [h886, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h891 | h891
          · linarith only [h891, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h893 | h893
            · rcases p0_3 (m.d 0 6) (by simp) with h894 | h894
              · linarith only [h867, h894, hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h894, hlam, hphi, ht0b, ht6b, p0_1, u0elo4, u6ehi6]
            · linarith only [h893, hlam, p0_0]
    · rcases p0_3 (m.d 0 2) (by simp) with h898 | h898
      · rcases p0_3 (m.d 0 3) (by simp) with h899 | h899
        · rcases p0_3 (m.d 0 4) (by simp) with h900 | h900
          · linarith only [h900, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h902 | h902
            · rcases p0_3 (m.d 0 6) (by simp) with h903 | h903
              · linarith only [h866, h903, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h898, h903, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
            · linarith only [h902, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h907 | h907
          · linarith only [h907, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h909 | h909
            · rcases p0_3 (m.d 0 6) (by simp) with h910 | h910
              · linarith only [h866, h910, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h898, h910, hlam, hphi, ht0b, ht6b, p0_1, u0elo1, u6ehi6]
            · linarith only [h909, hlam, p0_0]
      · rcases p0_3 (m.d 0 3) (by simp) with h914 | h914
        · rcases p0_3 (m.d 0 4) (by simp) with h915 | h915
          · linarith only [h915, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h917 | h917
            · rcases p0_3 (m.d 0 6) (by simp) with h918 | h918
              · linarith only [h866, h918, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h914, h918, hlam, hphi, ht0b, ht6b, p0_1, u0elo2, u6ehi6]
            · linarith only [h917, hlam, p0_0]
        · rcases p0_3 (m.d 0 4) (by simp) with h922 | h922
          · linarith only [h922, hlam, p0_0]
          · rcases p0_3 (m.d 0 5) (by simp) with h924 | h924
            · rcases p0_3 (m.d 0 6) (by simp) with h925 | h925
              · linarith only [h866, h925, hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
              · linarith only [h925, hlam, hphi, ht0b, ht6b, p0_1, u0elo4, u6ehi6]
            · linarith only [h924, hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht6b, p0_1, u0elo4, u6ehi6]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, ht56, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc02, hlam, hphi, ht23, ht34, ht45, ht56, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc03, hlam, hphi, ht34, ht45, ht56, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc04, hlam, hphi, ht45, ht56, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc05, hlam, hphi, ht56, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n8l_sBT8_M_LR_H_I (m : N8Model)
    (hb0 : CMSig2_8_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_H_I m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc16 := m.hcor 1 6 (by decide)
  have hc26 := m.hcor 2 6 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h6bigk := hb6.1
  have u0elo5 := h0elo (m.d 0 6) (by simp)
  have u0ehi11 := h0ehi (m.d 0 6) (by simp)
  rcases h6bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc26, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc36, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc46, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, ht01, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h9 | h9
    · linarith only [h9, hc26, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · linarith only [h9, hc16, hlam, hphi, ht01, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h12 | h12
    · linarith only [h12, hc36, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · linarith only [h12, hc16, hlam, hphi, ht01, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h15 | h15
    · linarith only [h15, hc46, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · linarith only [h15, hc16, hlam, hphi, ht01, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h18 | h18
    · linarith only [h18, hc56, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · linarith only [h18, hc16, hlam, hphi, ht01, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc26, hlam, hphi, ht01, ht12, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h22 | h22
    · linarith only [h22, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · linarith only [h22, hc26, hlam, hphi, ht01, ht12, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h26 | h26
    · linarith only [h26, hc36, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · linarith only [h26, hc26, hlam, hphi, ht01, ht12, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h29 | h29
    · linarith only [h29, hc46, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · linarith only [h29, hc26, hlam, hphi, ht01, ht12, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h32 | h32
    · linarith only [h32, hc56, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · linarith only [h32, hc26, hlam, hphi, ht01, ht12, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc36, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h36 | h36
    · linarith only [h36, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · linarith only [h36, hc36, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h39 | h39
    · linarith only [h39, hc26, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · linarith only [h39, hc36, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h43 | h43
    · linarith only [h43, hc46, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · linarith only [h43, hc36, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h46 | h46
    · linarith only [h46, hc56, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · linarith only [h46, hc36, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc46, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h50 | h50
    · linarith only [h50, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · linarith only [h50, hc46, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h53 | h53
    · linarith only [h53, hc26, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · linarith only [h53, hc46, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h56 | h56
    · linarith only [h56, hc36, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · linarith only [h56, hc46, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h60 | h60
    · linarith only [h60, hc56, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · linarith only [h60, hc46, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h64 | h64
    · linarith only [h64, hc16, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · linarith only [h64, hc56, hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h67 | h67
    · linarith only [h67, hc26, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · linarith only [h67, hc56, hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h70 | h70
    · linarith only [h70, hc36, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · linarith only [h70, hc56, hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h73 | h73
    · linarith only [h73, hc46, hlam, hphi, ht0b, ht6b, p0_1, u0elo5]
    · linarith only [h73, hc56, hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n8l_sBT8_M_LR_H_L (m : N8Model)
    (hb0 : CMSig2_8_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_H_L m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h6elo := hb6.1
  have u0ehi11 := h0ehi (m.d 0 6) (by simp)
  have u6elo0 := h6elo (m.d 0 6) (by simp)
  linarith only [hlam, hphi, ht01, ht12, ht23, ht34, ht45, ht56, u0ehi11, u6elo0]

theorem n8l_sBT8_M_LR_H_R (m : N8Model)
    (hb0 : CMSig2_8_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_H_R m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc16 := m.hcor 1 6 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc26 := m.hcor 2 6 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have ht56 : m.t 5 < m.t 6 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h6ehi := hb6.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u0ehi6 := h0ehi (m.d 0 1) (by simp)
  have u0ehi7 := h0ehi (m.d 0 2) (by simp)
  have u0ehi8 := h0ehi (m.d 0 3) (by simp)
  have u0ehi9 := h0ehi (m.d 0 4) (by simp)
  have u0ehi10 := h0ehi (m.d 0 5) (by simp)
  have u6ehi1 := h6ehi (m.d 1 6) (by simp)
  have u6ehi2 := h6ehi (m.d 2 6) (by simp)
  have u6ehi3 := h6ehi (m.d 3 6) (by simp)
  have u6ehi4 := h6ehi (m.d 4 6) (by simp)
  have u6ehi5 := h6ehi (m.d 5 6) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 6 (by decide) (by decide) with h3 | h3
        · linarith only [h3, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 2 4 (by decide) (by decide) with h6 | h6
            · rcases m.htr 0 2 6 (by decide) (by decide) with h7 | h7
              · linarith only [h0, h3, h7, hc16, hlam, hphi, ht01, ht0b, ht6b, u6ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h9 | h9
                · rcases m.htr 0 3 5 (by decide) (by decide) with h10 | h10
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h11 | h11
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h12 | h12
                      · linarith only [h0, h12, h3, h5, h9, hc16, hlam, hphi, ht01, ht0b, ht6b, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h14 | h14
                        · linarith only [h0, h11, h14, h3, h5, h9, hc16, hlam, hphi, ht01, ht0b, ht6b, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h16 | h16
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h17 | h17
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h18 | h18
                              · linarith only [h0, h16, h18, h3, hc16, hlam, hphi, ht01, ht0b, ht6b, u6ehi3]
                              · linarith only [h0, h16, h18, h3, hc23, hc36, hlam, hphi]
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h21 | h21
                              · linarith only [h0, h17, h21, h5, h9, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi3]
                              · linarith only [h0, h17, h21, h3, h5, h9, hc13, hc36, hlam, hphi]
                          · linarith only [h16, h5, h7, hc12, hc26, hlam, hphi]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h25 | h25
                      · linarith only [h25, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h27 | h27
                        · linarith only [h10, h27, h5, h7, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h29 | h29
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h30 | h30
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h31 | h31
                              · linarith only [h1, h3, h31, hc16, hlam, hphi, ht01, ht0b, ht6b, u6ehi3]
                              · linarith only [h0, h29, h3, h31, hc23, hc36, hlam, hphi]
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h34 | h34
                              · linarith only [h30, h34, h5, h7, h9, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi3]
                              · linarith only [h0, h29, h3, h30, h34, h5, h9, hc23, hc36, hlam, hphi]
                          · linarith only [h29, h5, h7, hc12, hc26, hlam, hphi]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h38 | h38
                    · linarith only [h10, h38, h9, hlam]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h40 | h40
                      · linarith only [h38, h40, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h42 | h42
                        · linarith only [h42, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h44 | h44
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h45 | h45
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h46 | h46
                              · linarith only [h0, h3, h44, h46, hc16, hlam, hphi, ht01, ht0b, ht6b, u6ehi3]
                              · linarith only [h0, h3, h44, h46, hc23, hc36, hlam, hphi]
                            · linarith only [h10, h42, h45, h9, hc13, hc56, hlam, hphi, ht34, ht45]
                          · linarith only [h44, h5, h7, hc12, hc26, hlam, hphi]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h51 | h51
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h52 | h52
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h53 | h53
                      · linarith only [h53, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h55 | h55
                        · linarith only [h51, h55, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h57 | h57
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h58 | h58
                            · linarith only [h58, h9, hc13, hlam, hphi, ht01, u0ehi8]
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h60 | h60
                              · linarith only [h0, h57, h60, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi3]
                              · linarith only [h0, h3, h57, h60, hc23, hc36, hlam, hphi]
                          · linarith only [h5, h57, h7, hc12, hc26, hlam, hphi]
                    · linarith only [h51, h52, h9, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h65 | h65
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h66 | h66
                      · linarith only [h66, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h68 | h68
                        · linarith only [h68, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h70 | h70
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h71 | h71
                            · linarith only [h71, h9, hc13, hlam, hphi, ht01, u0ehi8]
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h73 | h73
                              · linarith only [h0, h70, h73, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi3]
                              · linarith only [h0, h3, h70, h73, hc23, hc36, hlam, hphi]
                          · linarith only [h5, h7, h70, hc12, hc26, hlam, hphi]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h77 | h77
                      · linarith only [h65, h77, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h79 | h79
                        · linarith only [h79, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h81 | h81
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h82 | h82
                            · linarith only [h82, h9, hc13, hlam, hphi, ht01, u0ehi8]
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h84 | h84
                              · linarith only [h0, h81, h84, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi3]
                              · linarith only [h0, h3, h81, h84, hc23, hc36, hlam, hphi]
                          · linarith only [h5, h7, h81, hc12, hc26, hlam, hphi]
            · rcases m.htr 0 2 6 (by decide) (by decide) with h88 | h88
              · linarith only [h6, h88, hc24, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h90 | h90
                · linarith only [h5, h6, h90, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h92 | h92
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h93 | h93
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h94 | h94
                      · linarith only [h2, h3, h94, hc16, hlam, hphi, ht01, ht0b, ht6b, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h96 | h96
                        · linarith only [h5, h6, h92, h94, h96, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h98 | h98
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h99 | h99
                            · linarith only [h90, h98, h99, hc12, hlam, hphi, ht01, u0ehi8]
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h101 | h101
                              · linarith only [h0, h101, h3, h98, hc16, hlam, hphi, ht01, ht0b, ht6b, u6ehi3]
                              · linarith only [h0, h101, h3, h98, hc23, hc36, hlam, hphi]
                          · linarith only [h5, h6, h98, hc12, hc24, hlam, hphi]
                    · linarith only [h5, h6, h92, h93, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h106 | h106
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h107 | h107
                      · linarith only [h107, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h109 | h109
                        · linarith only [h106, h107, h109, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h111 | h111
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h112 | h112
                            · linarith only [h111, h112, h90, hc12, hlam, hphi, ht01, u0ehi8]
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h114 | h114
                              · linarith only [h0, h111, h114, h3, hc16, hlam, hphi, ht01, ht0b, ht6b, u6ehi3]
                              · linarith only [h0, h111, h114, h3, hc23, hc36, hlam, hphi]
                          · linarith only [h111, h5, h6, hc12, hc24, hlam, hphi]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h118 | h118
                      · linarith only [h106, h118, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h120 | h120
                        · linarith only [h120, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h122 | h122
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h123 | h123
                            · linarith only [h123, h90, hc13, hlam, hphi, ht01, u0ehi8]
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h125 | h125
                              · linarith only [h0, h122, h125, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi3]
                              · linarith only [h0, h122, h125, h3, hc23, hc36, hlam, hphi]
                          · linarith only [h106, h120, h122, h5, h6, hc12, hc56, hlam, hphi, ht23, ht34, ht45]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h129 | h129
            · rcases m.htr 0 2 6 (by decide) (by decide) with h130 | h130
              · linarith only [h1, h130, h5, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h132 | h132
                · rcases m.htr 0 3 5 (by decide) (by decide) with h133 | h133
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h134 | h134
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h135 | h135
                      · linarith only [h1, h129, h135, h3, h5, hc16, hlam, hphi, ht01, ht0b, ht6b, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h137 | h137
                        · linarith only [h137, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h139 | h139
                          · linarith only [h139, h5, hc12, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h141 | h141
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h142 | h142
                              · linarith only [h1, h142, h3, hc16, hlam, hphi, ht01, ht0b, ht6b, u6ehi3]
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h144 | h144
                                · linarith only [h1, h134, h135, h141, h142, h144, h3, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi10]
                                · linarith only [h1, h141, h144, h3, hc34, hc46, hlam, hphi]
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h147 | h147
                              · linarith only [h1, h147, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi3]
                              · linarith only [h1, h132, h141, h147, h3, hc13, hc36, hlam, hphi]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h150 | h150
                      · linarith only [h129, h150, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h152 | h152
                        · linarith only [h152, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h154 | h154
                          · linarith only [h0, h154, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h156 | h156
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h157 | h157
                              · linarith only [h1, h157, h3, hc16, hlam, hphi, ht01, ht0b, ht6b, u6ehi3]
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h159 | h159
                                · linarith only [h1, h150, h156, h157, h159, h3, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                                · linarith only [h1, h156, h159, h3, hc34, hc46, hlam, hphi]
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h162 | h162
                              · linarith only [h1, h132, h156, h162, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi3]
                              · linarith only [h1, h132, h154, h156, h162, h3, hc12, hc36, hlam, hphi, ht23]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h165 | h165
                    · linarith only [h129, h133, h165, h5, hlam]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h167 | h167
                      · linarith only [h129, h133, h167, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h169 | h169
                        · linarith only [h169, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h171 | h171
                          · linarith only [h171, h5, hc12, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h173 | h173
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h174 | h174
                              · linarith only [h1, h174, h3, hc16, hlam, hphi, ht01, ht0b, ht6b, u6ehi3]
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h176 | h176
                                · linarith only [h1, h167, h173, h174, h176, h3, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                                · linarith only [h1, h173, h176, h3, hc34, hc46, hlam, hphi]
                            · linarith only [h132, h133, h169, h171, h173, hc12, hc56, hlam, hphi, ht23, ht34, ht45]
                · linarith only [h129, h132, h5, hlam]
            · rcases m.htr 0 2 6 (by decide) (by decide) with h181 | h181
              · linarith only [h181, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h183 | h183
                · rcases m.htr 0 3 5 (by decide) (by decide) with h184 | h184
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h185 | h185
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h186 | h186
                      · linarith only [h1, h183, h186, h3, hc16, hlam, hphi, ht01, ht0b, ht6b, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h188 | h188
                        · linarith only [h188, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h190 | h190
                          · linarith only [h190, h5, hc12, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h192 | h192
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h193 | h193
                              · linarith only [h1, h193, h3, hc16, hlam, hphi, ht01, ht0b, ht6b, u6ehi3]
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h195 | h195
                                · linarith only [h1, h192, h193, h195, h3, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi4]
                                · linarith only [h1, h192, h195, h3, hc34, hc46, hlam, hphi]
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h198 | h198
                              · linarith only [h1, h183, h192, h198, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi3]
                              · linarith only [h1, h183, h190, h192, h198, h3, hc12, hc36, hlam, hphi, ht23]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h201 | h201
                      · linarith only [h201, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h203 | h203
                        · linarith only [h203, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h205 | h205
                          · linarith only [h205, h5, hc12, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h207 | h207
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h208 | h208
                              · linarith only [h1, h208, h3, hc16, hlam, hphi, ht01, ht0b, ht6b, u6ehi3]
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h210 | h210
                                · linarith only [h1, h201, h207, h208, h210, h3, hc04, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                · linarith only [h1, h207, h210, h3, hc34, hc46, hlam, hphi]
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h213 | h213
                              · linarith only [h1, h183, h207, h213, h3, hc16, hlam, hphi, ht01, ht0b, ht6b, u6ehi3]
                              · linarith only [h1, h183, h205, h207, h213, h3, hc12, hc36, hlam, hphi, ht23]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h216 | h216
                    · linarith only [h183, h184, h216, hlam]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h218 | h218
                      · linarith only [h216, h218, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h220 | h220
                        · linarith only [h220, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h222 | h222
                          · linarith only [h222, h5, hc12, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h224 | h224
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h225 | h225
                              · linarith only [h1, h225, h3, hc16, hlam, hphi, ht01, ht0b, ht6b, u6ehi3]
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h227 | h227
                                · linarith only [h218, h227, hc14, hlam, hphi, ht01, u0ehi9]
                                · linarith only [h1, h224, h227, h3, hc34, hc46, hlam, hphi]
                            · linarith only [h183, h184, h220, h222, h224, hc12, hc56, hlam, hphi, ht23, ht34, ht45]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h231 | h231
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h232 | h232
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h233 | h233
                      · linarith only [h2, h233, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h235 | h235
                        · linarith only [h183, h231, h233, h235, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h237 | h237
                          · linarith only [h237, h5, hc12, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h239 | h239
                            · linarith only [h183, h239, hc13, hlam, hphi, ht01, u0ehi8]
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h241 | h241
                              · linarith only [h2, h239, h241, h3, hc16, hlam, hphi, ht01, ht0b, ht6b, u6ehi3]
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h243 | h243
                                · linarith only [h2, h241, h243, h3, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi4]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h245 | h245
                                  · linarith only [h183, h231, h245, hc23, hlam, hphi, ht01, ht12, u0ehi10]
                                  · linarith only [h245, h5, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                    · linarith only [h183, h231, h232, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h249 | h249
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h250 | h250
                      · linarith only [h2, h250, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h252 | h252
                        · linarith only [h249, h250, h252, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h254 | h254
                          · linarith only [h254, h5, hc12, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h256 | h256
                            · linarith only [h183, h256, hc13, hlam, hphi, ht01, u0ehi8]
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h258 | h258
                              · linarith only [h2, h256, h258, h3, hc16, hlam, hphi, ht01, ht0b, ht6b, u6ehi3]
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h260 | h260
                                · linarith only [h2, h258, h260, h3, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi4]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h262 | h262
                                  · linarith only [h183, h262, h5, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                                  · linarith only [h262, h5, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h265 | h265
                      · linarith only [h2, h265, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h267 | h267
                        · linarith only [h267, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h269 | h269
                          · linarith only [h269, h5, hc12, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h271 | h271
                            · linarith only [h183, h271, h5, hc13, hlam, hphi, ht01, u0ehi7]
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h273 | h273
                              · linarith only [h2, h271, h273, h3, hc16, hlam, hphi, ht01, ht0b, ht6b, u6ehi3]
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h275 | h275
                                · linarith only [h2, h265, h273, h275, h3, hc04, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h277 | h277
                                  · linarith only [h183, h277, h5, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                                  · linarith only [h277, h5, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
      · rcases m.htr 0 1 6 (by decide) (by decide) with h280 | h280
        · linarith only [h280, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h282 | h282
          · rcases m.htr 0 2 4 (by decide) (by decide) with h283 | h283
            · linarith only [h0, h2, h283, hlam]
            · rcases m.htr 0 2 6 (by decide) (by decide) with h285 | h285
              · linarith only [h0, h285, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h287 | h287
                · linarith only [h1, h2, h287, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h289 | h289
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h290 | h290
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h291 | h291
                      · linarith only [h291, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h293 | h293
                        · linarith only [h293, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h295 | h295
                          · linarith only [h0, h2, h291, h295, hc23, hc46, hlam, hphi, ht34]
                          · linarith only [h0, h2, h282, h291, h295, hc12, hc46, hlam, hphi, ht23, ht34]
                    · linarith only [h0, h2, h282, h289, h290, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h299 | h299
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h300 | h300
                      · linarith only [h300, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h302 | h302
                        · linarith only [h302, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h304 | h304
                          · linarith only [h0, h2, h300, h304, hc23, hc46, hlam, hphi, ht34]
                          · linarith only [h282, h283, h304, hc12, hc24, hlam, hphi]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h307 | h307
                      · linarith only [h307, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h309 | h309
                        · linarith only [h309, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h311 | h311
                          · linarith only [h0, h2, h299, h309, h311, hc23, hc56, hlam, hphi, ht34, ht45]
                          · linarith only [h0, h2, h282, h299, h309, h311, hc12, hc56, hlam, hphi, ht23, ht34, ht45]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h314 | h314
            · linarith only [h1, h2, h282, h314, hlam]
            · rcases m.htr 0 2 6 (by decide) (by decide) with h316 | h316
              · linarith only [h1, h282, h316, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h318 | h318
                · linarith only [h1, h2, h318, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h320 | h320
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h321 | h321
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h322 | h322
                      · linarith only [h322, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h324 | h324
                        · linarith only [h1, h2, h320, h322, h324, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h326 | h326
                          · linarith only [h0, h2, h322, h326, hc23, hc46, hlam, hphi, ht34]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h328 | h328
                            · linarith only [h1, h2, h322, h328, hc34, hc46, hlam, hphi]
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h330 | h330
                              · linarith only [h1, h2, h322, h330, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi3]
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h332 | h332
                                · linarith only [h1, h2, h322, h326, h328, h332, hc12, hc34, hlam, hphi, ht23]
                                · linarith only [h1, h2, h282, h332, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                    · linarith only [h1, h2, h320, h321, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h336 | h336
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h337 | h337
                      · linarith only [h337, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h339 | h339
                        · linarith only [h339, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h341 | h341
                          · linarith only [h282, h341, hc12, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h343 | h343
                            · linarith only [h1, h2, h337, h343, hc34, hc46, hlam, hphi]
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h345 | h345
                              · linarith only [h1, h2, h337, h345, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi3]
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h347 | h347
                                · linarith only [h1, h2, h337, h341, h343, h347, hc12, hc34, hlam, hphi, ht23]
                                · linarith only [h1, h2, h282, h347, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h350 | h350
                      · linarith only [h350, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h352 | h352
                        · linarith only [h352, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h354 | h354
                          · linarith only [h282, h354, hc12, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h356 | h356
                            · linarith only [h1, h2, h336, h352, h356, hc34, hc56, hlam, hphi, ht45]
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h358 | h358
                              · linarith only [h1, h2, h336, h352, h358, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, u6ehi3]
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h360 | h360
                                · linarith only [h1, h2, h350, h354, h356, h360, hc12, hc34, hlam, hphi, ht23]
                                · linarith only [h1, h2, h282, h360, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h363 | h363
      · rcases m.htr 0 1 6 (by decide) (by decide) with h364 | h364
        · linarith only [h364, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h366 | h366
          · linarith only [h0, h1, h366, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h368 | h368
            · rcases m.htr 0 2 6 (by decide) (by decide) with h369 | h369
              · linarith only [h0, h369, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h371 | h371
                · rcases m.htr 0 3 5 (by decide) (by decide) with h372 | h372
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h373 | h373
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h374 | h374
                      · linarith only [h0, h1, h368, h374, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h376 | h376
                        · linarith only [h376, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h378 | h378
                          · linarith only [h366, h378, hc12, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h380 | h380
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h381 | h381
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h382 | h382
                                · linarith only [h363, h364, h378, h381, h382, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi4]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h384 | h384
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h385 | h385
                                    · rcases m.htr 2 3 6 (by decide) (by decide) with h386 | h386
                                      · rcases m.htr 2 4 5 (by decide) (by decide) with h387 | h387
                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h388 | h388
                                          · linarith only [h0, h364, h368, h382, h388, hlam]
                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h390 | h390
                                            · rcases m.htr 3 4 6 (by decide) (by decide) with h391 | h391
                                              · linarith only [h0, h364, h368, h382, h384, h391, hlam]
                                              · rcases m.htr 3 5 6 (by decide) (by decide) with h393 | h393
                                                · linarith only [h0, h364, h368, h376, h382, h385, h387, h393, hc05, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht56, ht6b]
                                                · rcases m.htr 4 5 6 (by decide) (by decide) with h395 | h395
                                                  · linarith only [h0, h364, h368, h376, h382, h384, h390, h395, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi10]
                                                  · linarith only [h0, h364, h368, h382, h384, h390, h395, hc45, hc56, hlam, hphi]
                                            · linarith only [h0, h368, h387, h390, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo0]
                                        · linarith only [h0, h364, h368, h373, h382, h387, hc24, hc46, hlam, hphi]
                                      · linarith only [h378, h381, h386, hlam]
                                    · linarith only [h372, h378, h381, h385, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi3]
                                  · linarith only [h0, h364, h378, h381, h384, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h0, h1, h368, h373, h381, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi10]
                            · linarith only [h0, h1, h368, h373, h380, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi10]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h405 | h405
                      · linarith only [h0, h368, h405, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h407 | h407
                        · linarith only [h407, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h409 | h409
                          · linarith only [h366, h409, hc12, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h411 | h411
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h412 | h412
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h413 | h413
                                · linarith only [h363, h364, h405, h409, h412, h413, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h415 | h415
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h416 | h416
                                    · rcases m.htr 2 3 6 (by decide) (by decide) with h417 | h417
                                      · rcases m.htr 2 4 5 (by decide) (by decide) with h418 | h418
                                        · linarith only [h368, h373, h418, hlam, hphi, u0ehi9, u0elo1]
                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h420 | h420
                                          · linarith only [h0, h364, h368, h413, h420, hlam]
                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h422 | h422
                                            · linarith only [h0, h364, h368, h373, h413, h415, h422, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi9]
                                            · rcases m.htr 3 4 6 (by decide) (by decide) with h424 | h424
                                              · linarith only [h0, h364, h368, h413, h415, h424, hlam]
                                              · rcases m.htr 3 5 6 (by decide) (by decide) with h426 | h426
                                                · linarith only [h372, h407, h426, hc05, hlam, hphi, ht0b, ht56, ht6b, u0elo2]
                                                · rcases m.htr 4 5 6 (by decide) (by decide) with h428 | h428
                                                  · linarith only [h373, h407, h428, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi9]
                                                  · linarith only [h373, h428, hc56, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi9]
                                      · linarith only [h409, h412, h417, hlam]
                                    · linarith only [h372, h409, h412, h416, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi3]
                                  · linarith only [h0, h364, h409, h412, h415, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h0, h1, h368, h412, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                            · linarith only [h0, h1, h368, h411, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h436 | h436
                    · linarith only [h0, h1, h368, h372, h436, hlam]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h438 | h438
                      · linarith only [h0, h368, h438, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h440 | h440
                        · linarith only [h440, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h442 | h442
                          · linarith only [h366, h442, hc12, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h444 | h444
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h445 | h445
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h446 | h446
                                · linarith only [h1, h363, h372, h438, h440, h446, hc56, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi9]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h448 | h448
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h449 | h449
                                    · linarith only [h0, h1, h372, h449, hc12, hc23, hlam, hphi]
                                    · linarith only [h366, h368, h449, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                                  · linarith only [h442, h445, h448, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi3]
                              · linarith only [h0, h1, h368, h445, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                            · linarith only [h0, h1, h368, h444, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                · linarith only [h0, h1, h368, h371, hlam]
            · rcases m.htr 0 2 6 (by decide) (by decide) with h456 | h456
              · linarith only [h456, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h458 | h458
                · rcases m.htr 0 3 5 (by decide) (by decide) with h459 | h459
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h460 | h460
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h461 | h461
                      · linarith only [h1, h363, h461, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h463 | h463
                        · linarith only [h463, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h465 | h465
                          · linarith only [h0, h1, h366, h465, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht56, ht6b, u0elo2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h467 | h467
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h468 | h468
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h469 | h469
                                · linarith only [h363, h364, h368, h461, h465, h468, h469, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h471 | h471
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h472 | h472
                                    · rcases m.htr 2 3 6 (by decide) (by decide) with h473 | h473
                                      · rcases m.htr 2 4 5 (by decide) (by decide) with h474 | h474
                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h475 | h475
                                          · linarith only [h0, h364, h469, h471, h475, hc12, hc23, hlam, hphi]
                                          · linarith only [h368, h475, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                                        · linarith only [h363, h368, h460, h474, hlam, hphi, u0ehi7, u0elo0]
                                      · linarith only [h1, h465, h473, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                                    · linarith only [h459, h465, h468, h472, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi1]
                                  · linarith only [h363, h364, h368, h465, h467, h468, h471, hc14, hlam, hphi, ht01, u0ehi7]
                              · linarith only [h1, h363, h368, h468, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                            · linarith only [h1, h363, h368, h467, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h484 | h484
                      · linarith only [h363, h484, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h486 | h486
                        · linarith only [h486, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h488 | h488
                          · linarith only [h366, h488, hc12, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h490 | h490
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h491 | h491
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h492 | h492
                                · linarith only [h363, h364, h484, h488, h491, h492, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h494 | h494
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h495 | h495
                                    · rcases m.htr 2 3 6 (by decide) (by decide) with h496 | h496
                                      · rcases m.htr 2 4 5 (by decide) (by decide) with h497 | h497
                                        · linarith only [h368, h460, h497, hc24, hlam, hphi, ht01, ht12, u0ehi7]
                                        · linarith only [h368, h497, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                                      · linarith only [h488, h491, h496, hlam]
                                    · linarith only [h459, h488, h491, h495, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi3]
                                  · linarith only [h363, h364, h488, h490, h491, h494, hlam]
                              · linarith only [h0, h1, h491, hc12, hc36, hlam, hphi, ht23]
                            · linarith only [h1, h363, h368, h490, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h505 | h505
                    · linarith only [h1, h363, h459, h505, hlam]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h507 | h507
                      · linarith only [h363, h507, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h509 | h509
                        · linarith only [h509, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h511 | h511
                          · linarith only [h0, h1, h459, h509, h511, hc23, hc56, hlam, hphi, ht34, ht45]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h513 | h513
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h514 | h514
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h515 | h515
                                · linarith only [h1, h363, h459, h507, h509, h515, hc04, hc56, hlam, hphi, ht45]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h517 | h517
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h518 | h518
                                    · linarith only [h0, h1, h459, h518, hc12, hc23, hlam, hphi]
                                    · linarith only [h366, h518, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                                  · linarith only [h363, h364, h511, h513, h514, h517, hlam]
                              · linarith only [h1, h363, h368, h514, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                            · linarith only [h1, h363, h368, h513, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                · linarith only [h1, h363, h458, hlam]
      · rcases m.htr 0 1 6 (by decide) (by decide) with h525 | h525
        · linarith only [h525, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h527 | h527
          · linarith only [h0, h1, h527, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h529 | h529
            · linarith only [h0, h363, h529, hlam]
            · rcases m.htr 0 2 6 (by decide) (by decide) with h531 | h531
              · linarith only [h0, h531, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h533 | h533
                · rcases m.htr 0 3 5 (by decide) (by decide) with h534 | h534
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h535 | h535
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h536 | h536
                      · linarith only [h533, h536, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h538 | h538
                        · linarith only [h538, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h540 | h540
                          · linarith only [h527, h540, hc12, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h542 | h542
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h543 | h543
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h544 | h544
                                · linarith only [h0, h363, h536, h540, h542, h544, hc12, hc23, hlam, hphi]
                                · linarith only [h0, h363, h544, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                              · linarith only [h0, h1, h543, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                            · linarith only [h0, h1, h533, h542, hlam, hphi, u0ehi7, u0elo2]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h549 | h549
                      · linarith only [h549, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h551 | h551
                        · linarith only [h534, h551, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h553 | h553
                          · linarith only [h0, h363, h535, h551, h553, hc23, hc56, hlam, hphi, ht34, ht45]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h555 | h555
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h556 | h556
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h557 | h557
                                · linarith only [h0, h363, h549, h553, h555, h557, hc12, hc23, hlam, hphi]
                                · linarith only [h0, h363, h557, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                              · linarith only [h0, h1, h556, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                            · linarith only [h0, h1, h533, h555, hlam, hphi, u0ehi7, u0elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h562 | h562
                    · linarith only [h533, h534, h562, hlam]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h564 | h564
                      · linarith only [h533, h534, h564, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h566 | h566
                        · linarith only [h566, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h568 | h568
                          · linarith only [h0, h1, h534, h566, h568, hc23, hc56, hlam, hphi, ht34, ht45]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h570 | h570
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h571 | h571
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h572 | h572
                                · linarith only [h0, h363, h564, h568, h570, h572, hc12, hc23, hlam, hphi]
                                · linarith only [h0, h363, h572, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                              · linarith only [h0, h1, h571, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                            · linarith only [h0, h1, h533, h534, h566, h570, hc56, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi7]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h577 | h577
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h578 | h578
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h579 | h579
                      · linarith only [h579, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h581 | h581
                        · linarith only [h577, h581, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h583 | h583
                          · linarith only [h0, h1, h533, h579, h583, hc23, hc46, hlam, hphi, ht34]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h585 | h585
                            · linarith only [h0, h1, h533, h583, h585, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1, h585, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                    · linarith only [h533, h577, h578, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h589 | h589
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h590 | h590
                      · linarith only [h590, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h592 | h592
                        · linarith only [h592, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h594 | h594
                          · linarith only [h0, h1, h577, h594, hc23, hc35, hlam, hphi]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h596 | h596
                            · linarith only [h0, h1, h533, h594, h596, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1, h596, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h599 | h599
                      · linarith only [h589, h599, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h601 | h601
                        · linarith only [h601, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h603 | h603
                          · linarith only [h0, h363, h589, h601, h603, hc23, hc56, hlam, hphi, ht34, ht45]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h605 | h605
                            · linarith only [h0, h1, h533, h603, h605, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1, h605, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h608 | h608
    · rcases m.htr 0 1 4 (by decide) (by decide) with h609 | h609
      · rcases m.htr 0 1 6 (by decide) (by decide) with h610 | h610
        · linarith only [h610, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h612 | h612
          · rcases m.htr 0 2 4 (by decide) (by decide) with h613 | h613
            · rcases m.htr 0 2 6 (by decide) (by decide) with h614 | h614
              · linarith only [h614, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h616 | h616
                · rcases m.htr 0 3 5 (by decide) (by decide) with h617 | h617
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h618 | h618
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h619 | h619
                      · linarith only [h0, h608, h614, h616, h619, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h621 | h621
                        · linarith only [h621, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h623 | h623
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h624 | h624
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h625 | h625
                              · linarith only [h0, h608, h614, h625, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi3]
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h627 | h627
                                · linarith only [h608, h610, h619, h624, h625, h627, hc04, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                · linarith only [h608, h610, h624, h627, hc34, hc46, hlam, hphi]
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h630 | h630
                              · linarith only [h608, h616, h624, h630, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi3]
                              · linarith only [h608, h610, h616, h624, h630, hc13, hc36, hlam, hphi]
                          · linarith only [h0, h623, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h634 | h634
                      · linarith only [h608, h617, h618, h634, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h636 | h636
                        · linarith only [h0, h608, h614, h617, h636, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h638 | h638
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h639 | h639
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h640 | h640
                              · linarith only [h0, h608, h614, h640, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi3]
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h642 | h642
                                · linarith only [h634, h642, hc14, hlam, hphi, ht01, u0ehi9]
                                · linarith only [h608, h610, h639, h642, hc34, hc46, hlam, hphi]
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h645 | h645
                              · linarith only [h639, h645, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi3]
                              · linarith only [h608, h610, h616, h638, h639, h645, hc23, hc36, hlam, hphi]
                          · linarith only [h0, h638, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h649 | h649
                    · linarith only [h616, h617, h649, hlam]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h651 | h651
                      · linarith only [h608, h616, h651, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h653 | h653
                        · linarith only [h653, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h655 | h655
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h656 | h656
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h657 | h657
                              · linarith only [h0, h608, h614, h657, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi3]
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h659 | h659
                                · linarith only [h608, h610, h651, h656, h657, h659, hc04, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                · linarith only [h608, h610, h656, h659, hc34, hc46, hlam, hphi]
                            · linarith only [h616, h617, h653, h656, hc13, hc56, hlam, hphi, ht34, ht45]
                          · linarith only [h0, h655, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h664 | h664
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h665 | h665
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h666 | h666
                      · linarith only [h609, h666, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h668 | h668
                        · linarith only [h664, h668, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h670 | h670
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h671 | h671
                            · linarith only [h616, h671, hc13, hlam, hphi, ht01, u0ehi8]
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h673 | h673
                              · linarith only [h0, h609, h614, h671, h673, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi3]
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h675 | h675
                                · linarith only [h609, h610, h666, h673, h675, hc04, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht56, ht6b]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h677 | h677
                                  · linarith only [h616, h664, h677, hc23, hlam, hphi, ht01, ht12, u0ehi10]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h679 | h679
                                    · rcases m.htr 2 3 6 (by decide) (by decide) with h680 | h680
                                      · linarith only [h609, h610, h670, h671, h675, h680, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi3]
                                      · rcases m.htr 2 4 5 (by decide) (by decide) with h682 | h682
                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h683 | h683
                                          · linarith only [h610, h613, h614, h675, h680, h683, hc01, hc36, hlam, hphi, ht12, ht23]
                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h685 | h685
                                            · rcases m.htr 3 4 6 (by decide) (by decide) with h686 | h686
                                              · linarith only [h0, h609, h614, h670, h671, h679, h683, h685, h686, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b]
                                              · linarith only [h616, h664, h686, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi10]
                                            · linarith only [h616, h664, h685, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi10]
                                        · linarith only [h665, h666, h682, hc24, hc46, hlam, hphi]
                                    · linarith only [h616, h664, h679, hc23, hc34, hlam, hphi]
                          · linarith only [h0, h609, h616, h664, h670, hc23, hlam, hphi, ht01, ht12, u0ehi10]
                    · linarith only [h616, h664, h665, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h694 | h694
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h695 | h695
                      · linarith only [h609, h695, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h697 | h697
                        · linarith only [h694, h695, h697, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h699 | h699
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h700 | h700
                            · linarith only [h616, h700, hc13, hlam, hphi, ht01, u0ehi8]
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h702 | h702
                              · linarith only [h0, h609, h614, h700, h702, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi3]
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h704 | h704
                                · linarith only [h609, h610, h702, h704, hc36, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi4]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h706 | h706
                                  · linarith only [h609, h610, h616, h699, h700, h704, h706, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h708 | h708
                                    · linarith only [h609, h610, h664, h699, h700, h704, h708, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8]
                                    · rcases m.htr 2 3 6 (by decide) (by decide) with h710 | h710
                                      · linarith only [h609, h610, h699, h700, h704, h710, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi3]
                                      · rcases m.htr 2 4 5 (by decide) (by decide) with h712 | h712
                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h713 | h713
                                          · linarith only [h610, h704, h713, hc24, hlam, hphi, ht01, ht12, u0ehi6]
                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h715 | h715
                                            · rcases m.htr 3 4 6 (by decide) (by decide) with h716 | h716
                                              · linarith only [h613, h614, h712, h713, h716, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht56, ht6b]
                                              · linarith only [h616, h716, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8]
                                            · linarith only [h616, h712, h715, hc24, hlam, hphi, ht01, ht12, u0ehi8]
                                        · linarith only [h694, h695, h712, hc24, hc46, hlam, hphi]
                          · linarith only [h0, h699, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h722 | h722
                      · linarith only [h609, h722, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h724 | h724
                        · linarith only [h724, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h726 | h726
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h727 | h727
                            · linarith only [h608, h616, h727, hlam, hphi, u0ehi8, u0elo0]
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h729 | h729
                              · linarith only [h0, h609, h614, h727, h729, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi3]
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h731 | h731
                                · linarith only [h609, h610, h616, h722, h729, h731, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h733 | h733
                                  · linarith only [h609, h610, h616, h726, h727, h731, h733, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h735 | h735
                                    · linarith only [h609, h610, h664, h726, h727, h731, h735, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8]
                                    · rcases m.htr 2 3 6 (by decide) (by decide) with h737 | h737
                                      · linarith only [h609, h610, h726, h727, h731, h737, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi3]
                                      · rcases m.htr 2 4 5 (by decide) (by decide) with h739 | h739
                                        · linarith only [h616, h694, h739, hc24, hlam, hphi, ht01, ht12, u0ehi8]
                                        · rcases m.htr 2 4 6 (by decide) (by decide) with h741 | h741
                                          · linarith only [h610, h613, h614, h731, h737, h741, hc01, hc36, hlam, hphi, ht12, ht23]
                                          · rcases m.htr 3 4 5 (by decide) (by decide) with h743 | h743
                                            · linarith only [h616, h694, h743, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                                            · linarith only [h616, h743, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8]
                          · linarith only [h0, h609, h616, h726, hc23, hlam, hphi, ht01, ht12, u0ehi8]
            · linarith only [h0, h609, h613, hlam]
          · linarith only [h0, h608, h612, hlam]
      · rcases m.htr 0 1 6 (by decide) (by decide) with h749 | h749
        · linarith only [h749, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h751 | h751
          · rcases m.htr 0 2 4 (by decide) (by decide) with h752 | h752
            · rcases m.htr 0 2 6 (by decide) (by decide) with h753 | h753
              · linarith only [h753, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h755 | h755
                · linarith only [h608, h609, h755, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h757 | h757
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h758 | h758
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h759 | h759
                      · linarith only [h752, h753, h759, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h761 | h761
                        · linarith only [h761, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h763 | h763
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h764 | h764
                            · linarith only [h755, h764, hc13, hlam, hphi, ht01, u0ehi8]
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h766 | h766
                              · linarith only [h608, h609, h759, h766, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi3]
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h768 | h768
                                · linarith only [h608, h609, h759, h764, h768, hc13, hc34, hlam, hphi]
                                · linarith only [h608, h609, h757, h768, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi10]
                          · linarith only [h0, h608, h757, h763, hc23, hlam, hphi, ht01, ht12, u0ehi10]
                    · linarith only [h608, h609, h757, h758, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h773 | h773
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h774 | h774
                      · linarith only [h774, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h776 | h776
                        · linarith only [h776, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h778 | h778
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h779 | h779
                            · linarith only [h608, h609, h774, h779, hc34, hc46, hlam, hphi]
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h781 | h781
                              · linarith only [h608, h609, h774, h781, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi3]
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h783 | h783
                                · linarith only [h608, h609, h774, h779, h783, hc13, hc34, hlam, hphi]
                                · linarith only [h608, h609, h783, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8]
                          · linarith only [h0, h608, h778, hc23, hlam, hphi, ht01, ht12, u0ehi8]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h787 | h787
                      · linarith only [h787, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h789 | h789
                        · linarith only [h789, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h791 | h791
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h792 | h792
                            · linarith only [h608, h609, h773, h789, h792, hc34, hc56, hlam, hphi, ht45]
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h794 | h794
                              · linarith only [h608, h609, h773, h789, h794, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, u6ehi3]
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h796 | h796
                                · linarith only [h608, h609, h787, h792, h796, hc13, hc34, hlam, hphi]
                                · linarith only [h608, h609, h796, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8]
                          · linarith only [h0, h608, h791, hc23, hlam, hphi, ht01, ht12, u0ehi8]
            · rcases m.htr 0 2 6 (by decide) (by decide) with h800 | h800
              · linarith only [h800, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h802 | h802
                · linarith only [h608, h609, h802, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h804 | h804
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h805 | h805
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h806 | h806
                      · linarith only [h806, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h808 | h808
                        · linarith only [h608, h804, h808, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h810 | h810
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h811 | h811
                            · linarith only [h0, h608, h752, h806, h811, hc34, hc46, hlam, hphi]
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h813 | h813
                              · linarith only [h0, h608, h752, h806, h813, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi3]
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h815 | h815
                                · linarith only [h0, h608, h752, h806, h811, h815, hc13, hc34, hlam, hphi]
                                · linarith only [h608, h609, h804, h815, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi10]
                          · linarith only [h0, h608, h804, h810, hc23, hlam, hphi, ht01, ht12, u0ehi10]
                    · linarith only [h0, h608, h752, h804, h805, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h820 | h820
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h821 | h821
                      · linarith only [h821, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h823 | h823
                        · linarith only [h823, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h825 | h825
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h826 | h826
                            · linarith only [h608, h609, h821, h826, hc34, hc46, hlam, hphi]
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h828 | h828
                              · linarith only [h0, h608, h752, h821, h828, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi3]
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h830 | h830
                                · linarith only [h0, h608, h752, h821, h826, h830, hc13, hc34, hlam, hphi]
                                · linarith only [h608, h609, h830, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8]
                          · linarith only [h0, h608, h825, hc23, hlam, hphi, ht01, ht12, u0ehi8]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h834 | h834
                      · linarith only [h834, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h836 | h836
                        · linarith only [h836, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h838 | h838
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h839 | h839
                            · linarith only [h608, h609, h820, h836, h839, hc34, hc56, hlam, hphi, ht45]
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h841 | h841
                              · linarith only [h0, h608, h752, h820, h836, h841, hc56, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht45, ht6b, u6ehi3]
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h843 | h843
                                · linarith only [h0, h608, h752, h834, h839, h843, hc13, hc34, hlam, hphi]
                                · linarith only [h608, h609, h843, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi8]
                          · linarith only [h0, h608, h838, hc23, hlam, hphi, ht01, ht12, u0ehi8]
          · linarith only [h0, h608, h751, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h848 | h848
      · rcases m.htr 0 1 6 (by decide) (by decide) with h849 | h849
        · linarith only [h849, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h851 | h851
          · rcases m.htr 0 2 4 (by decide) (by decide) with h852 | h852
            · rcases m.htr 0 2 6 (by decide) (by decide) with h853 | h853
              · linarith only [h853, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h855 | h855
                · rcases m.htr 0 3 5 (by decide) (by decide) with h856 | h856
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h857 | h857
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h858 | h858
                      · linarith only [h608, h848, h851, h853, h858, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h860 | h860
                        · linarith only [h860, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h862 | h862
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h863 | h863
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h864 | h864
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h865 | h865
                                · linarith only [h608, h848, h851, h853, h858, h865, hc04, hc26, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h867 | h867
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h868 | h868
                                    · rcases m.htr 2 3 6 (by decide) (by decide) with h869 | h869
                                      · linarith only [h851, h853, h869, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi3]
                                      · linarith only [h851, h853, h862, h864, h867, h869, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b]
                                    · linarith only [h848, h849, h856, h857, h865, h867, h868, hc34, hc46, hlam, hphi, u0ehi10, u0elo2]
                                  · linarith only [h848, h849, h863, h865, h867, hc23, hc46, hlam, hphi, ht34]
                              · linarith only [h608, h864, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                            · linarith only [h608, h848, h857, h863, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi10]
                          · linarith only [h0, h848, h857, h862, hc23, hlam, hphi, ht01, ht12, u0ehi10]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h877 | h877
                      · linarith only [h877, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h879 | h879
                        · linarith only [h851, h853, h856, h879, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h881 | h881
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h882 | h882
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h883 | h883
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h884 | h884
                                · linarith only [h608, h848, h851, h853, h877, h884, hc04, hc26, hlam, hphi, ht01, ht0b, ht12, ht45, ht56, ht6b]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h886 | h886
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h887 | h887
                                    · rcases m.htr 2 3 6 (by decide) (by decide) with h888 | h888
                                      · linarith only [h851, h853, h888, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi3]
                                      · linarith only [h851, h853, h883, h886, h888, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht56, ht6b]
                                    · linarith only [h851, h856, h886, h887, hc34, hlam, hphi, ht0b, ht45, ht56, ht6b, u0elo1]
                                  · linarith only [h848, h849, h882, h884, h886, hc23, hc46, hlam, hphi, ht34]
                              · linarith only [h608, h883, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                            · linarith only [h608, h848, h882, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                          · linarith only [h0, h848, h881, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h896 | h896
                    · linarith only [h608, h848, h856, h896, hlam]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h898 | h898
                      · linarith only [h848, h898, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h900 | h900
                        · linarith only [h900, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h902 | h902
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h903 | h903
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h904 | h904
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h905 | h905
                                · linarith only [h608, h848, h856, h898, h900, h905, hc04, hc56, hlam, hphi, ht45]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h907 | h907
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h908 | h908
                                    · linarith only [h608, h851, h853, h856, h908, hc01, hc26, hlam, hphi, ht12]
                                    · rcases m.htr 2 3 6 (by decide) (by decide) with h910 | h910
                                      · linarith only [h851, h853, h910, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi3]
                                      · linarith only [h853, h904, h910, hc13, hlam, hphi, ht01, u0ehi7]
                                  · linarith only [h608, h848, h856, h900, h903, h907, hc23, hc56, hlam, hphi, ht34, ht45]
                              · linarith only [h608, h848, h904, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                            · linarith only [h608, h848, h903, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                          · linarith only [h0, h848, h902, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                · linarith only [h608, h848, h855, hlam]
            · linarith only [h608, h848, h851, h852, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h919 | h919
            · rcases m.htr 0 2 6 (by decide) (by decide) with h920 | h920
              · linarith only [h920, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h922 | h922
                · rcases m.htr 0 3 5 (by decide) (by decide) with h923 | h923
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h924 | h924
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h925 | h925
                      · linarith only [h848, h925, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h927 | h927
                        · linarith only [h927, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h929 | h929
                          · linarith only [h0, h851, h929, hc12, hlam, hphi, ht01, u0ehi6]
                          · linarith only [h0, h848, h924, h929, hc23, hlam, hphi, ht01, ht12, u0ehi10]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h932 | h932
                      · linarith only [h848, h932, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h934 | h934
                        · linarith only [h934, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h936 | h936
                          · linarith only [h0, h851, h936, hc12, hlam, hphi, ht01, u0ehi6]
                          · linarith only [h0, h848, h936, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h939 | h939
                    · linarith only [h608, h848, h923, h939, hlam]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h941 | h941
                      · linarith only [h848, h941, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h943 | h943
                        · linarith only [h943, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h945 | h945
                          · linarith only [h0, h851, h945, hc12, hlam, hphi, ht01, u0ehi6]
                          · linarith only [h0, h848, h945, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                · linarith only [h0, h848, h851, h922, hlam]
            · linarith only [h0, h848, h919, hlam]
      · rcases m.htr 0 1 6 (by decide) (by decide) with h950 | h950
        · linarith only [h950, hlam, hphi, ht0b, ht6b, u0elo0, u6ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h952 | h952
          · rcases m.htr 0 2 4 (by decide) (by decide) with h953 | h953
            · rcases m.htr 0 2 6 (by decide) (by decide) with h954 | h954
              · linarith only [h954, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h956 | h956
                · rcases m.htr 0 3 5 (by decide) (by decide) with h957 | h957
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h958 | h958
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h959 | h959
                      · linarith only [h952, h954, h956, h959, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h961 | h961
                        · linarith only [h961, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h963 | h963
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h964 | h964
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h965 | h965
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h966 | h966
                                · linarith only [h848, h959, h963, h964, h966, hc12, hlam, hphi, ht01, u0ehi6]
                                · linarith only [h848, h966, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                              · linarith only [h608, h965, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                            · linarith only [h608, h952, h956, h964, hlam, hphi, u0ehi6, u0elo1]
                          · linarith only [h952, h954, h963, hc12, hc26, hlam, hphi]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h972 | h972
                      · linarith only [h972, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h974 | h974
                        · linarith only [h952, h954, h957, h974, hc26, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h976 | h976
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h977 | h977
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h978 | h978
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h979 | h979
                                · linarith only [h972, h976, h977, h979, hc12, hlam, hphi, ht01, u0ehi9]
                                · linarith only [h848, h979, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                              · linarith only [h608, h978, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                            · linarith only [h608, h952, h954, h956, h977, hc26, hlam, hphi, ht01, ht12, u0ehi6]
                          · linarith only [h952, h954, h976, hc12, hc26, hlam, hphi]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h985 | h985
                    · linarith only [h956, h957, h985, hlam]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h987 | h987
                      · linarith only [h956, h987, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h989 | h989
                        · linarith only [h989, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h991 | h991
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h992 | h992
                            · rcases m.htr 1 3 6 (by decide) (by decide) with h993 | h993
                              · rcases m.htr 1 4 6 (by decide) (by decide) with h994 | h994
                                · linarith only [h987, h991, h992, h994, hc12, hlam, hphi, ht01, u0ehi9]
                                · linarith only [h848, h994, hc46, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                              · linarith only [h608, h993, hc36, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                            · linarith only [h608, h956, h957, h989, h992, hc56, hlam, hphi, ht01, ht12, ht23, ht34, ht45, u0ehi6]
                          · linarith only [h952, h954, h991, hc12, hc26, hlam, hphi]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1000 | h1000
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1001 | h1001
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h1002 | h1002
                      · linarith only [h1002, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1004 | h1004
                        · linarith only [h1000, h1004, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1006 | h1006
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1007 | h1007
                            · linarith only [h1006, h1007, h956, hc12, hlam, hphi, ht01, u0ehi8]
                            · linarith only [h1007, h608, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                          · linarith only [h1006, h952, h954, hc12, hc26, hlam, hphi]
                    · linarith only [h1000, h1001, h956, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1012 | h1012
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h1013 | h1013
                      · linarith only [h1013, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1015 | h1015
                        · linarith only [h1015, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1017 | h1017
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1018 | h1018
                            · linarith only [h1017, h1018, h956, hc12, hlam, hphi, ht01, u0ehi8]
                            · linarith only [h1018, h608, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                          · linarith only [h1017, h952, h954, hc12, hc26, hlam, hphi]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h1022 | h1022
                      · linarith only [h1022, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1024 | h1024
                        · linarith only [h1024, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1026 | h1026
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1027 | h1027
                            · linarith only [h1026, h1027, h608, h956, hc12, hlam, hphi, ht01, u0ehi6]
                            · linarith only [h1027, h608, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                          · linarith only [h1026, h952, h954, hc12, hc26, hlam, hphi]
            · rcases m.htr 0 2 6 (by decide) (by decide) with h1031 | h1031
              · linarith only [h1031, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1033 | h1033
                · linarith only [h1033, h952, h953, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1035 | h1035
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1036 | h1036
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h1037 | h1037
                      · linarith only [h1037, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1039 | h1039
                        · linarith only [h1035, h1039, h952, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1041 | h1041
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1042 | h1042
                            · linarith only [h1033, h1041, h1042, hc12, hlam, hphi, ht01, u0ehi8]
                            · linarith only [h1042, h608, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                          · linarith only [h1037, h1041, h952, h953, hc12, hc46, hlam, hphi, ht23, ht34]
                    · linarith only [h1035, h1036, h952, h953, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1047 | h1047
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h1048 | h1048
                      · linarith only [h1048, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1050 | h1050
                        · linarith only [h1047, h1048, h1050, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1052 | h1052
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1053 | h1053
                            · linarith only [h1033, h1052, h1053, hc12, hlam, hphi, ht01, u0ehi8]
                            · linarith only [h1053, h608, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                          · linarith only [h1048, h1052, h952, h953, hc12, hc46, hlam, hphi, ht23, ht34]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h1057 | h1057
                      · linarith only [h1057, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1059 | h1059
                        · linarith only [h1059, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1061 | h1061
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1062 | h1062
                            · linarith only [h1033, h1061, h1062, h608, hc12, hlam, hphi, ht01, u0ehi6]
                            · linarith only [h1062, h608, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                          · linarith only [h1047, h1059, h1061, h952, h953, hc12, hc56, hlam, hphi, ht23, ht34, ht45]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1066 | h1066
            · rcases m.htr 0 2 6 (by decide) (by decide) with h1067 | h1067
              · linarith only [h1067, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1069 | h1069
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1070 | h1070
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1071 | h1071
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h1072 | h1072
                      · linarith only [h1066, h1072, h952, hc23, hlam, hphi, ht01, ht0b, ht12, ht6b, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1074 | h1074
                        · linarith only [h1074, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1076 | h1076
                          · linarith only [h1076, h952, hc12, hlam, hphi, ht01, u0ehi7]
                          · linarith only [h0, h1076, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h1079 | h1079
                      · linarith only [h1066, h1079, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1081 | h1081
                        · linarith only [h1081, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1083 | h1083
                          · linarith only [h1083, h952, hc12, hlam, hphi, ht01, u0ehi7]
                          · linarith only [h0, h1083, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1086 | h1086
                    · linarith only [h1066, h1070, h1086, h952, hlam]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h1088 | h1088
                      · linarith only [h1066, h1088, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1090 | h1090
                        · linarith only [h1090, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1092 | h1092
                          · linarith only [h1092, h952, hc12, hlam, hphi, ht01, u0ehi7]
                          · linarith only [h0, h1092, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                · linarith only [h1066, h1069, h952, hlam]
            · rcases m.htr 0 2 6 (by decide) (by decide) with h1096 | h1096
              · linarith only [h1096, hlam, hphi, ht0b, ht6b, u0elo1, u6ehi2]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1098 | h1098
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1099 | h1099
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1100 | h1100
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h1101 | h1101
                      · linarith only [h1098, h1101, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1103 | h1103
                        · linarith only [h1100, h1101, h1103, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1105 | h1105
                          · linarith only [h1105, h952, hc12, hlam, hphi, ht01, u0ehi7]
                          · linarith only [h0, h1105, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h1108 | h1108
                      · linarith only [h1108, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1110 | h1110
                        · linarith only [h1099, h1110, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1112 | h1112
                          · linarith only [h0, h1112, h952, hc12, hlam, hphi, ht01, u0ehi6]
                          · linarith only [h0, h1112, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1115 | h1115
                    · linarith only [h1098, h1099, h1115, hlam]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h1117 | h1117
                      · linarith only [h1098, h1099, h1117, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht6b, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1119 | h1119
                        · linarith only [h1119, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1121 | h1121
                          · linarith only [h0, h1121, h952, hc12, hlam, hphi, ht01, u0ehi6]
                          · linarith only [h0, h1121, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1124 | h1124
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1125 | h1125
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h1126 | h1126
                      · linarith only [h1126, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1128 | h1128
                        · linarith only [h1124, h1128, hlam, hphi, ht0b, ht6b, u0elo2, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1130 | h1130
                          · linarith only [h0, h1130, h952, hc12, hlam, hphi, ht01, u0ehi6]
                          · linarith only [h0, h1130, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                    · linarith only [h1098, h1124, h1125, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1134 | h1134
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h1135 | h1135
                      · linarith only [h1135, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1137 | h1137
                        · linarith only [h1134, h1135, h1137, hc46, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht6b, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1139 | h1139
                          · linarith only [h0, h1139, h952, hc12, hlam, hphi, ht01, u0ehi6]
                          · linarith only [h0, h1139, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                    · rcases m.htr 0 4 6 (by decide) (by decide) with h1142 | h1142
                      · linarith only [h1142, hlam, hphi, ht0b, ht6b, u0elo3, u6ehi4]
                      · rcases m.htr 0 5 6 (by decide) (by decide) with h1144 | h1144
                        · linarith only [h1144, hlam, hphi, ht0b, ht6b, u0elo4, u6ehi5]
                        · rcases m.htr 1 2 3 (by decide) (by decide) with h1146 | h1146
                          · linarith only [h0, h1146, h952, hc12, hlam, hphi, ht01, u0ehi6]
                          · linarith only [h0, h1146, hc23, hlam, hphi, ht01, ht12, u0ehi6]

theorem n8l_sBT8_M_LR_M_IR (m : N8Model)
    (hb0 : CMSig2_8_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_M_IR m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht6b := m.ht6
  have hc16 := m.hcor 1 6 (by decide)
  have hc26 := m.hcor 2 6 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h6ehi := hb6.2.1
  have h6bigk := hb6.2.2.2
  have u0elo5 := h0elo (m.d 0 6) (by simp)
  have u0ehi11 := h0ehi (m.d 0 6) (by simp)
  have u6ehi1 := h6ehi (m.d 1 6) (by simp)
  have u6ehi2 := h6ehi (m.d 2 6) (by simp)
  have u6ehi3 := h6ehi (m.d 3 6) (by simp)
  have u6ehi4 := h6ehi (m.d 4 6) (by simp)
  have u6ehi5 := h6ehi (m.d 5 6) (by simp)
  rcases h6bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht6b, p0_1, u0elo5, u6ehi1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht6b, p0_1, u0elo5, u6ehi2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht6b, p0_1, u0elo5, u6ehi3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht6b, p0_1, u0elo5, u6ehi4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, hphi, ht0b, ht6b, p0_1, u0elo5, u6ehi5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, ht01, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h9 | h9
    · linarith only [h9, hlam, hphi, ht0b, ht6b, p0_1, u0elo5, u6ehi2]
    · linarith only [h9, hc16, hlam, hphi, ht01, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h12 | h12
    · linarith only [h12, hlam, hphi, ht0b, ht6b, p0_1, u0elo5, u6ehi3]
    · linarith only [h12, hc16, hlam, hphi, ht01, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h15 | h15
    · linarith only [h15, hlam, hphi, ht0b, ht6b, p0_1, u0elo5, u6ehi4]
    · linarith only [h15, hc16, hlam, hphi, ht01, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h18 | h18
    · linarith only [h18, hlam, hphi, ht0b, ht6b, p0_1, u0elo5, u6ehi5]
    · linarith only [h18, hc16, hlam, hphi, ht01, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc26, hlam, hphi, ht01, ht12, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h22 | h22
    · linarith only [h22, hlam, hphi, ht0b, ht6b, p0_1, u0elo5, u6ehi1]
    · linarith only [h22, hc26, hlam, hphi, ht01, ht12, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h26 | h26
    · linarith only [h26, hlam, hphi, ht0b, ht6b, p0_1, u0elo5, u6ehi3]
    · linarith only [h26, hc26, hlam, hphi, ht01, ht12, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h29 | h29
    · linarith only [h29, hlam, hphi, ht0b, ht6b, p0_1, u0elo5, u6ehi4]
    · linarith only [h29, hc26, hlam, hphi, ht01, ht12, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h32 | h32
    · linarith only [h32, hlam, hphi, ht0b, ht6b, p0_1, u0elo5, u6ehi5]
    · linarith only [h32, hc26, hlam, hphi, ht01, ht12, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc36, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h36 | h36
    · linarith only [h36, hlam, hphi, ht0b, ht6b, p0_1, u0elo5, u6ehi1]
    · linarith only [h36, hc36, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h39 | h39
    · linarith only [h39, hlam, hphi, ht0b, ht6b, p0_1, u0elo5, u6ehi2]
    · linarith only [h39, hc36, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h43 | h43
    · linarith only [h43, hlam, hphi, ht0b, ht6b, p0_1, u0elo5, u6ehi4]
    · linarith only [h43, hc36, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h46 | h46
    · linarith only [h46, hlam, hphi, ht0b, ht6b, p0_1, u0elo5, u6ehi5]
    · linarith only [h46, hc36, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc46, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h50 | h50
    · linarith only [h50, hlam, hphi, ht0b, ht6b, p0_1, u0elo5, u6ehi1]
    · linarith only [h50, hc46, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h53 | h53
    · linarith only [h53, hlam, hphi, ht0b, ht6b, p0_1, u0elo5, u6ehi2]
    · linarith only [h53, hc46, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h56 | h56
    · linarith only [h56, hlam, hphi, ht0b, ht6b, p0_1, u0elo5, u6ehi3]
    · linarith only [h56, hc46, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h60 | h60
    · linarith only [h60, hlam, hphi, ht0b, ht6b, p0_1, u0elo5, u6ehi5]
    · linarith only [h60, hc46, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h64 | h64
    · linarith only [h64, hlam, hphi, ht0b, ht6b, p0_1, u0elo5, u6ehi1]
    · linarith only [h64, hc56, hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h67 | h67
    · linarith only [h67, hlam, hphi, ht0b, ht6b, p0_1, u0elo5, u6ehi2]
    · linarith only [h67, hc56, hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h70 | h70
    · linarith only [h70, hlam, hphi, ht0b, ht6b, p0_1, u0elo5, u6ehi3]
    · linarith only [h70, hc56, hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    rcases p0_3 (m.d 0 6) (by simp) with h73 | h73
    · linarith only [h73, hlam, hphi, ht0b, ht6b, p0_1, u0elo5, u6ehi4]
    · linarith only [h73, hc56, hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

theorem n8l_sBT8_M_LR_M_LI (m : N8Model)
    (hb0 : CMSig2_8_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5) (m.d 0 6))
    (hb6 : CMSig2_8_M_LI m.lam m.p (m.t 6) (m.d 0 6) (m.d 1 6) (m.d 2 6) (m.d 3 6) (m.d 4 6) (m.d 5 6))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have hc16 := m.hcor 1 6 (by decide)
  have hc26 := m.hcor 2 6 (by decide)
  have hc36 := m.hcor 3 6 (by decide)
  have hc46 := m.hcor 4 6 (by decide)
  have hc56 := m.hcor 5 6 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.2.2.1
  have h6elo := hb6.1
  have h6bigk := hb6.2.2.2
  have u0ehi11 := h0ehi (m.d 0 6) (by simp)
  have u6elo0 := h6elo (m.d 0 6) (by simp)
  have u6elo1 := h6elo (m.d 1 6) (by simp)
  have u6elo2 := h6elo (m.d 2 6) (by simp)
  have u6elo3 := h6elo (m.d 3 6) (by simp)
  have u6elo4 := h6elo (m.d 4 6) (by simp)
  have u6elo5 := h6elo (m.d 5 6) (by simp)
  rcases h6bigk with h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c | h0c
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc26, hlam, hphi, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc36, hlam, hphi, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc46, hlam, hphi, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, p0_1, u6elo0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, ht01, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc26, hlam, hphi, p0_1, u6elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc36, hlam, hphi, p0_1, u6elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc46, hlam, hphi, p0_1, u6elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, p0_1, u6elo1]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc26, hlam, hphi, ht01, ht12, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u6elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc36, hlam, hphi, p0_1, u6elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc46, hlam, hphi, p0_1, u6elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, p0_1, u6elo2]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc36, hlam, hphi, ht01, ht12, ht23, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u6elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc26, hlam, hphi, p0_1, u6elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc46, hlam, hphi, p0_1, u6elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, p0_1, u6elo3]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc46, hlam, hphi, ht01, ht12, ht23, ht34, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u6elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc26, hlam, hphi, p0_1, u6elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc36, hlam, hphi, p0_1, u6elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, p0_1, u6elo4]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc56, hlam, hphi, ht01, ht12, ht23, ht34, ht45, p0_1, u0ehi11]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc16, hlam, hphi, p0_1, u6elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc26, hlam, hphi, p0_1, u6elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc36, hlam, hphi, p0_1, u6elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hc46, hlam, hphi, p0_1, u6elo5]
  · obtain ⟨p0_0, p0_1, p0_2, p0_3⟩ := h0c
    linarith only [hlam, p0_0]

end R2N4
