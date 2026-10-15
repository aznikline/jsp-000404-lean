import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7982000 in
set_option maxHeartbeats 7982000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s10_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg8410 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h10008 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h10009 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h10010 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h10011 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h10012 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10013 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h10014 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10015 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10016 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h10017 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h10018 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h10019 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h10020 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h8410 := hg8410
  rcases m.htr 2 3 5 (by decide) (by decide) with h10021 | h10021
  · rcases m.htr 2 4 5 (by decide) (by decide) with h10022 | h10022
    · rcases m.htr 3 4 5 (by decide) (by decide) with h10023 | h10023
      · rcases h2bigk with h10024c | h10024c | h10024c | h10024c | h10024c | h10024c | h10024c | h10024c | h10024c | h10024c | h10024c | h10024c | h10024c | h10024c | h10024c | h10024c | h10024c | h10024c | h10024c | h10024c | h10024c | h10024c | h10024c | h10024c | h10024c
        · have p10024_0 := h10024c.1
          have p10024_1 := h10024c.2.1
          have p10024_2 := h10024c.2.2.1
          have p10024_3 := h10024c.2.2.2
          linarith only [hlam, p10024_0]
        · have p10024_0 := h10024c.1
          have p10024_1 := h10024c.2.1
          have p10024_2 := h10024c.2.2.1
          have p10024_3 := h10024c.2.2.2
          linarith only [h0, hlam, p10024_1]
        · have p10024_0 := h10024c.1
          have p10024_1 := h10024c.2.1
          have p10024_2 := h10024c.2.2.1
          have p10024_3 := h10024c.2.2.2
          linarith only [h10020, h10023, hc02, hc45, hlam, hphi, ht0b, ht5b, p10024_1]
        · have p10024_0 := h10024c.1
          have p10024_1 := h10024c.2.1
          have p10024_2 := h10024c.2.2.1
          have p10024_3 := h10024c.2.2.2
          rcases p10024_3 (m.d 0 2) (by simp) with h10028 | h10028
          · rcases p10024_3 (m.d 1 2) (by simp) with h10029 | h10029
            · rcases p10024_3 (m.d 2 3) (by simp) with h10030 | h10030
              · linarith only [h10009, h10030, hlam]
              · linarith only [h10020, h10030, hlam]
            · linarith only [h0, h10029, hlam, p10024_1]
          · linarith only [h10028, hlam, p10024_0]
        · have p10024_0 := h10024c.1
          have p10024_1 := h10024c.2.1
          have p10024_2 := h10024c.2.2.1
          have p10024_3 := h10024c.2.2.2
          rcases p10024_3 (m.d 0 2) (by simp) with h10035 | h10035
          · rcases p10024_3 (m.d 1 2) (by simp) with h10036 | h10036
            · rcases p10024_3 (m.d 2 3) (by simp) with h10037 | h10037
              · linarith only [h10009, h10037, hlam]
              · linarith only [h10021, h10037, hlam]
            · linarith only [h10016, h10036, hlam]
          · linarith only [h10035, hlam, p10024_0]
        · have p10024_0 := h10024c.1
          have p10024_1 := h10024c.2.1
          have p10024_2 := h10024c.2.2.1
          have p10024_3 := h10024c.2.2.2
          linarith only [hc12, hlam, hphi, ht01, p10024_1, u0ehi1]
        · have p10024_0 := h10024c.1
          have p10024_1 := h10024c.2.1
          have p10024_2 := h10024c.2.2.1
          have p10024_3 := h10024c.2.2.2
          linarith only [hlam, p10024_0]
        · have p10024_0 := h10024c.1
          have p10024_1 := h10024c.2.1
          have p10024_2 := h10024c.2.2.1
          have p10024_3 := h10024c.2.2.2
          linarith only [h10020, h10023, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10024_1]
        · have p10024_0 := h10024c.1
          have p10024_1 := h10024c.2.1
          have p10024_2 := h10024c.2.2.1
          have p10024_3 := h10024c.2.2.2
          rcases p10024_3 (m.d 0 2) (by simp) with h10045 | h10045
          · linarith only [h0, h10045, hlam]
          · linarith only [h10010, h10045, hlam]
        · have p10024_0 := h10024c.1
          have p10024_1 := h10024c.2.1
          have p10024_2 := h10024c.2.2.1
          have p10024_3 := h10024c.2.2.2
          rcases p10024_3 (m.d 0 2) (by simp) with h10048 | h10048
          · linarith only [h0, h10048, hlam]
          · linarith only [h10011, h10048, hlam]
        · have p10024_0 := h10024c.1
          have p10024_1 := h10024c.2.1
          have p10024_2 := h10024c.2.2.1
          have p10024_3 := h10024c.2.2.2
          linarith only [h10009, hlam, p10024_0]
        · have p10024_0 := h10024c.1
          have p10024_1 := h10024c.2.1
          have p10024_2 := h10024c.2.2.1
          have p10024_3 := h10024c.2.2.2
          linarith only [h10015, hlam, p10024_0]
        · have p10024_0 := h10024c.1
          have p10024_1 := h10024c.2.1
          have p10024_2 := h10024c.2.2.1
          have p10024_3 := h10024c.2.2.2
          linarith only [hlam, p10024_0]
        · have p10024_0 := h10024c.1
          have p10024_1 := h10024c.2.1
          have p10024_2 := h10024c.2.2.1
          have p10024_3 := h10024c.2.2.2
          linarith only [h10009, h10020, h10023, hc02, hc45, hlam, hphi, ht0b, ht5b, p10024_1]
        · have p10024_0 := h10024c.1
          have p10024_1 := h10024c.2.1
          have p10024_2 := h10024c.2.2.1
          have p10024_3 := h10024c.2.2.2
          rcases p10024_3 (m.d 0 2) (by simp) with h10055 | h10055
          · rcases p10024_3 (m.d 1 2) (by simp) with h10056 | h10056
            · rcases p10024_3 (m.d 2 3) (by simp) with h10057 | h10057
              · rcases p10024_3 (m.d 2 4) (by simp) with h10058 | h10058
                · linarith only [h10020, h10058, hlam]
                · linarith only [h10022, h10058, hlam]
              · linarith only [h10021, h10057, hlam]
            · linarith only [h10016, h10056, hlam]
          · linarith only [h10011, h10055, hlam]
        · have p10024_0 := h10024c.1
          have p10024_1 := h10024c.2.1
          have p10024_2 := h10024c.2.2.1
          have p10024_3 := h10024c.2.2.2
          linarith only [h10010, hlam, p10024_0]
        · have p10024_0 := h10024c.1
          have p10024_1 := h10024c.2.1
          have p10024_2 := h10024c.2.2.1
          have p10024_3 := h10024c.2.2.2
          linarith only [h10015, h8410, hc01, hc24, hlam, hphi, ht12, p10024_1]
        · have p10024_0 := h10024c.1
          have p10024_1 := h10024c.2.1
          have p10024_2 := h10024c.2.2.1
          have p10024_3 := h10024c.2.2.2
          linarith only [h10020, hlam, p10024_1]
        · have p10024_0 := h10024c.1
          have p10024_1 := h10024c.2.1
          have p10024_2 := h10024c.2.2.1
          have p10024_3 := h10024c.2.2.2
          linarith only [hlam, p10024_0]
        · have p10024_0 := h10024c.1
          have p10024_1 := h10024c.2.1
          have p10024_2 := h10024c.2.2.1
          have p10024_3 := h10024c.2.2.2
          rcases p10024_3 (m.d 0 2) (by simp) with h10068 | h10068
          · rcases p10024_3 (m.d 1 2) (by simp) with h10069 | h10069
            · rcases p10024_3 (m.d 2 3) (by simp) with h10070 | h10070
              · rcases p10024_3 (m.d 2 4) (by simp) with h10071 | h10071
                · rcases p10024_3 (m.d 2 5) (by simp) with h10072 | h10072
                  · linarith only [h10022, h10072, hlam]
                  · rcases h3bigk with h10074c | h10074c | h10074c | h10074c | h10074c | h10074c | h10074c | h10074c | h10074c | h10074c | h10074c | h10074c | h10074c | h10074c | h10074c | h10074c | h10074c | h10074c | h10074c | h10074c | h10074c | h10074c | h10074c | h10074c | h10074c
                    · have p10074_0 := h10074c.1
                      have p10074_1 := h10074c.2.1
                      have p10074_2 := h10074c.2.2.1
                      have p10074_3 := h10074c.2.2.2
                      linarith only [hlam, p10074_0]
                    · have p10074_0 := h10074c.1
                      have p10074_1 := h10074c.2.1
                      have p10074_2 := h10074c.2.2.1
                      have p10074_3 := h10074c.2.2.2
                      linarith only [h8410, hlam, p10074_1]
                    · have p10074_0 := h10074c.1
                      have p10074_1 := h10074c.2.1
                      have p10074_2 := h10074c.2.2.1
                      have p10074_3 := h10074c.2.2.2
                      linarith only [h10020, hc03, hc25, hlam, hphi, ht0b, ht5b, p10024_1, p10074_1]
                    · have p10074_0 := h10074c.1
                      have p10074_1 := h10074c.2.1
                      have p10074_2 := h10074c.2.2.1
                      have p10074_3 := h10074c.2.2.2
                      rcases p10074_3 (m.d 0 3) (by simp) with h10078 | h10078
                      · rcases p10074_3 (m.d 1 3) (by simp) with h10079 | h10079
                        · rcases p10074_3 (m.d 2 3) (by simp) with h10080 | h10080
                          · linarith only [h10009, h10080, hlam]
                          · linarith only [h10020, h10080, hlam]
                        · linarith only [h10017, h10079, hlam]
                      · linarith only [h10078, hlam, p10074_0]
                    · have p10074_0 := h10074c.1
                      have p10074_1 := h10074c.2.1
                      have p10074_2 := h10074c.2.2.1
                      have p10074_3 := h10074c.2.2.2
                      rcases p10074_3 (m.d 0 3) (by simp) with h10085 | h10085
                      · rcases p10074_3 (m.d 1 3) (by simp) with h10086 | h10086
                        · rcases p10074_3 (m.d 2 3) (by simp) with h10087 | h10087
                          · linarith only [h10009, h10087, hlam]
                          · linarith only [h10021, h10087, hlam]
                        · linarith only [h10018, h10086, hlam]
                      · linarith only [h10085, hlam, p10074_0]
                    · have p10074_0 := h10074c.1
                      have p10074_1 := h10074c.2.1
                      have p10074_2 := h10074c.2.2.1
                      have p10074_3 := h10074c.2.2.2
                      linarith only [h10015, hc12, hlam, hphi, ht01, p10074_1, u0ehi2]
                    · have p10074_0 := h10074c.1
                      have p10074_1 := h10074c.2.1
                      have p10074_2 := h10074c.2.2.1
                      have p10074_3 := h10074c.2.2.2
                      linarith only [hlam, p10074_0]
                    · have p10074_0 := h10074c.1
                      have p10074_1 := h10074c.2.1
                      have p10074_2 := h10074c.2.2.1
                      have p10074_3 := h10074c.2.2.2
                      linarith only [h10015, h10020, h10021, h10023, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10024_1, p10074_1]
                    · have p10074_0 := h10074c.1
                      have p10074_1 := h10074c.2.1
                      have p10074_2 := h10074c.2.2.1
                      have p10074_3 := h10074c.2.2.2
                      rcases p10074_3 (m.d 0 3) (by simp) with h10095 | h10095
                      · linarith only [h10095, h8410, hlam]
                      · linarith only [h10012, h10095, hlam]
                    · have p10074_0 := h10074c.1
                      have p10074_1 := h10074c.2.1
                      have p10074_2 := h10074c.2.2.1
                      have p10074_3 := h10074c.2.2.2
                      rcases p10074_3 (m.d 0 3) (by simp) with h10098 | h10098
                      · linarith only [h10098, h8410, hlam]
                      · linarith only [h10013, h10098, hlam]
                    · have p10074_0 := h10074c.1
                      have p10074_1 := h10074c.2.1
                      have p10074_2 := h10074c.2.2.1
                      have p10074_3 := h10074c.2.2.2
                      linarith only [h10009, hlam, p10074_0]
                    · have p10074_0 := h10074c.1
                      have p10074_1 := h10074c.2.1
                      have p10074_2 := h10074c.2.2.1
                      have p10074_3 := h10074c.2.2.2
                      linarith only [h10015, hlam, p10074_0]
                    · have p10074_0 := h10074c.1
                      have p10074_1 := h10074c.2.1
                      have p10074_2 := h10074c.2.2.1
                      have p10074_3 := h10074c.2.2.2
                      linarith only [hlam, p10074_0]
                    · have p10074_0 := h10074c.1
                      have p10074_1 := h10074c.2.1
                      have p10074_2 := h10074c.2.2.1
                      have p10074_3 := h10074c.2.2.2
                      linarith only [h0, h10009, h10023, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10074_1]
                    · have p10074_0 := h10074c.1
                      have p10074_1 := h10074c.2.1
                      have p10074_2 := h10074c.2.2.1
                      have p10074_3 := h10074c.2.2.2
                      rcases p10074_3 (m.d 0 3) (by simp) with h10105 | h10105
                      · rcases p10074_3 (m.d 1 3) (by simp) with h10106 | h10106
                        · rcases p10074_3 (m.d 2 3) (by simp) with h10107 | h10107
                          · rcases p10074_3 (m.d 3 4) (by simp) with h10108 | h10108
                            · linarith only [h10020, h10108, hlam]
                            · linarith only [h10023, h10108, hlam]
                          · linarith only [h10107, hlam, p10074_0]
                        · linarith only [h10018, h10106, hlam]
                      · linarith only [h10013, h10105, hlam]
                    · have p10074_0 := h10074c.1
                      have p10074_1 := h10074c.2.1
                      have p10074_2 := h10074c.2.2.1
                      have p10074_3 := h10074c.2.2.2
                      linarith only [h10012, hlam, p10074_0]
                    · have p10074_0 := h10074c.1
                      have p10074_1 := h10074c.2.1
                      have p10074_2 := h10074c.2.2.1
                      have p10074_3 := h10074c.2.2.2
                      linarith only [h10017, hlam, p10074_0]
                    · have p10074_0 := h10074c.1
                      have p10074_1 := h10074c.2.1
                      have p10074_2 := h10074c.2.2.1
                      have p10074_3 := h10074c.2.2.2
                      linarith only [h10020, hlam, p10074_0]
                    · have p10074_0 := h10074c.1
                      have p10074_1 := h10074c.2.1
                      have p10074_2 := h10074c.2.2.1
                      have p10074_3 := h10074c.2.2.2
                      linarith only [hlam, p10074_0]
                    · have p10074_0 := h10074c.1
                      have p10074_1 := h10074c.2.1
                      have p10074_2 := h10074c.2.2.1
                      have p10074_3 := h10074c.2.2.2
                      linarith only [h0, h10009, h10020, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p10074_1]
                    · have p10074_0 := h10074c.1
                      have p10074_1 := h10074c.2.1
                      have p10074_2 := h10074c.2.2.1
                      have p10074_3 := h10074c.2.2.2
                      linarith only [h10013, hlam, p10074_0]
                    · have p10074_0 := h10074c.1
                      have p10074_1 := h10074c.2.1
                      have p10074_2 := h10074c.2.2.1
                      have p10074_3 := h10074c.2.2.2
                      linarith only [h10018, hlam, p10074_0]
                    · have p10074_0 := h10074c.1
                      have p10074_1 := h10074c.2.1
                      have p10074_2 := h10074c.2.2.1
                      have p10074_3 := h10074c.2.2.2
                      linarith only [h10021, hlam, p10074_0]
                    · have p10074_0 := h10074c.1
                      have p10074_1 := h10074c.2.1
                      have p10074_2 := h10074c.2.2.1
                      have p10074_3 := h10074c.2.2.2
                      linarith only [h10023, hlam, p10074_0]
                    · have p10074_0 := h10074c.1
                      have p10074_1 := h10074c.2.1
                      have p10074_2 := h10074c.2.2.1
                      have p10074_3 := h10074c.2.2.2
                      linarith only [hlam, p10074_0]
                · linarith only [h10022, h10071, hlam]
              · linarith only [h10021, h10070, hlam]
            · linarith only [h10016, h10069, hlam]
          · linarith only [h10011, h10068, hlam]
        · have p10024_0 := h10024c.1
          have p10024_1 := h10024c.2.1
          have p10024_2 := h10024c.2.2.1
          have p10024_3 := h10024c.2.2.2
          linarith only [h10011, hlam, p10024_0]
        · have p10024_0 := h10024c.1
          have p10024_1 := h10024c.2.1
          have p10024_2 := h10024c.2.2.1
          have p10024_3 := h10024c.2.2.2
          linarith only [h10016, hlam, p10024_0]
        · have p10024_0 := h10024c.1
          have p10024_1 := h10024c.2.1
          have p10024_2 := h10024c.2.2.1
          have p10024_3 := h10024c.2.2.2
          linarith only [h10021, hlam, p10024_1]
        · have p10024_0 := h10024c.1
          have p10024_1 := h10024c.2.1
          have p10024_2 := h10024c.2.2.1
          have p10024_3 := h10024c.2.2.2
          linarith only [h10022, hlam, p10024_0]
        · have p10024_0 := h10024c.1
          have p10024_1 := h10024c.2.1
          have p10024_2 := h10024c.2.2.1
          have p10024_3 := h10024c.2.2.2
          linarith only [hlam, p10024_0]
      · rcases h2bigk with h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c | h10133c
        · have p10133_0 := h10133c.1
          have p10133_1 := h10133c.2.1
          have p10133_2 := h10133c.2.2.1
          have p10133_3 := h10133c.2.2.2
          linarith only [hlam, p10133_0]
        · have p10133_0 := h10133c.1
          have p10133_1 := h10133c.2.1
          have p10133_2 := h10133c.2.2.1
          have p10133_3 := h10133c.2.2.2
          linarith only [h0, hlam, p10133_1]
        · have p10133_0 := h10133c.1
          have p10133_1 := h10133c.2.1
          have p10133_2 := h10133c.2.2.1
          have p10133_3 := h10133c.2.2.2
          linarith only [h0, h10020, h10022, h10023, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10133_1]
        · have p10133_0 := h10133c.1
          have p10133_1 := h10133c.2.1
          have p10133_2 := h10133c.2.2.1
          have p10133_3 := h10133c.2.2.2
          linarith only [h0, h10022, h10023, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10133_1]
        · have p10133_0 := h10133c.1
          have p10133_1 := h10133c.2.1
          have p10133_2 := h10133c.2.2.1
          have p10133_3 := h10133c.2.2.2
          rcases p10133_3 (m.d 0 2) (by simp) with h10138 | h10138
          · rcases p10133_3 (m.d 1 2) (by simp) with h10139 | h10139
            · rcases p10133_3 (m.d 2 3) (by simp) with h10140 | h10140
              · linarith only [h10009, h10140, hlam]
              · linarith only [h10021, h10140, hlam]
            · linarith only [h10016, h10139, hlam]
          · linarith only [h10138, hlam, p10133_0]
        · have p10133_0 := h10133c.1
          have p10133_1 := h10133c.2.1
          have p10133_2 := h10133c.2.2.1
          have p10133_3 := h10133c.2.2.2
          linarith only [hc12, hlam, hphi, ht01, p10133_1, u0ehi1]
        · have p10133_0 := h10133c.1
          have p10133_1 := h10133c.2.1
          have p10133_2 := h10133c.2.2.1
          have p10133_3 := h10133c.2.2.2
          linarith only [hlam, p10133_0]
        · have p10133_0 := h10133c.1
          have p10133_1 := h10133c.2.1
          have p10133_2 := h10133c.2.2.1
          have p10133_3 := h10133c.2.2.2
          linarith only [h10020, h10022, h10023, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10133_1]
        · have p10133_0 := h10133c.1
          have p10133_1 := h10133c.2.1
          have p10133_2 := h10133c.2.2.1
          have p10133_3 := h10133c.2.2.2
          linarith only [h10022, h10023, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10133_1]
        · have p10133_0 := h10133c.1
          have p10133_1 := h10133c.2.1
          have p10133_2 := h10133c.2.2.1
          have p10133_3 := h10133c.2.2.2
          rcases p10133_3 (m.d 0 2) (by simp) with h10149 | h10149
          · linarith only [h0, h10149, hlam]
          · linarith only [h10011, h10149, hlam]
        · have p10133_0 := h10133c.1
          have p10133_1 := h10133c.2.1
          have p10133_2 := h10133c.2.2.1
          have p10133_3 := h10133c.2.2.2
          linarith only [h10009, hlam, p10133_0]
        · have p10133_0 := h10133c.1
          have p10133_1 := h10133c.2.1
          have p10133_2 := h10133c.2.2.1
          have p10133_3 := h10133c.2.2.2
          linarith only [h10015, hlam, p10133_0]
        · have p10133_0 := h10133c.1
          have p10133_1 := h10133c.2.1
          have p10133_2 := h10133c.2.2.1
          have p10133_3 := h10133c.2.2.2
          linarith only [hlam, p10133_0]
        · have p10133_0 := h10133c.1
          have p10133_1 := h10133c.2.1
          have p10133_2 := h10133c.2.2.1
          have p10133_3 := h10133c.2.2.2
          linarith only [h10009, h10022, h10023, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p10133_1]
        · have p10133_0 := h10133c.1
          have p10133_1 := h10133c.2.1
          have p10133_2 := h10133c.2.2.1
          have p10133_3 := h10133c.2.2.2
          linarith only [h0, h10009, h10022, h10023, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10133_1]
        · have p10133_0 := h10133c.1
          have p10133_1 := h10133c.2.1
          have p10133_2 := h10133c.2.2.1
          have p10133_3 := h10133c.2.2.2
          linarith only [h10010, hlam, p10133_0]
        · have p10133_0 := h10133c.1
          have p10133_1 := h10133c.2.1
          have p10133_2 := h10133c.2.2.1
          have p10133_3 := h10133c.2.2.2
          linarith only [h10008, h10010, h10015, h8410, hc04, hc15, hlam, hphi, ht0b, ht5b, p10133_1]
        · have p10133_0 := h10133c.1
          have p10133_1 := h10133c.2.1
          have p10133_2 := h10133c.2.2.1
          have p10133_3 := h10133c.2.2.2
          linarith only [h10020, hlam, p10133_1]
        · have p10133_0 := h10133c.1
          have p10133_1 := h10133c.2.1
          have p10133_2 := h10133c.2.2.1
          have p10133_3 := h10133c.2.2.2
          linarith only [hlam, p10133_0]
        · have p10133_0 := h10133c.1
          have p10133_1 := h10133c.2.1
          have p10133_2 := h10133c.2.2.1
          have p10133_3 := h10133c.2.2.2
          linarith only [h10010, h10022, h10023, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p10133_1]
        · have p10133_0 := h10133c.1
          have p10133_1 := h10133c.2.1
          have p10133_2 := h10133c.2.2.1
          have p10133_3 := h10133c.2.2.2
          linarith only [h10011, hlam, p10133_0]
        · have p10133_0 := h10133c.1
          have p10133_1 := h10133c.2.1
          have p10133_2 := h10133c.2.2.1
          have p10133_3 := h10133c.2.2.2
          linarith only [h10016, hlam, p10133_0]
        · have p10133_0 := h10133c.1
          have p10133_1 := h10133c.2.1
          have p10133_2 := h10133c.2.2.1
          have p10133_3 := h10133c.2.2.2
          linarith only [h10021, hlam, p10133_1]
        · have p10133_0 := h10133c.1
          have p10133_1 := h10133c.2.1
          have p10133_2 := h10133c.2.2.1
          have p10133_3 := h10133c.2.2.2
          linarith only [h10022, hlam, p10133_0]
        · have p10133_0 := h10133c.1
          have p10133_1 := h10133c.2.1
          have p10133_2 := h10133c.2.2.1
          have p10133_3 := h10133c.2.2.2
          linarith only [hlam, p10133_0]
    · rcases m.htr 3 4 5 (by decide) (by decide) with h10167 | h10167
      · linarith only [h10020, h10022, h10167, hlam]
      · rcases h2bigk with h10169c | h10169c | h10169c | h10169c | h10169c | h10169c | h10169c | h10169c | h10169c | h10169c | h10169c | h10169c | h10169c | h10169c | h10169c | h10169c | h10169c | h10169c | h10169c | h10169c | h10169c | h10169c | h10169c | h10169c | h10169c
        · have p10169_0 := h10169c.1
          have p10169_1 := h10169c.2.1
          have p10169_2 := h10169c.2.2.1
          have p10169_3 := h10169c.2.2.2
          linarith only [hlam, p10169_0]
        · have p10169_0 := h10169c.1
          have p10169_1 := h10169c.2.1
          have p10169_2 := h10169c.2.2.1
          have p10169_3 := h10169c.2.2.2
          linarith only [h0, hlam, p10169_1]
        · have p10169_0 := h10169c.1
          have p10169_1 := h10169c.2.1
          have p10169_2 := h10169c.2.2.1
          have p10169_3 := h10169c.2.2.2
          rcases p10169_3 (m.d 0 2) (by simp) with h10172 | h10172
          · rcases p10169_3 (m.d 1 2) (by simp) with h10173 | h10173
            · rcases p10169_3 (m.d 2 3) (by simp) with h10174 | h10174
              · linarith only [h10174, hlam, p10169_0]
              · rcases p10169_3 (m.d 2 4) (by simp) with h10176 | h10176
                · linarith only [h10010, h10176, hlam]
                · rcases p10169_3 (m.d 2 5) (by simp) with h10178 | h10178
                  · linarith only [h10011, h10178, hlam]
                  · rcases h3bigk with h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c | h10180c
                    · have p10180_0 := h10180c.1
                      have p10180_1 := h10180c.2.1
                      have p10180_2 := h10180c.2.2.1
                      have p10180_3 := h10180c.2.2.2
                      linarith only [hlam, p10180_0]
                    · have p10180_0 := h10180c.1
                      have p10180_1 := h10180c.2.1
                      have p10180_2 := h10180c.2.2.1
                      have p10180_3 := h10180c.2.2.2
                      linarith only [h8410, hlam, p10180_1]
                    · have p10180_0 := h10180c.1
                      have p10180_1 := h10180c.2.1
                      have p10180_2 := h10180c.2.2.1
                      have p10180_3 := h10180c.2.2.2
                      rcases p10180_3 (m.d 0 3) (by simp) with h10183 | h10183
                      · rcases p10180_3 (m.d 1 3) (by simp) with h10184 | h10184
                        · rcases p10180_3 (m.d 2 3) (by simp) with h10185 | h10185
                          · linarith only [h10009, h10185, hlam]
                          · rcases p10180_3 (m.d 3 4) (by simp) with h10187 | h10187
                            · linarith only [h10012, h10187, hlam]
                            · rcases p10180_3 (m.d 3 5) (by simp) with h10189 | h10189
                              · linarith only [h10013, h10189, hlam]
                              · rcases h5bigk with h10191c | h10191c | h10191c | h10191c | h10191c | h10191c | h10191c | h10191c | h10191c | h10191c | h10191c | h10191c | h10191c | h10191c | h10191c | h10191c | h10191c | h10191c | h10191c | h10191c | h10191c | h10191c | h10191c | h10191c | h10191c
                                · have p10191_0 := h10191c.1
                                  have p10191_1 := h10191c.2.1
                                  have p10191_2 := h10191c.2.2.1
                                  have p10191_3 := h10191c.2.2.2
                                  linarith only [hlam, p10191_0]
                                · have p10191_0 := h10191c.1
                                  have p10191_1 := h10191c.2.1
                                  have p10191_2 := h10191c.2.2.1
                                  have p10191_3 := h10191c.2.2.2
                                  linarith only [h10008, h10015, h8410, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p10191_1]
                                · have p10191_0 := h10191c.1
                                  have p10191_1 := h10191c.2.1
                                  have p10191_2 := h10191c.2.2.1
                                  have p10191_3 := h10191c.2.2.2
                                  linarith only [h10008, h10015, h8410, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p10191_1]
                                · have p10191_0 := h10191c.1
                                  have p10191_1 := h10191c.2.1
                                  have p10191_2 := h10191c.2.2.1
                                  have p10191_3 := h10191c.2.2.2
                                  linarith only [h10008, h10015, h10167, h8410, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10191_1]
                                · have p10191_0 := h10191c.1
                                  have p10191_1 := h10191c.2.1
                                  have p10191_2 := h10191c.2.2.1
                                  have p10191_3 := h10191c.2.2.2
                                  linarith only [h10008, h10015, h10020, h10022, h8410, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10191_1]
                                · have p10191_0 := h10191c.1
                                  have p10191_1 := h10191c.2.1
                                  have p10191_2 := h10191c.2.2.1
                                  have p10191_3 := h10191c.2.2.2
                                  linarith only [h10008, hlam, p10191_0]
                                · have p10191_0 := h10191c.1
                                  have p10191_1 := h10191c.2.1
                                  have p10191_2 := h10191c.2.2.1
                                  have p10191_3 := h10191c.2.2.2
                                  linarith only [hlam, p10191_0]
                                · have p10191_0 := h10191c.1
                                  have p10191_1 := h10191c.2.1
                                  have p10191_2 := h10191c.2.2.1
                                  have p10191_3 := h10191c.2.2.2
                                  linarith only [h10008, h10015, h8410, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p10191_1]
                                · have p10191_0 := h10191c.1
                                  have p10191_1 := h10191c.2.1
                                  have p10191_2 := h10191c.2.2.1
                                  have p10191_3 := h10191c.2.2.2
                                  linarith only [h10008, h10015, h10167, h8410, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10191_1]
                                · have p10191_0 := h10191c.1
                                  have p10191_1 := h10191c.2.1
                                  have p10191_2 := h10191c.2.2.1
                                  have p10191_3 := h10191c.2.2.2
                                  linarith only [h10008, h10015, h10020, h10022, h8410, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10191_1]
                                · have p10191_0 := h10191c.1
                                  have p10191_1 := h10191c.2.1
                                  have p10191_2 := h10191c.2.2.1
                                  have p10191_3 := h10191c.2.2.2
                                  linarith only [h10011, hlam, p10191_1]
                                · have p10191_0 := h10191c.1
                                  have p10191_1 := h10191c.2.1
                                  have p10191_2 := h10191c.2.2.1
                                  have p10191_3 := h10191c.2.2.2
                                  linarith only [h10016, hlam, p10191_1]
                                · have p10191_0 := h10191c.1
                                  have p10191_1 := h10191c.2.1
                                  have p10191_2 := h10191c.2.2.1
                                  have p10191_3 := h10191c.2.2.2
                                  linarith only [hlam, p10191_0]
                                · have p10191_0 := h10191c.1
                                  have p10191_1 := h10191c.2.1
                                  have p10191_2 := h10191c.2.2.1
                                  have p10191_3 := h10191c.2.2.2
                                  linarith only [h0, h10011, h10167, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10191_1]
                                · have p10191_0 := h10191c.1
                                  have p10191_1 := h10191c.2.1
                                  have p10191_2 := h10191c.2.2.1
                                  have p10191_3 := h10191c.2.2.2
                                  linarith only [h10022, hlam, p10191_1]
                                · have p10191_0 := h10191c.1
                                  have p10191_1 := h10191c.2.1
                                  have p10191_2 := h10191c.2.2.1
                                  have p10191_3 := h10191c.2.2.2
                                  linarith only [h10013, hlam, p10191_0]
                                · have p10191_0 := h10191c.1
                                  have p10191_1 := h10191c.2.1
                                  have p10191_2 := h10191c.2.2.1
                                  have p10191_3 := h10191c.2.2.2
                                  linarith only [h10018, hlam, p10191_0]
                                · have p10191_0 := h10191c.1
                                  have p10191_1 := h10191c.2.1
                                  have p10191_2 := h10191c.2.2.1
                                  have p10191_3 := h10191c.2.2.2
                                  linarith only [h10021, hlam, p10191_0]
                                · have p10191_0 := h10191c.1
                                  have p10191_1 := h10191c.2.1
                                  have p10191_2 := h10191c.2.2.1
                                  have p10191_3 := h10191c.2.2.2
                                  linarith only [hlam, p10191_0]
                                · have p10191_0 := h10191c.1
                                  have p10191_1 := h10191c.2.1
                                  have p10191_2 := h10191c.2.2.1
                                  have p10191_3 := h10191c.2.2.2
                                  linarith only [h10167, hlam, p10191_1]
                                · have p10191_0 := h10191c.1
                                  have p10191_1 := h10191c.2.1
                                  have p10191_2 := h10191c.2.2.1
                                  have p10191_3 := h10191c.2.2.2
                                  linarith only [h10014, hlam, p10191_0]
                                · have p10191_0 := h10191c.1
                                  have p10191_1 := h10191c.2.1
                                  have p10191_2 := h10191c.2.2.1
                                  have p10191_3 := h10191c.2.2.2
                                  linarith only [h10019, hlam, p10191_0]
                                · have p10191_0 := h10191c.1
                                  have p10191_1 := h10191c.2.1
                                  have p10191_2 := h10191c.2.2.1
                                  have p10191_3 := h10191c.2.2.2
                                  linarith only [h10019, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b, p10191_1]
                                · have p10191_0 := h10191c.1
                                  have p10191_1 := h10191c.2.1
                                  have p10191_2 := h10191c.2.2.1
                                  have p10191_3 := h10191c.2.2.2
                                  linarith only [h10008, h10015, h10019, h10167, h8410, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10191_1]
                                · have p10191_0 := h10191c.1
                                  have p10191_1 := h10191c.2.1
                                  have p10191_2 := h10191c.2.2.1
                                  have p10191_3 := h10191c.2.2.2
                                  linarith only [hlam, p10191_0]
                        · linarith only [h10015, h10184, hlam]
                      · linarith only [h10009, h10183, hlam]
                    · have p10180_0 := h10180c.1
                      have p10180_1 := h10180c.2.1
                      have p10180_2 := h10180c.2.2.1
                      have p10180_3 := h10180c.2.2.2
                      rcases p10180_3 (m.d 0 3) (by simp) with h10219 | h10219
                      · rcases p10180_3 (m.d 1 3) (by simp) with h10220 | h10220
                        · rcases p10180_3 (m.d 2 3) (by simp) with h10221 | h10221
                          · linarith only [h10009, h10221, hlam]
                          · linarith only [h10020, h10221, hlam]
                        · linarith only [h10017, h10220, hlam]
                      · linarith only [h10219, hlam, p10180_0]
                    · have p10180_0 := h10180c.1
                      have p10180_1 := h10180c.2.1
                      have p10180_2 := h10180c.2.2.1
                      have p10180_3 := h10180c.2.2.2
                      rcases p10180_3 (m.d 0 3) (by simp) with h10226 | h10226
                      · rcases p10180_3 (m.d 1 3) (by simp) with h10227 | h10227
                        · rcases p10180_3 (m.d 2 3) (by simp) with h10228 | h10228
                          · linarith only [h10009, h10228, hlam]
                          · linarith only [h10021, h10228, hlam]
                        · linarith only [h10018, h10227, hlam]
                      · linarith only [h10226, hlam, p10180_0]
                    · have p10180_0 := h10180c.1
                      have p10180_1 := h10180c.2.1
                      have p10180_2 := h10180c.2.2.1
                      have p10180_3 := h10180c.2.2.2
                      linarith only [h10015, hc12, hlam, hphi, ht01, p10180_1, u0ehi2]
                    · have p10180_0 := h10180c.1
                      have p10180_1 := h10180c.2.1
                      have p10180_2 := h10180c.2.2.1
                      have p10180_3 := h10180c.2.2.2
                      linarith only [hlam, p10180_0]
                    · have p10180_0 := h10180c.1
                      have p10180_1 := h10180c.2.1
                      have p10180_2 := h10180c.2.2.1
                      have p10180_3 := h10180c.2.2.2
                      rcases p10180_3 (m.d 0 3) (by simp) with h10235 | h10235
                      · linarith only [h10235, h8410, hlam]
                      · linarith only [h10009, h10235, hlam]
                    · have p10180_0 := h10180c.1
                      have p10180_1 := h10180c.2.1
                      have p10180_2 := h10180c.2.2.1
                      have p10180_3 := h10180c.2.2.2
                      linarith only [h10008, h10019, h10020, h10022, h8410, hlam, p10180_2]
                    · have p10180_0 := h10180c.1
                      have p10180_1 := h10180c.2.1
                      have p10180_2 := h10180c.2.2.1
                      have p10180_3 := h10180c.2.2.2
                      rcases p10180_3 (m.d 0 3) (by simp) with h10239 | h10239
                      · linarith only [h10239, h8410, hlam]
                      · linarith only [h10013, h10239, hlam]
                    · have p10180_0 := h10180c.1
                      have p10180_1 := h10180c.2.1
                      have p10180_2 := h10180c.2.2.1
                      have p10180_3 := h10180c.2.2.2
                      linarith only [h10009, hlam, p10180_0]
                    · have p10180_0 := h10180c.1
                      have p10180_1 := h10180c.2.1
                      have p10180_2 := h10180c.2.2.1
                      have p10180_3 := h10180c.2.2.2
                      linarith only [h10015, hlam, p10180_0]
                    · have p10180_0 := h10180c.1
                      have p10180_1 := h10180c.2.1
                      have p10180_2 := h10180c.2.2.1
                      have p10180_3 := h10180c.2.2.2
                      linarith only [hlam, p10180_0]
                    · have p10180_0 := h10180c.1
                      have p10180_1 := h10180c.2.1
                      have p10180_2 := h10180c.2.2.1
                      have p10180_3 := h10180c.2.2.2
                      linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10169_1, p10180_1]
                    · have p10180_0 := h10180c.1
                      have p10180_1 := h10180c.2.1
                      have p10180_2 := h10180c.2.2.1
                      have p10180_3 := h10180c.2.2.2
                      linarith only [h0, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p10169_1, p10180_1]
                    · have p10180_0 := h10180c.1
                      have p10180_1 := h10180c.2.1
                      have p10180_2 := h10180c.2.2.1
                      have p10180_3 := h10180c.2.2.2
                      linarith only [h10012, hlam, p10180_0]
                    · have p10180_0 := h10180c.1
                      have p10180_1 := h10180c.2.1
                      have p10180_2 := h10180c.2.2.1
                      have p10180_3 := h10180c.2.2.2
                      linarith only [h10017, hlam, p10180_0]
                    · have p10180_0 := h10180c.1
                      have p10180_1 := h10180c.2.1
                      have p10180_2 := h10180c.2.2.1
                      have p10180_3 := h10180c.2.2.2
                      linarith only [h10020, hlam, p10180_0]
                    · have p10180_0 := h10180c.1
                      have p10180_1 := h10180c.2.1
                      have p10180_2 := h10180c.2.2.1
                      have p10180_3 := h10180c.2.2.2
                      linarith only [hlam, p10180_0]
                    · have p10180_0 := h10180c.1
                      have p10180_1 := h10180c.2.1
                      have p10180_2 := h10180c.2.2.1
                      have p10180_3 := h10180c.2.2.2
                      linarith only [h10167, hlam, p10180_1]
                    · have p10180_0 := h10180c.1
                      have p10180_1 := h10180c.2.1
                      have p10180_2 := h10180c.2.2.1
                      have p10180_3 := h10180c.2.2.2
                      linarith only [h10013, hlam, p10180_0]
                    · have p10180_0 := h10180c.1
                      have p10180_1 := h10180c.2.1
                      have p10180_2 := h10180c.2.2.1
                      have p10180_3 := h10180c.2.2.2
                      linarith only [h10018, hlam, p10180_0]
                    · have p10180_0 := h10180c.1
                      have p10180_1 := h10180c.2.1
                      have p10180_2 := h10180c.2.2.1
                      have p10180_3 := h10180c.2.2.2
                      linarith only [h10021, hlam, p10180_0]
                    · have p10180_0 := h10180c.1
                      have p10180_1 := h10180c.2.1
                      have p10180_2 := h10180c.2.2.1
                      have p10180_3 := h10180c.2.2.2
                      linarith only [h10008, h10018, h8410, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10180_1]
                    · have p10180_0 := h10180c.1
                      have p10180_1 := h10180c.2.1
                      have p10180_2 := h10180c.2.2.1
                      have p10180_3 := h10180c.2.2.2
                      linarith only [hlam, p10180_0]
            · linarith only [h10015, h10173, hlam]
          · linarith only [h10172, hlam, p10169_0]
        · have p10169_0 := h10169c.1
          have p10169_1 := h10169c.2.1
          have p10169_2 := h10169c.2.2.1
          have p10169_3 := h10169c.2.2.2
          rcases p10169_3 (m.d 0 2) (by simp) with h10259 | h10259
          · rcases p10169_3 (m.d 1 2) (by simp) with h10260 | h10260
            · rcases p10169_3 (m.d 2 3) (by simp) with h10261 | h10261
              · linarith only [h10009, h10261, hlam]
              · linarith only [h10020, h10261, hlam]
            · linarith only [h0, h10260, hlam, p10169_1]
          · linarith only [h10259, hlam, p10169_0]
        · have p10169_0 := h10169c.1
          have p10169_1 := h10169c.2.1
          have p10169_2 := h10169c.2.2.1
          have p10169_3 := h10169c.2.2.2
          rcases p10169_3 (m.d 0 2) (by simp) with h10266 | h10266
          · rcases p10169_3 (m.d 1 2) (by simp) with h10267 | h10267
            · rcases p10169_3 (m.d 2 3) (by simp) with h10268 | h10268
              · linarith only [h10009, h10268, hlam]
              · linarith only [h10021, h10268, hlam]
            · linarith only [h10016, h10267, hlam]
          · linarith only [h10266, hlam, p10169_0]
        · have p10169_0 := h10169c.1
          have p10169_1 := h10169c.2.1
          have p10169_2 := h10169c.2.2.1
          have p10169_3 := h10169c.2.2.2
          linarith only [hc12, hlam, hphi, ht01, p10169_1, u0ehi1]
        · have p10169_0 := h10169c.1
          have p10169_1 := h10169c.2.1
          have p10169_2 := h10169c.2.2.1
          have p10169_3 := h10169c.2.2.2
          linarith only [hlam, p10169_0]
        · have p10169_0 := h10169c.1
          have p10169_1 := h10169c.2.1
          have p10169_2 := h10169c.2.2.1
          have p10169_3 := h10169c.2.2.2
          rcases p10169_3 (m.d 0 2) (by simp) with h10275 | h10275
          · linarith only [h0, h10275, hlam]
          · linarith only [h10009, h10275, hlam]
        · have p10169_0 := h10169c.1
          have p10169_1 := h10169c.2.1
          have p10169_2 := h10169c.2.2.1
          have p10169_3 := h10169c.2.2.2
          linarith only [h10008, h10015, h10019, h10022, h8410, hlam, p10169_2]
        · have p10169_0 := h10169c.1
          have p10169_1 := h10169c.2.1
          have p10169_2 := h10169c.2.2.1
          have p10169_3 := h10169c.2.2.2
          rcases p10169_3 (m.d 0 2) (by simp) with h10279 | h10279
          · linarith only [h0, h10279, hlam]
          · linarith only [h10011, h10279, hlam]
        · have p10169_0 := h10169c.1
          have p10169_1 := h10169c.2.1
          have p10169_2 := h10169c.2.2.1
          have p10169_3 := h10169c.2.2.2
          linarith only [h10009, hlam, p10169_0]
        · have p10169_0 := h10169c.1
          have p10169_1 := h10169c.2.1
          have p10169_2 := h10169c.2.2.1
          have p10169_3 := h10169c.2.2.2
          linarith only [h10015, hlam, p10169_0]
        · have p10169_0 := h10169c.1
          have p10169_1 := h10169c.2.1
          have p10169_2 := h10169c.2.2.1
          have p10169_3 := h10169c.2.2.2
          linarith only [hlam, p10169_0]
        · have p10169_0 := h10169c.1
          have p10169_1 := h10169c.2.1
          have p10169_2 := h10169c.2.2.1
          have p10169_3 := h10169c.2.2.2
          rcases p10169_3 (m.d 0 2) (by simp) with h10285 | h10285
          · rcases p10169_3 (m.d 1 2) (by simp) with h10286 | h10286
            · rcases p10169_3 (m.d 2 3) (by simp) with h10287 | h10287
              · rcases p10169_3 (m.d 2 4) (by simp) with h10288 | h10288
                · linarith only [h10020, h10288, hlam]
                · rcases p10169_3 (m.d 2 5) (by simp) with h10290 | h10290
                  · linarith only [h10021, h10290, hlam]
                  · linarith only [h10022, h10290, hlam]
              · linarith only [h10020, h10287, hlam]
            · linarith only [h10008, h10015, h10019, h10022, h10286, h8410, hlam]
          · linarith only [h10010, h10285, hlam]
        · have p10169_0 := h10169c.1
          have p10169_1 := h10169c.2.1
          have p10169_2 := h10169c.2.2.1
          have p10169_3 := h10169c.2.2.2
          rcases p10169_3 (m.d 0 2) (by simp) with h10296 | h10296
          · rcases p10169_3 (m.d 1 2) (by simp) with h10297 | h10297
            · rcases p10169_3 (m.d 2 3) (by simp) with h10298 | h10298
              · rcases p10169_3 (m.d 2 4) (by simp) with h10299 | h10299
                · linarith only [h10020, h10299, hlam]
                · rcases p10169_3 (m.d 2 5) (by simp) with h10301 | h10301
                  · linarith only [h10021, h10301, hlam]
                  · rcases h3bigk with h10303c | h10303c | h10303c | h10303c | h10303c | h10303c | h10303c | h10303c | h10303c | h10303c | h10303c | h10303c | h10303c | h10303c | h10303c | h10303c | h10303c | h10303c | h10303c | h10303c | h10303c | h10303c | h10303c | h10303c | h10303c
                    · have p10303_0 := h10303c.1
                      have p10303_1 := h10303c.2.1
                      have p10303_2 := h10303c.2.2.1
                      have p10303_3 := h10303c.2.2.2
                      linarith only [hlam, p10303_0]
                    · have p10303_0 := h10303c.1
                      have p10303_1 := h10303c.2.1
                      have p10303_2 := h10303c.2.2.1
                      have p10303_3 := h10303c.2.2.2
                      linarith only [h8410, hlam, p10303_1]
                    · have p10303_0 := h10303c.1
                      have p10303_1 := h10303c.2.1
                      have p10303_2 := h10303c.2.2.1
                      have p10303_3 := h10303c.2.2.2
                      linarith only [h10020, h10022, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p10169_1, p10303_1]
                    · have p10303_0 := h10303c.1
                      have p10303_1 := h10303c.2.1
                      have p10303_2 := h10303c.2.2.1
                      have p10303_3 := h10303c.2.2.2
                      rcases p10303_3 (m.d 0 3) (by simp) with h10307 | h10307
                      · rcases p10303_3 (m.d 1 3) (by simp) with h10308 | h10308
                        · rcases p10303_3 (m.d 2 3) (by simp) with h10309 | h10309
                          · linarith only [h10009, h10309, hlam]
                          · linarith only [h10020, h10309, hlam]
                        · linarith only [h10017, h10308, hlam]
                      · linarith only [h10307, hlam, p10303_0]
                    · have p10303_0 := h10303c.1
                      have p10303_1 := h10303c.2.1
                      have p10303_2 := h10303c.2.2.1
                      have p10303_3 := h10303c.2.2.2
                      rcases p10303_3 (m.d 0 3) (by simp) with h10314 | h10314
                      · rcases p10303_3 (m.d 1 3) (by simp) with h10315 | h10315
                        · rcases p10303_3 (m.d 2 3) (by simp) with h10316 | h10316
                          · linarith only [h10009, h10316, hlam]
                          · linarith only [h10021, h10316, hlam]
                        · linarith only [h10018, h10315, hlam]
                      · linarith only [h10314, hlam, p10303_0]
                    · have p10303_0 := h10303c.1
                      have p10303_1 := h10303c.2.1
                      have p10303_2 := h10303c.2.2.1
                      have p10303_3 := h10303c.2.2.2
                      linarith only [h10015, hc12, hlam, hphi, ht01, p10303_1, u0ehi2]
                    · have p10303_0 := h10303c.1
                      have p10303_1 := h10303c.2.1
                      have p10303_2 := h10303c.2.2.1
                      have p10303_3 := h10303c.2.2.2
                      linarith only [hlam, p10303_0]
                    · have p10303_0 := h10303c.1
                      have p10303_1 := h10303c.2.1
                      have p10303_2 := h10303c.2.2.1
                      have p10303_3 := h10303c.2.2.2
                      linarith only [h10015, h10020, h10022, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10169_1, p10303_1]
                    · have p10303_0 := h10303c.1
                      have p10303_1 := h10303c.2.1
                      have p10303_2 := h10303c.2.2.1
                      have p10303_3 := h10303c.2.2.2
                      linarith only [h10008, h10019, h10020, h10022, h8410, hlam, p10303_2]
                    · have p10303_0 := h10303c.1
                      have p10303_1 := h10303c.2.1
                      have p10303_2 := h10303c.2.2.1
                      have p10303_3 := h10303c.2.2.2
                      rcases p10303_3 (m.d 0 3) (by simp) with h10325 | h10325
                      · linarith only [h10325, h8410, hlam]
                      · linarith only [h10013, h10325, hlam]
                    · have p10303_0 := h10303c.1
                      have p10303_1 := h10303c.2.1
                      have p10303_2 := h10303c.2.2.1
                      have p10303_3 := h10303c.2.2.2
                      linarith only [h10009, hlam, p10303_0]
                    · have p10303_0 := h10303c.1
                      have p10303_1 := h10303c.2.1
                      have p10303_2 := h10303c.2.2.1
                      have p10303_3 := h10303c.2.2.2
                      linarith only [h10015, hlam, p10303_0]
                    · have p10303_0 := h10303c.1
                      have p10303_1 := h10303c.2.1
                      have p10303_2 := h10303c.2.2.1
                      have p10303_3 := h10303c.2.2.2
                      linarith only [hlam, p10303_0]
                    · have p10303_0 := h10303c.1
                      have p10303_1 := h10303c.2.1
                      have p10303_2 := h10303c.2.2.1
                      have p10303_3 := h10303c.2.2.2
                      rcases p10303_3 (m.d 0 3) (by simp) with h10331 | h10331
                      · rcases p10303_3 (m.d 1 3) (by simp) with h10332 | h10332
                        · rcases p10303_3 (m.d 2 3) (by simp) with h10333 | h10333
                          · rcases p10303_3 (m.d 3 4) (by simp) with h10334 | h10334
                            · linarith only [h10334, hlam, p10303_0]
                            · rcases p10303_3 (m.d 3 5) (by simp) with h10336 | h10336
                              · linarith only [h10021, h10336, hlam]
                              · linarith only [h10167, h10336, hlam]
                          · linarith only [h10333, hlam, p10303_0]
                        · linarith only [h10017, h10332, hlam]
                      · linarith only [h10012, h10331, hlam]
                    · have p10303_0 := h10303c.1
                      have p10303_1 := h10303c.2.1
                      have p10303_2 := h10303c.2.2.1
                      have p10303_3 := h10303c.2.2.2
                      rcases p10303_3 (m.d 0 3) (by simp) with h10342 | h10342
                      · rcases p10303_3 (m.d 1 3) (by simp) with h10343 | h10343
                        · rcases p10303_3 (m.d 2 3) (by simp) with h10344 | h10344
                          · rcases p10303_3 (m.d 3 4) (by simp) with h10345 | h10345
                            · linarith only [h10020, h10345, hlam]
                            · rcases p10303_3 (m.d 3 5) (by simp) with h10347 | h10347
                              · linarith only [h10347, hlam, p10303_0]
                              · rcases h5bigk with h10349c | h10349c | h10349c | h10349c | h10349c | h10349c | h10349c | h10349c | h10349c | h10349c | h10349c | h10349c | h10349c | h10349c | h10349c | h10349c | h10349c | h10349c | h10349c | h10349c | h10349c | h10349c | h10349c | h10349c | h10349c
                                · have p10349_0 := h10349c.1
                                  have p10349_1 := h10349c.2.1
                                  have p10349_2 := h10349c.2.2.1
                                  have p10349_3 := h10349c.2.2.2
                                  linarith only [hlam, p10349_0]
                                · have p10349_0 := h10349c.1
                                  have p10349_1 := h10349c.2.1
                                  have p10349_2 := h10349c.2.2.1
                                  have p10349_3 := h10349c.2.2.2
                                  linarith only [h10019, h10020, h10022, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p10349_1]
                                · have p10349_0 := h10349c.1
                                  have p10349_1 := h10349c.2.1
                                  have p10349_2 := h10349c.2.2.1
                                  have p10349_3 := h10349c.2.2.2
                                  linarith only [h10008, h8410, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b, p10349_1]
                                · have p10349_0 := h10349c.1
                                  have p10349_1 := h10349c.2.1
                                  have p10349_2 := h10349c.2.2.1
                                  have p10349_3 := h10349c.2.2.2
                                  linarith only [h10008, h8410, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b, p10349_1]
                                · have p10349_0 := h10349c.1
                                  have p10349_1 := h10349c.2.1
                                  have p10349_2 := h10349c.2.2.1
                                  have p10349_3 := h10349c.2.2.2
                                  linarith only [h10008, h10022, h8410, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p10349_1]
                                · have p10349_0 := h10349c.1
                                  have p10349_1 := h10349c.2.1
                                  have p10349_2 := h10349c.2.2.1
                                  have p10349_3 := h10349c.2.2.2
                                  linarith only [h10008, hlam, p10349_0]
                                · have p10349_0 := h10349c.1
                                  have p10349_1 := h10349c.2.1
                                  have p10349_2 := h10349c.2.2.1
                                  have p10349_3 := h10349c.2.2.2
                                  linarith only [hlam, p10349_0]
                                · have p10349_0 := h10349c.1
                                  have p10349_1 := h10349c.2.1
                                  have p10349_2 := h10349c.2.2.1
                                  have p10349_3 := h10349c.2.2.2
                                  linarith only [h10008, h10015, h10021, h8410, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p10349_1]
                                · have p10349_0 := h10349c.1
                                  have p10349_1 := h10349c.2.1
                                  have p10349_2 := h10349c.2.2.1
                                  have p10349_3 := h10349c.2.2.2
                                  linarith only [h10008, h10015, h8410, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p10349_1]
                                · have p10349_0 := h10349c.1
                                  have p10349_1 := h10349c.2.1
                                  have p10349_2 := h10349c.2.2.1
                                  have p10349_3 := h10349c.2.2.2
                                  linarith only [h10008, h10015, h10020, h10022, h8410, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10349_1]
                                · have p10349_0 := h10349c.1
                                  have p10349_1 := h10349c.2.1
                                  have p10349_2 := h10349c.2.2.1
                                  have p10349_3 := h10349c.2.2.2
                                  linarith only [h10011, hlam, p10349_1]
                                · have p10349_0 := h10349c.1
                                  have p10349_1 := h10349c.2.1
                                  have p10349_2 := h10349c.2.2.1
                                  have p10349_3 := h10349c.2.2.2
                                  linarith only [h10016, hlam, p10349_1]
                                · have p10349_0 := h10349c.1
                                  have p10349_1 := h10349c.2.1
                                  have p10349_2 := h10349c.2.2.1
                                  have p10349_3 := h10349c.2.2.2
                                  linarith only [hlam, p10349_0]
                                · have p10349_0 := h10349c.1
                                  have p10349_1 := h10349c.2.1
                                  have p10349_2 := h10349c.2.2.1
                                  have p10349_3 := h10349c.2.2.2
                                  linarith only [h10009, hc02, hc35, hlam, hphi, ht0b, ht5b, p10169_1, p10349_1]
                                · have p10349_0 := h10349c.1
                                  have p10349_1 := h10349c.2.1
                                  have p10349_2 := h10349c.2.2.1
                                  have p10349_3 := h10349c.2.2.2
                                  linarith only [h10022, hlam, p10349_1]
                                · have p10349_0 := h10349c.1
                                  have p10349_1 := h10349c.2.1
                                  have p10349_2 := h10349c.2.2.1
                                  have p10349_3 := h10349c.2.2.2
                                  linarith only [h10013, hlam, p10349_0]
                                · have p10349_0 := h10349c.1
                                  have p10349_1 := h10349c.2.1
                                  have p10349_2 := h10349c.2.2.1
                                  have p10349_3 := h10349c.2.2.2
                                  linarith only [h10018, hlam, p10349_0]
                                · have p10349_0 := h10349c.1
                                  have p10349_1 := h10349c.2.1
                                  have p10349_2 := h10349c.2.2.1
                                  have p10349_3 := h10349c.2.2.2
                                  linarith only [h10021, hlam, p10349_0]
                                · have p10349_0 := h10349c.1
                                  have p10349_1 := h10349c.2.1
                                  have p10349_2 := h10349c.2.2.1
                                  have p10349_3 := h10349c.2.2.2
                                  linarith only [hlam, p10349_0]
                                · have p10349_0 := h10349c.1
                                  have p10349_1 := h10349c.2.1
                                  have p10349_2 := h10349c.2.2.1
                                  have p10349_3 := h10349c.2.2.2
                                  linarith only [h10167, hlam, p10349_1]
                                · have p10349_0 := h10349c.1
                                  have p10349_1 := h10349c.2.1
                                  have p10349_2 := h10349c.2.2.1
                                  have p10349_3 := h10349c.2.2.2
                                  linarith only [h10014, hlam, p10349_0]
                                · have p10349_0 := h10349c.1
                                  have p10349_1 := h10349c.2.1
                                  have p10349_2 := h10349c.2.2.1
                                  have p10349_3 := h10349c.2.2.2
                                  linarith only [h10019, hlam, p10349_0]
                                · have p10349_0 := h10349c.1
                                  have p10349_1 := h10349c.2.1
                                  have p10349_2 := h10349c.2.2.1
                                  have p10349_3 := h10349c.2.2.2
                                  linarith only [h10014, hc04, hc25, hlam, hphi, ht0b, ht5b, p10349_1]
                                · have p10349_0 := h10349c.1
                                  have p10349_1 := h10349c.2.1
                                  have p10349_2 := h10349c.2.2.1
                                  have p10349_3 := h10349c.2.2.2
                                  linarith only [h10008, h10015, h10019, h8410, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p10349_1]
                                · have p10349_0 := h10349c.1
                                  have p10349_1 := h10349c.2.1
                                  have p10349_2 := h10349c.2.2.1
                                  have p10349_3 := h10349c.2.2.2
                                  linarith only [hlam, p10349_0]
                          · linarith only [h10344, hlam, p10303_0]
                        · linarith only [h10018, h10343, hlam]
                      · linarith only [h10013, h10342, hlam]
                    · have p10303_0 := h10303c.1
                      have p10303_1 := h10303c.2.1
                      have p10303_2 := h10303c.2.2.1
                      have p10303_3 := h10303c.2.2.2
                      linarith only [h10012, hlam, p10303_0]
                    · have p10303_0 := h10303c.1
                      have p10303_1 := h10303c.2.1
                      have p10303_2 := h10303c.2.2.1
                      have p10303_3 := h10303c.2.2.2
                      linarith only [h10017, hlam, p10303_0]
                    · have p10303_0 := h10303c.1
                      have p10303_1 := h10303c.2.1
                      have p10303_2 := h10303c.2.2.1
                      have p10303_3 := h10303c.2.2.2
                      linarith only [h10020, hlam, p10303_0]
                    · have p10303_0 := h10303c.1
                      have p10303_1 := h10303c.2.1
                      have p10303_2 := h10303c.2.2.1
                      have p10303_3 := h10303c.2.2.2
                      linarith only [hlam, p10303_0]
                    · have p10303_0 := h10303c.1
                      have p10303_1 := h10303c.2.1
                      have p10303_2 := h10303c.2.2.1
                      have p10303_3 := h10303c.2.2.2
                      linarith only [h10167, hlam, p10303_1]
                    · have p10303_0 := h10303c.1
                      have p10303_1 := h10303c.2.1
                      have p10303_2 := h10303c.2.2.1
                      have p10303_3 := h10303c.2.2.2
                      linarith only [h10013, hlam, p10303_0]
                    · have p10303_0 := h10303c.1
                      have p10303_1 := h10303c.2.1
                      have p10303_2 := h10303c.2.2.1
                      have p10303_3 := h10303c.2.2.2
                      linarith only [h10018, hlam, p10303_0]
                    · have p10303_0 := h10303c.1
                      have p10303_1 := h10303c.2.1
                      have p10303_2 := h10303c.2.2.1
                      have p10303_3 := h10303c.2.2.2
                      linarith only [h10021, hlam, p10303_0]
                    · have p10303_0 := h10303c.1
                      have p10303_1 := h10303c.2.1
                      have p10303_2 := h10303c.2.2.1
                      have p10303_3 := h10303c.2.2.2
                      linarith only [h10008, h10015, h10018, h8410, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10303_1]
                    · have p10303_0 := h10303c.1
                      have p10303_1 := h10303c.2.1
                      have p10303_2 := h10303c.2.2.1
                      have p10303_3 := h10303c.2.2.2
                      linarith only [hlam, p10303_0]
              · linarith only [h10021, h10298, hlam]
            · linarith only [h10016, h10297, hlam]
          · linarith only [h10011, h10296, hlam]
        · have p10169_0 := h10169c.1
          have p10169_1 := h10169c.2.1
          have p10169_2 := h10169c.2.2.1
          have p10169_3 := h10169c.2.2.2
          linarith only [h10010, hlam, p10169_0]
        · have p10169_0 := h10169c.1
          have p10169_1 := h10169c.2.1
          have p10169_2 := h10169c.2.2.1
          have p10169_3 := h10169c.2.2.2
          linarith only [h10015, h8410, hc01, hc24, hlam, hphi, ht12, p10169_1]
        · have p10169_0 := h10169c.1
          have p10169_1 := h10169c.2.1
          have p10169_2 := h10169c.2.2.1
          have p10169_3 := h10169c.2.2.2
          linarith only [h10020, hlam, p10169_1]
        · have p10169_0 := h10169c.1
          have p10169_1 := h10169c.2.1
          have p10169_2 := h10169c.2.2.1
          have p10169_3 := h10169c.2.2.2
          linarith only [hlam, p10169_0]
        · have p10169_0 := h10169c.1
          have p10169_1 := h10169c.2.1
          have p10169_2 := h10169c.2.2.1
          have p10169_3 := h10169c.2.2.2
          linarith only [h10022, hlam, p10169_1]
        · have p10169_0 := h10169c.1
          have p10169_1 := h10169c.2.1
          have p10169_2 := h10169c.2.2.1
          have p10169_3 := h10169c.2.2.2
          linarith only [h10011, hlam, p10169_0]
        · have p10169_0 := h10169c.1
          have p10169_1 := h10169c.2.1
          have p10169_2 := h10169c.2.2.1
          have p10169_3 := h10169c.2.2.2
          linarith only [h10016, hlam, p10169_0]
        · have p10169_0 := h10169c.1
          have p10169_1 := h10169c.2.1
          have p10169_2 := h10169c.2.2.1
          have p10169_3 := h10169c.2.2.2
          linarith only [h10021, hlam, p10169_1]
        · have p10169_0 := h10169c.1
          have p10169_1 := h10169c.2.1
          have p10169_2 := h10169c.2.2.1
          have p10169_3 := h10169c.2.2.2
          linarith only [h10008, h10015, h10016, h8410, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p10169_1]
        · have p10169_0 := h10169c.1
          have p10169_1 := h10169c.2.1
          have p10169_2 := h10169c.2.2.1
          have p10169_3 := h10169c.2.2.2
          linarith only [hlam, p10169_0]
  · linarith only [h10008, h10015, h10018, h10020, h10021, h8410, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]

end R2N4
