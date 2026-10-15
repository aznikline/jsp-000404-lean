import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10174000 in
set_option maxHeartbeats 10174000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s3_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3397 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h3738 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h3969 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h3970 | h3970
  · rcases m.htr 0 4 5 (by decide) (by decide) with h3971 | h3971
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3972 | h3972
      · linarith only [h0, h3972, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3974 | h3974
        · linarith only [h0, h3397, h3974, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3976 | h3976
          · linarith only [h0, h3738, h3976, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3978 | h3978
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3979 | h3979
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3980 | h3980
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3981 | h3981
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3982 | h3982
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3983 | h3983
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3984 | h3984
                        · rcases h0bigk with h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c | h3985c
                          · have p3985_0 := h3985c.1
                            have p3985_1 := h3985c.2.1
                            have p3985_2 := h3985c.2.2.1
                            have p3985_3 := h3985c.2.2.2
                            linarith only [hlam, p3985_0]
                          · have p3985_0 := h3985c.1
                            have p3985_1 := h3985c.2.1
                            have p3985_2 := h3985c.2.2.1
                            have p3985_3 := h3985c.2.2.2
                            rcases p3985_3 (m.d 0 1) (by simp) with h3987 | h3987
                            · rcases p3985_3 (m.d 0 2) (by simp) with h3988 | h3988
                              · linarith only [h0, h3988, hlam]
                              · rcases p3985_3 (m.d 0 3) (by simp) with h3990 | h3990
                                · linarith only [h1, h3990, hlam]
                                · linarith only [h3990, h4, hlam]
                            · linarith only [h0, h3987, hlam]
                          · have p3985_0 := h3985c.1
                            have p3985_1 := h3985c.2.1
                            have p3985_2 := h3985c.2.2.1
                            have p3985_3 := h3985c.2.2.2
                            linarith only [h1, h3978, h3984, hc01, hc45, hlam, hphi, ht0b, ht5b, p3985_1]
                          · have p3985_0 := h3985c.1
                            have p3985_1 := h3985c.2.1
                            have p3985_2 := h3985c.2.2.1
                            have p3985_3 := h3985c.2.2.2
                            linarith only [h3969, h3984, hc01, hc45, hlam, hphi, ht0b, ht5b, p3985_1]
                          · have p3985_0 := h3985c.1
                            have p3985_1 := h3985c.2.1
                            have p3985_2 := h3985c.2.2.1
                            have p3985_3 := h3985c.2.2.2
                            rcases p3985_3 (m.d 0 1) (by simp) with h3996 | h3996
                            · rcases p3985_3 (m.d 0 2) (by simp) with h3997 | h3997
                              · linarith only [h0, h3997, hlam]
                              · rcases p3985_3 (m.d 0 3) (by simp) with h3999 | h3999
                                · linarith only [h1, h3999, hlam]
                                · linarith only [h3970, h3999, hlam]
                            · linarith only [h3, h3996, hlam]
                          · have p3985_0 := h3985c.1
                            have p3985_1 := h3985c.2.1
                            have p3985_2 := h3985c.2.2.1
                            have p3985_3 := h3985c.2.2.2
                            linarith only [h0, hlam, p3985_0]
                          · have p3985_0 := h3985c.1
                            have p3985_1 := h3985c.2.1
                            have p3985_2 := h3985c.2.2.1
                            have p3985_3 := h3985c.2.2.2
                            linarith only [hlam, p3985_0]
                          · have p3985_0 := h3985c.1
                            have p3985_1 := h3985c.2.1
                            have p3985_2 := h3985c.2.2.1
                            have p3985_3 := h3985c.2.2.2
                            linarith only [h4, hlam, p3985_0]
                          · have p3985_0 := h3985c.1
                            have p3985_1 := h3985c.2.1
                            have p3985_2 := h3985c.2.2.1
                            have p3985_3 := h3985c.2.2.2
                            linarith only [h3397, hlam, p3985_1]
                          · have p3985_0 := h3985c.1
                            have p3985_1 := h3985c.2.1
                            have p3985_2 := h3985c.2.2.1
                            have p3985_3 := h3985c.2.2.2
                            linarith only [h3738, hlam, p3985_0]
                          · have p3985_0 := h3985c.1
                            have p3985_1 := h3985c.2.1
                            have p3985_2 := h3985c.2.2.1
                            have p3985_3 := h3985c.2.2.2
                            linarith only [h1, hlam, p3985_1]
                          · have p3985_0 := h3985c.1
                            have p3985_1 := h3985c.2.1
                            have p3985_2 := h3985c.2.2.1
                            have p3985_3 := h3985c.2.2.2
                            linarith only [h0, h4, hc12, hc23, hlam, hphi, p3985_1]
                          · have p3985_0 := h3985c.1
                            have p3985_1 := h3985c.2.1
                            have p3985_2 := h3985c.2.2.1
                            have p3985_3 := h3985c.2.2.2
                            linarith only [hlam, p3985_0]
                          · have p3985_0 := h3985c.1
                            have p3985_1 := h3985c.2.1
                            have p3985_2 := h3985c.2.2.1
                            have p3985_3 := h3985c.2.2.2
                            linarith only [h2, h3978, h3984, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p3985_1]
                          · have p3985_0 := h3985c.1
                            have p3985_1 := h3985c.2.1
                            have p3985_2 := h3985c.2.2.1
                            have p3985_3 := h3985c.2.2.2
                            linarith only [h0, h3738, h4, hc12, hc23, hlam, hphi, p3985_1]
                          · have p3985_0 := h3985c.1
                            have p3985_1 := h3985c.2.1
                            have p3985_2 := h3985c.2.2.1
                            have p3985_3 := h3985c.2.2.2
                            linarith only [h2, hlam, p3985_0]
                          · have p3985_0 := h3985c.1
                            have p3985_1 := h3985c.2.1
                            have p3985_2 := h3985c.2.2.1
                            have p3985_3 := h3985c.2.2.2
                            linarith only [h0, h3397, hc12, hc24, hlam, hphi, p3985_1]
                          · have p3985_0 := h3985c.1
                            have p3985_1 := h3985c.2.1
                            have p3985_2 := h3985c.2.2.1
                            have p3985_3 := h3985c.2.2.2
                            linarith only [h3969, hlam, p3985_0]
                          · have p3985_0 := h3985c.1
                            have p3985_1 := h3985c.2.1
                            have p3985_2 := h3985c.2.2.1
                            have p3985_3 := h3985c.2.2.2
                            linarith only [hlam, p3985_0]
                          · have p3985_0 := h3985c.1
                            have p3985_1 := h3985c.2.1
                            have p3985_2 := h3985c.2.2.1
                            have p3985_3 := h3985c.2.2.2
                            linarith only [h0, h3738, h3969, h4, hc12, hc23, hlam, hphi, p3985_1]
                          · have p3985_0 := h3985c.1
                            have p3985_1 := h3985c.2.1
                            have p3985_2 := h3985c.2.2.1
                            have p3985_3 := h3985c.2.2.2
                            linarith only [h3, hlam, p3985_0]
                          · have p3985_0 := h3985c.1
                            have p3985_1 := h3985c.2.1
                            have p3985_2 := h3985c.2.2.1
                            have p3985_3 := h3985c.2.2.2
                            linarith only [h0, h3738, h3983, hc12, hc24, hlam, hphi, p3985_1]
                          · have p3985_0 := h3985c.1
                            have p3985_1 := h3985c.2.1
                            have p3985_2 := h3985c.2.2.1
                            have p3985_3 := h3985c.2.2.2
                            linarith only [h3970, hlam, p3985_0]
                          · have p3985_0 := h3985c.1
                            have p3985_1 := h3985c.2.1
                            have p3985_2 := h3985c.2.2.1
                            have p3985_3 := h3985c.2.2.2
                            linarith only [h3971, hlam, p3985_1]
                          · have p3985_0 := h3985c.1
                            have p3985_1 := h3985c.2.1
                            have p3985_2 := h3985c.2.2.1
                            have p3985_3 := h3985c.2.2.2
                            linarith only [hlam, p3985_0]
                        · rcases h0bigk with h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c | h4023c
                          · have p4023_0 := h4023c.1
                            have p4023_1 := h4023c.2.1
                            have p4023_2 := h4023c.2.2.1
                            have p4023_3 := h4023c.2.2.2
                            linarith only [hlam, p4023_0]
                          · have p4023_0 := h4023c.1
                            have p4023_1 := h4023c.2.1
                            have p4023_2 := h4023c.2.2.1
                            have p4023_3 := h4023c.2.2.2
                            rcases p4023_3 (m.d 0 1) (by simp) with h4025 | h4025
                            · rcases p4023_3 (m.d 0 2) (by simp) with h4026 | h4026
                              · linarith only [h0, h4026, hlam]
                              · rcases p4023_3 (m.d 0 3) (by simp) with h4028 | h4028
                                · linarith only [h1, h4028, hlam]
                                · linarith only [h4, h4028, hlam]
                            · linarith only [h0, h4025, hlam]
                          · have p4023_0 := h4023c.1
                            have p4023_1 := h4023c.2.1
                            have p4023_2 := h4023c.2.2.1
                            have p4023_3 := h4023c.2.2.2
                            linarith only [h1, h3978, h3980, h3984, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4023_1]
                          · have p4023_0 := h4023c.1
                            have p4023_1 := h4023c.2.1
                            have p4023_2 := h4023c.2.2.1
                            have p4023_3 := h4023c.2.2.2
                            linarith only [h2, h3980, h3984, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4023_1]
                          · have p4023_0 := h4023c.1
                            have p4023_1 := h4023c.2.1
                            have p4023_2 := h4023c.2.2.1
                            have p4023_3 := h4023c.2.2.2
                            linarith only [h3971, h3984, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4023_1]
                          · have p4023_0 := h4023c.1
                            have p4023_1 := h4023c.2.1
                            have p4023_2 := h4023c.2.2.1
                            have p4023_3 := h4023c.2.2.2
                            linarith only [h0, hlam, p4023_0]
                          · have p4023_0 := h4023c.1
                            have p4023_1 := h4023c.2.1
                            have p4023_2 := h4023c.2.2.1
                            have p4023_3 := h4023c.2.2.2
                            linarith only [hlam, p4023_0]
                          · have p4023_0 := h4023c.1
                            have p4023_1 := h4023c.2.1
                            have p4023_2 := h4023c.2.2.1
                            have p4023_3 := h4023c.2.2.2
                            linarith only [h4, hlam, p4023_0]
                          · have p4023_0 := h4023c.1
                            have p4023_1 := h4023c.2.1
                            have p4023_2 := h4023c.2.2.1
                            have p4023_3 := h4023c.2.2.2
                            linarith only [h3397, hlam, p4023_1]
                          · have p4023_0 := h4023c.1
                            have p4023_1 := h4023c.2.1
                            have p4023_2 := h4023c.2.2.1
                            have p4023_3 := h4023c.2.2.2
                            linarith only [h3738, hlam, p4023_0]
                          · have p4023_0 := h4023c.1
                            have p4023_1 := h4023c.2.1
                            have p4023_2 := h4023c.2.2.1
                            have p4023_3 := h4023c.2.2.2
                            linarith only [h1, hlam, p4023_1]
                          · have p4023_0 := h4023c.1
                            have p4023_1 := h4023c.2.1
                            have p4023_2 := h4023c.2.2.1
                            have p4023_3 := h4023c.2.2.2
                            linarith only [h0, h4, hc12, hc23, hlam, hphi, p4023_1]
                          · have p4023_0 := h4023c.1
                            have p4023_1 := h4023c.2.1
                            have p4023_2 := h4023c.2.2.1
                            have p4023_3 := h4023c.2.2.2
                            linarith only [hlam, p4023_0]
                          · have p4023_0 := h4023c.1
                            have p4023_1 := h4023c.2.1
                            have p4023_2 := h4023c.2.2.1
                            have p4023_3 := h4023c.2.2.2
                            linarith only [h2, h3980, h3984, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4023_1]
                          · have p4023_0 := h4023c.1
                            have p4023_1 := h4023c.2.1
                            have p4023_2 := h4023c.2.2.1
                            have p4023_3 := h4023c.2.2.2
                            linarith only [h0, h3738, h4, hc12, hc23, hlam, hphi, p4023_1]
                          · have p4023_0 := h4023c.1
                            have p4023_1 := h4023c.2.1
                            have p4023_2 := h4023c.2.2.1
                            have p4023_3 := h4023c.2.2.2
                            linarith only [h2, hlam, p4023_0]
                          · have p4023_0 := h4023c.1
                            have p4023_1 := h4023c.2.1
                            have p4023_2 := h4023c.2.2.1
                            have p4023_3 := h4023c.2.2.2
                            linarith only [h0, h3397, h3981, hc12, hc23, hlam, hphi, p4023_1]
                          · have p4023_0 := h4023c.1
                            have p4023_1 := h4023c.2.1
                            have p4023_2 := h4023c.2.2.1
                            have p4023_3 := h4023c.2.2.2
                            linarith only [h3969, hlam, p4023_0]
                          · have p4023_0 := h4023c.1
                            have p4023_1 := h4023c.2.1
                            have p4023_2 := h4023c.2.2.1
                            have p4023_3 := h4023c.2.2.2
                            linarith only [hlam, p4023_0]
                          · have p4023_0 := h4023c.1
                            have p4023_1 := h4023c.2.1
                            have p4023_2 := h4023c.2.2.1
                            have p4023_3 := h4023c.2.2.2
                            linarith only [h0, h3397, h3738, h3981, hc12, hc23, hlam, hphi, p4023_1]
                          · have p4023_0 := h4023c.1
                            have p4023_1 := h4023c.2.1
                            have p4023_2 := h4023c.2.2.1
                            have p4023_3 := h4023c.2.2.2
                            linarith only [h3, hlam, p4023_0]
                          · have p4023_0 := h4023c.1
                            have p4023_1 := h4023c.2.1
                            have p4023_2 := h4023c.2.2.1
                            have p4023_3 := h4023c.2.2.2
                            linarith only [h0, h3738, h3981, h3983, hc12, hc23, hlam, hphi, p4023_1]
                          · have p4023_0 := h4023c.1
                            have p4023_1 := h4023c.2.1
                            have p4023_2 := h4023c.2.2.1
                            have p4023_3 := h4023c.2.2.2
                            linarith only [h3970, hlam, p4023_0]
                          · have p4023_0 := h4023c.1
                            have p4023_1 := h4023c.2.1
                            have p4023_2 := h4023c.2.2.1
                            have p4023_3 := h4023c.2.2.2
                            linarith only [h3971, hlam, p4023_1]
                          · have p4023_0 := h4023c.1
                            have p4023_1 := h4023c.2.1
                            have p4023_2 := h4023c.2.2.1
                            have p4023_3 := h4023c.2.2.2
                            linarith only [hlam, p4023_0]
                      · linarith only [h2, h3397, h3980, h3983, hlam]
                    · linarith only [h2, h3969, h3979, h3980, h3982, h4, hlam]
                  · linarith only [h3969, h3981, h4, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4058 | h4058
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4059 | h4059
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4060 | h4060
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4061 | h4061
                        · linarith only [h3978, h3980, h4061, hlam]
                        · rcases h0bigk with h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c | h4063c
                          · have p4063_0 := h4063c.1
                            have p4063_1 := h4063c.2.1
                            have p4063_2 := h4063c.2.2.1
                            have p4063_3 := h4063c.2.2.2
                            linarith only [hlam, p4063_0]
                          · have p4063_0 := h4063c.1
                            have p4063_1 := h4063c.2.1
                            have p4063_2 := h4063c.2.2.1
                            have p4063_3 := h4063c.2.2.2
                            rcases p4063_3 (m.d 0 1) (by simp) with h4065 | h4065
                            · rcases p4063_3 (m.d 0 2) (by simp) with h4066 | h4066
                              · linarith only [h0, h4066, hlam]
                              · rcases p4063_3 (m.d 0 3) (by simp) with h4068 | h4068
                                · linarith only [h1, h4068, hlam]
                                · linarith only [h4, h4068, hlam]
                            · linarith only [h0, h4065, hlam]
                          · have p4063_0 := h4063c.1
                            have p4063_1 := h4063c.2.1
                            have p4063_2 := h4063c.2.2.1
                            have p4063_3 := h4063c.2.2.2
                            linarith only [h3969, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4063_1]
                          · have p4063_0 := h4063c.1
                            have p4063_1 := h4063c.2.1
                            have p4063_2 := h4063c.2.2.1
                            have p4063_3 := h4063c.2.2.2
                            linarith only [h3971, h3974, h3980, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4063_1]
                          · have p4063_0 := h4063c.1
                            have p4063_1 := h4063c.2.1
                            have p4063_2 := h4063c.2.2.1
                            have p4063_3 := h4063c.2.2.2
                            linarith only [h3971, h3974, h3980, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4063_1]
                          · have p4063_0 := h4063c.1
                            have p4063_1 := h4063c.2.1
                            have p4063_2 := h4063c.2.2.1
                            have p4063_3 := h4063c.2.2.2
                            linarith only [h0, hlam, p4063_0]
                          · have p4063_0 := h4063c.1
                            have p4063_1 := h4063c.2.1
                            have p4063_2 := h4063c.2.2.1
                            have p4063_3 := h4063c.2.2.2
                            linarith only [hlam, p4063_0]
                          · have p4063_0 := h4063c.1
                            have p4063_1 := h4063c.2.1
                            have p4063_2 := h4063c.2.2.1
                            have p4063_3 := h4063c.2.2.2
                            linarith only [h4, hlam, p4063_0]
                          · have p4063_0 := h4063c.1
                            have p4063_1 := h4063c.2.1
                            have p4063_2 := h4063c.2.2.1
                            have p4063_3 := h4063c.2.2.2
                            linarith only [h3397, hlam, p4063_1]
                          · have p4063_0 := h4063c.1
                            have p4063_1 := h4063c.2.1
                            have p4063_2 := h4063c.2.2.1
                            have p4063_3 := h4063c.2.2.2
                            linarith only [h3738, hlam, p4063_0]
                          · have p4063_0 := h4063c.1
                            have p4063_1 := h4063c.2.1
                            have p4063_2 := h4063c.2.2.1
                            have p4063_3 := h4063c.2.2.2
                            linarith only [h1, hlam, p4063_1]
                          · have p4063_0 := h4063c.1
                            have p4063_1 := h4063c.2.1
                            have p4063_2 := h4063c.2.2.1
                            have p4063_3 := h4063c.2.2.2
                            linarith only [h0, h4, hc12, hc23, hlam, hphi, p4063_1]
                          · have p4063_0 := h4063c.1
                            have p4063_1 := h4063c.2.1
                            have p4063_2 := h4063c.2.2.1
                            have p4063_3 := h4063c.2.2.2
                            linarith only [hlam, p4063_0]
                          · have p4063_0 := h4063c.1
                            have p4063_1 := h4063c.2.1
                            have p4063_2 := h4063c.2.2.1
                            have p4063_3 := h4063c.2.2.2
                            linarith only [h3971, h3974, h3980, h4, hc12, hc23, hlam, hphi, p4063_1]
                          · have p4063_0 := h4063c.1
                            have p4063_1 := h4063c.2.1
                            have p4063_2 := h4063c.2.2.1
                            have p4063_3 := h4063c.2.2.2
                            linarith only [h0, h3738, h4, hc12, hc23, hlam, hphi, p4063_1]
                          · have p4063_0 := h4063c.1
                            have p4063_1 := h4063c.2.1
                            have p4063_2 := h4063c.2.2.1
                            have p4063_3 := h4063c.2.2.2
                            linarith only [h2, hlam, p4063_0]
                          · have p4063_0 := h4063c.1
                            have p4063_1 := h4063c.2.1
                            have p4063_2 := h4063c.2.2.1
                            have p4063_3 := h4063c.2.2.2
                            linarith only [h0, h3397, hc12, hc24, hlam, hphi, p4063_1]
                          · have p4063_0 := h4063c.1
                            have p4063_1 := h4063c.2.1
                            have p4063_2 := h4063c.2.2.1
                            have p4063_3 := h4063c.2.2.2
                            linarith only [h3969, hlam, p4063_0]
                          · have p4063_0 := h4063c.1
                            have p4063_1 := h4063c.2.1
                            have p4063_2 := h4063c.2.2.1
                            have p4063_3 := h4063c.2.2.2
                            linarith only [hlam, p4063_0]
                          · have p4063_0 := h4063c.1
                            have p4063_1 := h4063c.2.1
                            have p4063_2 := h4063c.2.2.1
                            have p4063_3 := h4063c.2.2.2
                            linarith only [h0, h3738, h3969, h4, hc12, hc23, hlam, hphi, p4063_1]
                          · have p4063_0 := h4063c.1
                            have p4063_1 := h4063c.2.1
                            have p4063_2 := h4063c.2.2.1
                            have p4063_3 := h4063c.2.2.2
                            linarith only [h3, hlam, p4063_0]
                          · have p4063_0 := h4063c.1
                            have p4063_1 := h4063c.2.1
                            have p4063_2 := h4063c.2.2.1
                            have p4063_3 := h4063c.2.2.2
                            linarith only [h0, h3738, h4060, hc12, hc24, hlam, hphi, p4063_1]
                          · have p4063_0 := h4063c.1
                            have p4063_1 := h4063c.2.1
                            have p4063_2 := h4063c.2.2.1
                            have p4063_3 := h4063c.2.2.2
                            linarith only [h3970, hlam, p4063_0]
                          · have p4063_0 := h4063c.1
                            have p4063_1 := h4063c.2.1
                            have p4063_2 := h4063c.2.2.1
                            have p4063_3 := h4063c.2.2.2
                            linarith only [h3971, hlam, p4063_1]
                          · have p4063_0 := h4063c.1
                            have p4063_1 := h4063c.2.1
                            have p4063_2 := h4063c.2.2.1
                            have p4063_3 := h4063c.2.2.2
                            linarith only [hlam, p4063_0]
                      · linarith only [h3397, h3971, h4060, hlam]
                    · linarith only [h1, h3969, h3971, h3979, h4, h4059, hc01, hc45, hlam, hphi, ht0b, ht5b]
                  · linarith only [h3969, h4, h4058, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4098 | h4098
                · linarith only [h3978, h3979, h4098, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4100 | h4100
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4101 | h4101
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4102 | h4102
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4103 | h4103
                        · linarith only [h3970, h3978, h3979, h4, h4098, h4103, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases h0bigk with h4105c | h4105c | h4105c | h4105c | h4105c | h4105c | h4105c | h4105c | h4105c | h4105c | h4105c | h4105c | h4105c | h4105c | h4105c | h4105c | h4105c | h4105c | h4105c | h4105c | h4105c | h4105c | h4105c | h4105c | h4105c
                          · have p4105_0 := h4105c.1
                            have p4105_1 := h4105c.2.1
                            have p4105_2 := h4105c.2.2.1
                            have p4105_3 := h4105c.2.2.2
                            linarith only [hlam, p4105_0]
                          · have p4105_0 := h4105c.1
                            have p4105_1 := h4105c.2.1
                            have p4105_2 := h4105c.2.2.1
                            have p4105_3 := h4105c.2.2.2
                            rcases p4105_3 (m.d 0 1) (by simp) with h4107 | h4107
                            · rcases p4105_3 (m.d 0 2) (by simp) with h4108 | h4108
                              · linarith only [h0, h4108, hlam]
                              · rcases p4105_3 (m.d 0 3) (by simp) with h4110 | h4110
                                · linarith only [h1, h4110, hlam]
                                · linarith only [h4, h4110, hlam]
                            · linarith only [h0, h4107, hlam]
                          · have p4105_0 := h4105c.1
                            have p4105_1 := h4105c.2.1
                            have p4105_2 := h4105c.2.2.1
                            have p4105_3 := h4105c.2.2.2
                            linarith only [h3969, h3971, h3979, h4103, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4105_1]
                          · have p4105_0 := h4105c.1
                            have p4105_1 := h4105c.2.1
                            have p4105_2 := h4105c.2.2.1
                            have p4105_3 := h4105c.2.2.2
                            linarith only [h3971, h3978, h3979, h4103, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4105_1]
                          · have p4105_0 := h4105c.1
                            have p4105_1 := h4105c.2.1
                            have p4105_2 := h4105c.2.2.1
                            have p4105_3 := h4105c.2.2.2
                            linarith only [h3, h3978, h3979, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4105_1]
                          · have p4105_0 := h4105c.1
                            have p4105_1 := h4105c.2.1
                            have p4105_2 := h4105c.2.2.1
                            have p4105_3 := h4105c.2.2.2
                            linarith only [h0, hlam, p4105_0]
                          · have p4105_0 := h4105c.1
                            have p4105_1 := h4105c.2.1
                            have p4105_2 := h4105c.2.2.1
                            have p4105_3 := h4105c.2.2.2
                            linarith only [hlam, p4105_0]
                          · have p4105_0 := h4105c.1
                            have p4105_1 := h4105c.2.1
                            have p4105_2 := h4105c.2.2.1
                            have p4105_3 := h4105c.2.2.2
                            linarith only [h4, hlam, p4105_0]
                          · have p4105_0 := h4105c.1
                            have p4105_1 := h4105c.2.1
                            have p4105_2 := h4105c.2.2.1
                            have p4105_3 := h4105c.2.2.2
                            linarith only [h3397, hlam, p4105_1]
                          · have p4105_0 := h4105c.1
                            have p4105_1 := h4105c.2.1
                            have p4105_2 := h4105c.2.2.1
                            have p4105_3 := h4105c.2.2.2
                            linarith only [h3738, hlam, p4105_0]
                          · have p4105_0 := h4105c.1
                            have p4105_1 := h4105c.2.1
                            have p4105_2 := h4105c.2.2.1
                            have p4105_3 := h4105c.2.2.2
                            linarith only [h1, hlam, p4105_1]
                          · have p4105_0 := h4105c.1
                            have p4105_1 := h4105c.2.1
                            have p4105_2 := h4105c.2.2.1
                            have p4105_3 := h4105c.2.2.2
                            linarith only [h0, h4, hc12, hc23, hlam, hphi, p4105_1]
                          · have p4105_0 := h4105c.1
                            have p4105_1 := h4105c.2.1
                            have p4105_2 := h4105c.2.2.1
                            have p4105_3 := h4105c.2.2.2
                            linarith only [hlam, p4105_0]
                          · have p4105_0 := h4105c.1
                            have p4105_1 := h4105c.2.1
                            have p4105_2 := h4105c.2.2.1
                            have p4105_3 := h4105c.2.2.2
                            linarith only [h3971, h3978, h3979, h4, h4103, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4105_1]
                          · have p4105_0 := h4105c.1
                            have p4105_1 := h4105c.2.1
                            have p4105_2 := h4105c.2.2.1
                            have p4105_3 := h4105c.2.2.2
                            linarith only [h3, h3978, h3979, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4105_1]
                          · have p4105_0 := h4105c.1
                            have p4105_1 := h4105c.2.1
                            have p4105_2 := h4105c.2.2.1
                            have p4105_3 := h4105c.2.2.2
                            linarith only [h2, hlam, p4105_0]
                          · have p4105_0 := h4105c.1
                            have p4105_1 := h4105c.2.1
                            have p4105_2 := h4105c.2.2.1
                            have p4105_3 := h4105c.2.2.2
                            linarith only [h0, h3397, h4100, hc12, hc23, hlam, hphi, p4105_1]
                          · have p4105_0 := h4105c.1
                            have p4105_1 := h4105c.2.1
                            have p4105_2 := h4105c.2.2.1
                            have p4105_3 := h4105c.2.2.2
                            linarith only [h3969, hlam, p4105_0]
                          · have p4105_0 := h4105c.1
                            have p4105_1 := h4105c.2.1
                            have p4105_2 := h4105c.2.2.1
                            have p4105_3 := h4105c.2.2.2
                            linarith only [hlam, p4105_0]
                          · have p4105_0 := h4105c.1
                            have p4105_1 := h4105c.2.1
                            have p4105_2 := h4105c.2.2.1
                            have p4105_3 := h4105c.2.2.2
                            linarith only [h3397, h3970, h3978, h3979, h4100, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4105_1]
                          · have p4105_0 := h4105c.1
                            have p4105_1 := h4105c.2.1
                            have p4105_2 := h4105c.2.2.1
                            have p4105_3 := h4105c.2.2.2
                            linarith only [h3, hlam, p4105_0]
                          · have p4105_0 := h4105c.1
                            have p4105_1 := h4105c.2.1
                            have p4105_2 := h4105c.2.2.1
                            have p4105_3 := h4105c.2.2.2
                            linarith only [h0, h3738, hc12, hc25, hlam, hphi, p4105_1]
                          · have p4105_0 := h4105c.1
                            have p4105_1 := h4105c.2.1
                            have p4105_2 := h4105c.2.2.1
                            have p4105_3 := h4105c.2.2.2
                            linarith only [h3970, hlam, p4105_0]
                          · have p4105_0 := h4105c.1
                            have p4105_1 := h4105c.2.1
                            have p4105_2 := h4105c.2.2.1
                            have p4105_3 := h4105c.2.2.2
                            linarith only [h3971, hlam, p4105_1]
                          · have p4105_0 := h4105c.1
                            have p4105_1 := h4105c.2.1
                            have p4105_2 := h4105c.2.2.1
                            have p4105_3 := h4105c.2.2.2
                            linarith only [hlam, p4105_0]
                      · linarith only [h3397, h3970, h3971, h3978, h3979, h4102, hc34, hc45, hlam, hphi]
                    · linarith only [h3969, h3971, h3974, h4, h4098, h4101, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h3970, h3978, h3979, h4, h4100, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4140 | h4140
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4141 | h4141
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4142 | h4142
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4143 | h4143
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4144 | h4144
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4145 | h4145
                        · rcases h0bigk with h4146c | h4146c | h4146c | h4146c | h4146c | h4146c | h4146c | h4146c | h4146c | h4146c | h4146c | h4146c | h4146c | h4146c | h4146c | h4146c | h4146c | h4146c | h4146c | h4146c | h4146c | h4146c | h4146c | h4146c | h4146c
                          · have p4146_0 := h4146c.1
                            have p4146_1 := h4146c.2.1
                            have p4146_2 := h4146c.2.2.1
                            have p4146_3 := h4146c.2.2.2
                            linarith only [hlam, p4146_0]
                          · have p4146_0 := h4146c.1
                            have p4146_1 := h4146c.2.1
                            have p4146_2 := h4146c.2.2.1
                            have p4146_3 := h4146c.2.2.2
                            rcases p4146_3 (m.d 0 1) (by simp) with h4148 | h4148
                            · rcases p4146_3 (m.d 0 2) (by simp) with h4149 | h4149
                              · linarith only [h0, h4149, hlam]
                              · rcases p4146_3 (m.d 0 3) (by simp) with h4151 | h4151
                                · linarith only [h1, h4151, hlam]
                                · linarith only [h4, h4151, hlam]
                            · linarith only [h0, h4148, hlam]
                          · have p4146_0 := h4146c.1
                            have p4146_1 := h4146c.2.1
                            have p4146_2 := h4146c.2.2.1
                            have p4146_3 := h4146c.2.2.2
                            linarith only [h3969, h3978, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4146_1]
                          · have p4146_0 := h4146c.1
                            have p4146_1 := h4146c.2.1
                            have p4146_2 := h4146c.2.2.1
                            have p4146_3 := h4146c.2.2.2
                            linarith only [h3969, h3978, h4140, h4145, hc01, hc45, hlam, hphi, ht0b, ht5b, p4146_1]
                          · have p4146_0 := h4146c.1
                            have p4146_1 := h4146c.2.1
                            have p4146_2 := h4146c.2.2.1
                            have p4146_3 := h4146c.2.2.2
                            rcases p4146_3 (m.d 0 1) (by simp) with h4157 | h4157
                            · rcases p4146_3 (m.d 0 2) (by simp) with h4158 | h4158
                              · linarith only [h0, h4158, hlam]
                              · rcases p4146_3 (m.d 0 3) (by simp) with h4160 | h4160
                                · linarith only [h1, h4160, hlam]
                                · linarith only [h3970, h4160, hlam]
                            · linarith only [h3, h4157, hlam]
                          · have p4146_0 := h4146c.1
                            have p4146_1 := h4146c.2.1
                            have p4146_2 := h4146c.2.2.1
                            have p4146_3 := h4146c.2.2.2
                            linarith only [h0, hlam, p4146_0]
                          · have p4146_0 := h4146c.1
                            have p4146_1 := h4146c.2.1
                            have p4146_2 := h4146c.2.2.1
                            have p4146_3 := h4146c.2.2.2
                            linarith only [hlam, p4146_0]
                          · have p4146_0 := h4146c.1
                            have p4146_1 := h4146c.2.1
                            have p4146_2 := h4146c.2.2.1
                            have p4146_3 := h4146c.2.2.2
                            linarith only [h4, hlam, p4146_0]
                          · have p4146_0 := h4146c.1
                            have p4146_1 := h4146c.2.1
                            have p4146_2 := h4146c.2.2.1
                            have p4146_3 := h4146c.2.2.2
                            linarith only [h3397, hlam, p4146_1]
                          · have p4146_0 := h4146c.1
                            have p4146_1 := h4146c.2.1
                            have p4146_2 := h4146c.2.2.1
                            have p4146_3 := h4146c.2.2.2
                            linarith only [h3738, hlam, p4146_0]
                          · have p4146_0 := h4146c.1
                            have p4146_1 := h4146c.2.1
                            have p4146_2 := h4146c.2.2.1
                            have p4146_3 := h4146c.2.2.2
                            linarith only [h1, hlam, p4146_1]
                          · have p4146_0 := h4146c.1
                            have p4146_1 := h4146c.2.1
                            have p4146_2 := h4146c.2.2.1
                            have p4146_3 := h4146c.2.2.2
                            linarith only [h0, h4, hc12, hc23, hlam, hphi, p4146_1]
                          · have p4146_0 := h4146c.1
                            have p4146_1 := h4146c.2.1
                            have p4146_2 := h4146c.2.2.1
                            have p4146_3 := h4146c.2.2.2
                            linarith only [hlam, p4146_0]
                          · have p4146_0 := h4146c.1
                            have p4146_1 := h4146c.2.1
                            have p4146_2 := h4146c.2.2.1
                            have p4146_3 := h4146c.2.2.2
                            linarith only [h3969, h3978, h4, h4140, h4145, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4146_1]
                          · have p4146_0 := h4146c.1
                            have p4146_1 := h4146c.2.1
                            have p4146_2 := h4146c.2.2.1
                            have p4146_3 := h4146c.2.2.2
                            linarith only [h0, h3738, h4, hc12, hc23, hlam, hphi, p4146_1]
                          · have p4146_0 := h4146c.1
                            have p4146_1 := h4146c.2.1
                            have p4146_2 := h4146c.2.2.1
                            have p4146_3 := h4146c.2.2.2
                            linarith only [h2, hlam, p4146_0]
                          · have p4146_0 := h4146c.1
                            have p4146_1 := h4146c.2.1
                            have p4146_2 := h4146c.2.2.1
                            have p4146_3 := h4146c.2.2.2
                            linarith only [h0, h3397, hc12, hc24, hlam, hphi, p4146_1]
                          · have p4146_0 := h4146c.1
                            have p4146_1 := h4146c.2.1
                            have p4146_2 := h4146c.2.2.1
                            have p4146_3 := h4146c.2.2.2
                            linarith only [h3969, hlam, p4146_0]
                          · have p4146_0 := h4146c.1
                            have p4146_1 := h4146c.2.1
                            have p4146_2 := h4146c.2.2.1
                            have p4146_3 := h4146c.2.2.2
                            linarith only [hlam, p4146_0]
                          · have p4146_0 := h4146c.1
                            have p4146_1 := h4146c.2.1
                            have p4146_2 := h4146c.2.2.1
                            have p4146_3 := h4146c.2.2.2
                            linarith only [h0, h3738, h3969, h4, hc12, hc23, hlam, hphi, p4146_1]
                          · have p4146_0 := h4146c.1
                            have p4146_1 := h4146c.2.1
                            have p4146_2 := h4146c.2.2.1
                            have p4146_3 := h4146c.2.2.2
                            linarith only [h3, hlam, p4146_0]
                          · have p4146_0 := h4146c.1
                            have p4146_1 := h4146c.2.1
                            have p4146_2 := h4146c.2.2.1
                            have p4146_3 := h4146c.2.2.2
                            linarith only [h0, h3738, hc12, hc25, hlam, hphi, p4146_1]
                          · have p4146_0 := h4146c.1
                            have p4146_1 := h4146c.2.1
                            have p4146_2 := h4146c.2.2.1
                            have p4146_3 := h4146c.2.2.2
                            linarith only [h3970, hlam, p4146_0]
                          · have p4146_0 := h4146c.1
                            have p4146_1 := h4146c.2.1
                            have p4146_2 := h4146c.2.2.1
                            have p4146_3 := h4146c.2.2.2
                            linarith only [h3971, hlam, p4146_1]
                          · have p4146_0 := h4146c.1
                            have p4146_1 := h4146c.2.1
                            have p4146_2 := h4146c.2.2.1
                            have p4146_3 := h4146c.2.2.2
                            linarith only [hlam, p4146_0]
                        · linarith only [h3969, h3971, h3978, h4, h4140, h4145, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h2, h3397, h4141, h4144, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h3978, h4, h4140, h4143, hc03, hc34, hlam, hphi]
                  · linarith only [h3969, h4, h4142, hlam]
                · linarith only [h3978, h4140, h4141, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4189 | h4189
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4190 | h4190
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4191 | h4191
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4192 | h4192
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4193 | h4193
                        · rcases h0bigk with h4194c | h4194c | h4194c | h4194c | h4194c | h4194c | h4194c | h4194c | h4194c | h4194c | h4194c | h4194c | h4194c | h4194c | h4194c | h4194c | h4194c | h4194c | h4194c | h4194c | h4194c | h4194c | h4194c | h4194c | h4194c
                          · have p4194_0 := h4194c.1
                            have p4194_1 := h4194c.2.1
                            have p4194_2 := h4194c.2.2.1
                            have p4194_3 := h4194c.2.2.2
                            linarith only [hlam, p4194_0]
                          · have p4194_0 := h4194c.1
                            have p4194_1 := h4194c.2.1
                            have p4194_2 := h4194c.2.2.1
                            have p4194_3 := h4194c.2.2.2
                            rcases p4194_3 (m.d 0 1) (by simp) with h4196 | h4196
                            · rcases p4194_3 (m.d 0 2) (by simp) with h4197 | h4197
                              · linarith only [h0, h4197, hlam]
                              · rcases p4194_3 (m.d 0 3) (by simp) with h4199 | h4199
                                · linarith only [h1, h4199, hlam]
                                · linarith only [h4, h4199, hlam]
                            · linarith only [h0, h4196, hlam]
                          · have p4194_0 := h4194c.1
                            have p4194_1 := h4194c.2.1
                            have p4194_2 := h4194c.2.2.1
                            have p4194_3 := h4194c.2.2.2
                            linarith only [h3969, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4194_1]
                          · have p4194_0 := h4194c.1
                            have p4194_1 := h4194c.2.1
                            have p4194_2 := h4194c.2.2.1
                            have p4194_3 := h4194c.2.2.2
                            linarith only [h2, h4189, hc01, hc45, hlam, hphi, ht0b, ht5b, p4194_1]
                          · have p4194_0 := h4194c.1
                            have p4194_1 := h4194c.2.1
                            have p4194_2 := h4194c.2.2.1
                            have p4194_3 := h4194c.2.2.2
                            linarith only [h3970, h4140, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4194_1]
                          · have p4194_0 := h4194c.1
                            have p4194_1 := h4194c.2.1
                            have p4194_2 := h4194c.2.2.1
                            have p4194_3 := h4194c.2.2.2
                            linarith only [h0, hlam, p4194_0]
                          · have p4194_0 := h4194c.1
                            have p4194_1 := h4194c.2.1
                            have p4194_2 := h4194c.2.2.1
                            have p4194_3 := h4194c.2.2.2
                            linarith only [hlam, p4194_0]
                          · have p4194_0 := h4194c.1
                            have p4194_1 := h4194c.2.1
                            have p4194_2 := h4194c.2.2.1
                            have p4194_3 := h4194c.2.2.2
                            linarith only [h4, hlam, p4194_0]
                          · have p4194_0 := h4194c.1
                            have p4194_1 := h4194c.2.1
                            have p4194_2 := h4194c.2.2.1
                            have p4194_3 := h4194c.2.2.2
                            linarith only [h3397, hlam, p4194_1]
                          · have p4194_0 := h4194c.1
                            have p4194_1 := h4194c.2.1
                            have p4194_2 := h4194c.2.2.1
                            have p4194_3 := h4194c.2.2.2
                            linarith only [h3738, hlam, p4194_0]
                          · have p4194_0 := h4194c.1
                            have p4194_1 := h4194c.2.1
                            have p4194_2 := h4194c.2.2.1
                            have p4194_3 := h4194c.2.2.2
                            linarith only [h1, hlam, p4194_1]
                          · have p4194_0 := h4194c.1
                            have p4194_1 := h4194c.2.1
                            have p4194_2 := h4194c.2.2.1
                            have p4194_3 := h4194c.2.2.2
                            linarith only [h0, h4, hc12, hc23, hlam, hphi, p4194_1]
                          · have p4194_0 := h4194c.1
                            have p4194_1 := h4194c.2.1
                            have p4194_2 := h4194c.2.2.1
                            have p4194_3 := h4194c.2.2.2
                            linarith only [hlam, p4194_0]
                          · have p4194_0 := h4194c.1
                            have p4194_1 := h4194c.2.1
                            have p4194_2 := h4194c.2.2.1
                            have p4194_3 := h4194c.2.2.2
                            linarith only [h2, h4, h4189, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p4194_1]
                          · have p4194_0 := h4194c.1
                            have p4194_1 := h4194c.2.1
                            have p4194_2 := h4194c.2.2.1
                            have p4194_3 := h4194c.2.2.2
                            linarith only [h3970, h4, h4140, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4194_1]
                          · have p4194_0 := h4194c.1
                            have p4194_1 := h4194c.2.1
                            have p4194_2 := h4194c.2.2.1
                            have p4194_3 := h4194c.2.2.2
                            linarith only [h2, hlam, p4194_0]
                          · have p4194_0 := h4194c.1
                            have p4194_1 := h4194c.2.1
                            have p4194_2 := h4194c.2.2.1
                            have p4194_3 := h4194c.2.2.2
                            linarith only [h0, h3397, h4190, hc12, hc23, hlam, hphi, p4194_1]
                          · have p4194_0 := h4194c.1
                            have p4194_1 := h4194c.2.1
                            have p4194_2 := h4194c.2.2.1
                            have p4194_3 := h4194c.2.2.2
                            linarith only [h3969, hlam, p4194_0]
                          · have p4194_0 := h4194c.1
                            have p4194_1 := h4194c.2.1
                            have p4194_2 := h4194c.2.2.1
                            have p4194_3 := h4194c.2.2.2
                            linarith only [hlam, p4194_0]
                          · have p4194_0 := h4194c.1
                            have p4194_1 := h4194c.2.1
                            have p4194_2 := h4194c.2.2.1
                            have p4194_3 := h4194c.2.2.2
                            linarith only [h3397, h3970, h4140, h4190, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p4194_1]
                          · have p4194_0 := h4194c.1
                            have p4194_1 := h4194c.2.1
                            have p4194_2 := h4194c.2.2.1
                            have p4194_3 := h4194c.2.2.2
                            linarith only [h3, hlam, p4194_0]
                          · have p4194_0 := h4194c.1
                            have p4194_1 := h4194c.2.1
                            have p4194_2 := h4194c.2.2.1
                            have p4194_3 := h4194c.2.2.2
                            linarith only [h0, h3738, hc12, hc25, hlam, hphi, p4194_1]
                          · have p4194_0 := h4194c.1
                            have p4194_1 := h4194c.2.1
                            have p4194_2 := h4194c.2.2.1
                            have p4194_3 := h4194c.2.2.2
                            linarith only [h3970, hlam, p4194_0]
                          · have p4194_0 := h4194c.1
                            have p4194_1 := h4194c.2.1
                            have p4194_2 := h4194c.2.2.1
                            have p4194_3 := h4194c.2.2.2
                            linarith only [h3971, hlam, p4194_1]
                          · have p4194_0 := h4194c.1
                            have p4194_1 := h4194c.2.1
                            have p4194_2 := h4194c.2.2.1
                            have p4194_3 := h4194c.2.2.2
                            linarith only [hlam, p4194_0]
                        · linarith only [h3397, h3971, h3972, h3978, h4190, h4193, hc12, hc23, hlam, hphi]
                      · linarith only [h2, h3397, h4189, h4192, hlam]
                    · linarith only [h3969, h3970, h3971, h4, h4191, hlam]
                  · linarith only [h3969, h4, h4190, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4230 | h4230
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4231 | h4231
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4232 | h4232
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4233 | h4233
                        · linarith only [h3969, h3972, h3978, h4, h4189, h4233, hc12, hc23, hlam, hphi]
                        · linarith only [h3397, h3971, h3972, h3978, h4230, h4233, hc12, hc23, hlam, hphi]
                      · linarith only [h3397, h3971, h4232, hlam]
                    · linarith only [h3970, h4, h4231, hlam]
                  · linarith only [h3969, h4, h4230, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4239 | h4239
      · linarith only [h0, h4, h4239, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4241 | h4241
        · linarith only [h0, h3397, h4241, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4243 | h4243
          · linarith only [h0, h3738, h4243, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4245 | h4245
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4246 | h4246
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4247 | h4247
                · linarith only [h2, h3971, h4247, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4249 | h4249
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4250 | h4250
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4251 | h4251
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4252 | h4252
                        · linarith only [h0, h1, h3397, h3971, h4245, h4252, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases h0bigk with h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c | h4254c
                          · have p4254_0 := h4254c.1
                            have p4254_1 := h4254c.2.1
                            have p4254_2 := h4254c.2.2.1
                            have p4254_3 := h4254c.2.2.2
                            linarith only [hlam, p4254_0]
                          · have p4254_0 := h4254c.1
                            have p4254_1 := h4254c.2.1
                            have p4254_2 := h4254c.2.2.1
                            have p4254_3 := h4254c.2.2.2
                            rcases p4254_3 (m.d 0 1) (by simp) with h4256 | h4256
                            · rcases p4254_3 (m.d 0 2) (by simp) with h4257 | h4257
                              · linarith only [h0, h4257, hlam]
                              · rcases p4254_3 (m.d 0 3) (by simp) with h4259 | h4259
                                · linarith only [h1, h4259, hlam]
                                · linarith only [h4, h4259, hlam]
                            · linarith only [h0, h4256, hlam]
                          · have p4254_0 := h4254c.1
                            have p4254_1 := h4254c.2.1
                            have p4254_2 := h4254c.2.2.1
                            have p4254_3 := h4254c.2.2.2
                            linarith only [h3969, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4254_1]
                          · have p4254_0 := h4254c.1
                            have p4254_1 := h4254c.2.1
                            have p4254_2 := h4254c.2.2.1
                            have p4254_3 := h4254c.2.2.2
                            rcases p4254_3 (m.d 0 1) (by simp) with h4264 | h4264
                            · rcases p4254_3 (m.d 0 2) (by simp) with h4265 | h4265
                              · linarith only [h0, h4265, hlam]
                              · rcases p4254_3 (m.d 0 3) (by simp) with h4267 | h4267
                                · linarith only [h1, h4267, hlam]
                                · linarith only [h3969, h4267, hlam]
                            · linarith only [h2, h4264, hlam]
                          · have p4254_0 := h4254c.1
                            have p4254_1 := h4254c.2.1
                            have p4254_2 := h4254c.2.2.1
                            have p4254_3 := h4254c.2.2.2
                            rcases p4254_3 (m.d 0 1) (by simp) with h4271 | h4271
                            · rcases p4254_3 (m.d 0 2) (by simp) with h4272 | h4272
                              · linarith only [h0, h4272, hlam]
                              · rcases p4254_3 (m.d 0 3) (by simp) with h4274 | h4274
                                · linarith only [h1, h4274, hlam]
                                · linarith only [h3970, h4274, hlam]
                            · linarith only [h3, h4271, hlam]
                          · have p4254_0 := h4254c.1
                            have p4254_1 := h4254c.2.1
                            have p4254_2 := h4254c.2.2.1
                            have p4254_3 := h4254c.2.2.2
                            linarith only [h0, hlam, p4254_0]
                          · have p4254_0 := h4254c.1
                            have p4254_1 := h4254c.2.1
                            have p4254_2 := h4254c.2.2.1
                            have p4254_3 := h4254c.2.2.2
                            linarith only [hlam, p4254_0]
                          · have p4254_0 := h4254c.1
                            have p4254_1 := h4254c.2.1
                            have p4254_2 := h4254c.2.2.1
                            have p4254_3 := h4254c.2.2.2
                            linarith only [h4, hlam, p4254_0]
                          · have p4254_0 := h4254c.1
                            have p4254_1 := h4254c.2.1
                            have p4254_2 := h4254c.2.2.1
                            have p4254_3 := h4254c.2.2.2
                            linarith only [h3397, hlam, p4254_1]
                          · have p4254_0 := h4254c.1
                            have p4254_1 := h4254c.2.1
                            have p4254_2 := h4254c.2.2.1
                            have p4254_3 := h4254c.2.2.2
                            linarith only [h3738, hlam, p4254_0]
                          · have p4254_0 := h4254c.1
                            have p4254_1 := h4254c.2.1
                            have p4254_2 := h4254c.2.2.1
                            have p4254_3 := h4254c.2.2.2
                            linarith only [h1, hlam, p4254_1]
                          · have p4254_0 := h4254c.1
                            have p4254_1 := h4254c.2.1
                            have p4254_2 := h4254c.2.2.1
                            have p4254_3 := h4254c.2.2.2
                            linarith only [h0, h4, hc12, hc23, hlam, hphi, p4254_1]
                          · have p4254_0 := h4254c.1
                            have p4254_1 := h4254c.2.1
                            have p4254_2 := h4254c.2.2.1
                            have p4254_3 := h4254c.2.2.2
                            linarith only [hlam, p4254_0]
                          · have p4254_0 := h4254c.1
                            have p4254_1 := h4254c.2.1
                            have p4254_2 := h4254c.2.2.1
                            have p4254_3 := h4254c.2.2.2
                            linarith only [h0, h3397, h4, hc12, hc23, hlam, hphi, p4254_1]
                          · have p4254_0 := h4254c.1
                            have p4254_1 := h4254c.2.1
                            have p4254_2 := h4254c.2.2.1
                            have p4254_3 := h4254c.2.2.2
                            linarith only [h0, h3738, h4, hc12, hc23, hlam, hphi, p4254_1]
                          · have p4254_0 := h4254c.1
                            have p4254_1 := h4254c.2.1
                            have p4254_2 := h4254c.2.2.1
                            have p4254_3 := h4254c.2.2.2
                            linarith only [h2, hlam, p4254_0]
                          · have p4254_0 := h4254c.1
                            have p4254_1 := h4254c.2.1
                            have p4254_2 := h4254c.2.2.1
                            have p4254_3 := h4254c.2.2.2
                            linarith only [h0, h3971, h4251, hc12, hc25, hlam, hphi, p4254_1]
                          · have p4254_0 := h4254c.1
                            have p4254_1 := h4254c.2.1
                            have p4254_2 := h4254c.2.2.1
                            have p4254_3 := h4254c.2.2.2
                            linarith only [h3969, hlam, p4254_0]
                          · have p4254_0 := h4254c.1
                            have p4254_1 := h4254c.2.1
                            have p4254_2 := h4254c.2.2.1
                            have p4254_3 := h4254c.2.2.2
                            linarith only [hlam, p4254_0]
                          · have p4254_0 := h4254c.1
                            have p4254_1 := h4254c.2.1
                            have p4254_2 := h4254c.2.2.1
                            have p4254_3 := h4254c.2.2.2
                            linarith only [h3971, hlam, p4254_0]
                          · have p4254_0 := h4254c.1
                            have p4254_1 := h4254c.2.1
                            have p4254_2 := h4254c.2.2.1
                            have p4254_3 := h4254c.2.2.2
                            linarith only [h3, hlam, p4254_0]
                          · have p4254_0 := h4254c.1
                            have p4254_1 := h4254c.2.1
                            have p4254_2 := h4254c.2.2.1
                            have p4254_3 := h4254c.2.2.2
                            linarith only [h0, h3738, hc12, hc25, hlam, hphi, p4254_1]
                          · have p4254_0 := h4254c.1
                            have p4254_1 := h4254c.2.1
                            have p4254_2 := h4254c.2.2.1
                            have p4254_3 := h4254c.2.2.2
                            linarith only [h3970, hlam, p4254_0]
                          · have p4254_0 := h4254c.1
                            have p4254_1 := h4254c.2.1
                            have p4254_2 := h4254c.2.2.1
                            have p4254_3 := h4254c.2.2.2
                            linarith only [h3971, hc04, hc45, hlam, hphi, p4254_1]
                          · have p4254_0 := h4254c.1
                            have p4254_1 := h4254c.2.1
                            have p4254_2 := h4254c.2.2.1
                            have p4254_3 := h4254c.2.2.2
                            linarith only [hlam, p4254_0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4298 | h4298
                        · linarith only [h0, h3397, h4251, h4298, hc12, hc34, hlam, hphi, ht23]
                        · rcases h0bigk with h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c | h4300c
                          · have p4300_0 := h4300c.1
                            have p4300_1 := h4300c.2.1
                            have p4300_2 := h4300c.2.2.1
                            have p4300_3 := h4300c.2.2.2
                            linarith only [hlam, p4300_0]
                          · have p4300_0 := h4300c.1
                            have p4300_1 := h4300c.2.1
                            have p4300_2 := h4300c.2.2.1
                            have p4300_3 := h4300c.2.2.2
                            rcases p4300_3 (m.d 0 1) (by simp) with h4302 | h4302
                            · rcases p4300_3 (m.d 0 2) (by simp) with h4303 | h4303
                              · linarith only [h0, h4303, hlam]
                              · rcases p4300_3 (m.d 0 3) (by simp) with h4305 | h4305
                                · linarith only [h1, h4305, hlam]
                                · linarith only [h4, h4305, hlam]
                            · linarith only [h0, h4302, hlam]
                          · have p4300_0 := h4300c.1
                            have p4300_1 := h4300c.2.1
                            have p4300_2 := h4300c.2.2.1
                            have p4300_3 := h4300c.2.2.2
                            linarith only [h1, h4246, hc01, hc35, hlam, hphi, ht0b, ht5b, p4300_1]
                          · have p4300_0 := h4300c.1
                            have p4300_1 := h4300c.2.1
                            have p4300_2 := h4300c.2.2.1
                            have p4300_3 := h4300c.2.2.2
                            rcases p4300_3 (m.d 0 1) (by simp) with h4310 | h4310
                            · rcases p4300_3 (m.d 0 2) (by simp) with h4311 | h4311
                              · linarith only [h0, h4311, hlam]
                              · rcases p4300_3 (m.d 0 3) (by simp) with h4313 | h4313
                                · linarith only [h1, h4313, hlam]
                                · linarith only [h3969, h4313, hlam]
                            · linarith only [h2, h4310, hlam]
                          · have p4300_0 := h4300c.1
                            have p4300_1 := h4300c.2.1
                            have p4300_2 := h4300c.2.2.1
                            have p4300_3 := h4300c.2.2.2
                            rcases p4300_3 (m.d 0 1) (by simp) with h4317 | h4317
                            · rcases p4300_3 (m.d 0 2) (by simp) with h4318 | h4318
                              · linarith only [h0, h4318, hlam]
                              · rcases p4300_3 (m.d 0 3) (by simp) with h4320 | h4320
                                · linarith only [h1, h4320, hlam]
                                · linarith only [h3970, h4320, hlam]
                            · linarith only [h3, h4317, hlam]
                          · have p4300_0 := h4300c.1
                            have p4300_1 := h4300c.2.1
                            have p4300_2 := h4300c.2.2.1
                            have p4300_3 := h4300c.2.2.2
                            linarith only [h0, hlam, p4300_0]
                          · have p4300_0 := h4300c.1
                            have p4300_1 := h4300c.2.1
                            have p4300_2 := h4300c.2.2.1
                            have p4300_3 := h4300c.2.2.2
                            linarith only [hlam, p4300_0]
                          · have p4300_0 := h4300c.1
                            have p4300_1 := h4300c.2.1
                            have p4300_2 := h4300c.2.2.1
                            have p4300_3 := h4300c.2.2.2
                            linarith only [h4, hlam, p4300_0]
                          · have p4300_0 := h4300c.1
                            have p4300_1 := h4300c.2.1
                            have p4300_2 := h4300c.2.2.1
                            have p4300_3 := h4300c.2.2.2
                            linarith only [h3397, hlam, p4300_1]
                          · have p4300_0 := h4300c.1
                            have p4300_1 := h4300c.2.1
                            have p4300_2 := h4300c.2.2.1
                            have p4300_3 := h4300c.2.2.2
                            linarith only [h3738, hlam, p4300_0]
                          · have p4300_0 := h4300c.1
                            have p4300_1 := h4300c.2.1
                            have p4300_2 := h4300c.2.2.1
                            have p4300_3 := h4300c.2.2.2
                            linarith only [h1, hlam, p4300_1]
                          · have p4300_0 := h4300c.1
                            have p4300_1 := h4300c.2.1
                            have p4300_2 := h4300c.2.2.1
                            have p4300_3 := h4300c.2.2.2
                            linarith only [h0, h4, hc12, hc23, hlam, hphi, p4300_1]
                          · have p4300_0 := h4300c.1
                            have p4300_1 := h4300c.2.1
                            have p4300_2 := h4300c.2.2.1
                            have p4300_3 := h4300c.2.2.2
                            linarith only [hlam, p4300_0]
                          · have p4300_0 := h4300c.1
                            have p4300_1 := h4300c.2.1
                            have p4300_2 := h4300c.2.2.1
                            have p4300_3 := h4300c.2.2.2
                            linarith only [h2, h4, h4241, hc12, hc23, hlam, hphi, p4300_1]
                          · have p4300_0 := h4300c.1
                            have p4300_1 := h4300c.2.1
                            have p4300_2 := h4300c.2.2.1
                            have p4300_3 := h4300c.2.2.2
                            linarith only [h2, h3971, h4, h4241, hc12, hc23, hlam, hphi, p4300_1]
                          · have p4300_0 := h4300c.1
                            have p4300_1 := h4300c.2.1
                            have p4300_2 := h4300c.2.2.1
                            have p4300_3 := h4300c.2.2.2
                            linarith only [h2, hlam, p4300_0]
                          · have p4300_0 := h4300c.1
                            have p4300_1 := h4300c.2.1
                            have p4300_2 := h4300c.2.2.1
                            have p4300_3 := h4300c.2.2.2
                            linarith only [h0, h3397, h4251, hc12, hc45, hlam, hphi, ht23, ht34, p4300_1]
                          · have p4300_0 := h4300c.1
                            have p4300_1 := h4300c.2.1
                            have p4300_2 := h4300c.2.2.1
                            have p4300_3 := h4300c.2.2.2
                            linarith only [h3969, hlam, p4300_0]
                          · have p4300_0 := h4300c.1
                            have p4300_1 := h4300c.2.1
                            have p4300_2 := h4300c.2.2.1
                            have p4300_3 := h4300c.2.2.2
                            linarith only [hlam, p4300_0]
                          · have p4300_0 := h4300c.1
                            have p4300_1 := h4300c.2.1
                            have p4300_2 := h4300c.2.2.1
                            have p4300_3 := h4300c.2.2.2
                            linarith only [h3971, hlam, p4300_0]
                          · have p4300_0 := h4300c.1
                            have p4300_1 := h4300c.2.1
                            have p4300_2 := h4300c.2.2.1
                            have p4300_3 := h4300c.2.2.2
                            linarith only [h3, hlam, p4300_0]
                          · have p4300_0 := h4300c.1
                            have p4300_1 := h4300c.2.1
                            have p4300_2 := h4300c.2.2.1
                            have p4300_3 := h4300c.2.2.2
                            linarith only [h0, h3738, hc12, hc25, hlam, hphi, p4300_1]
                          · have p4300_0 := h4300c.1
                            have p4300_1 := h4300c.2.1
                            have p4300_2 := h4300c.2.2.1
                            have p4300_3 := h4300c.2.2.2
                            linarith only [h3970, hlam, p4300_0]
                          · have p4300_0 := h4300c.1
                            have p4300_1 := h4300c.2.1
                            have p4300_2 := h4300c.2.2.1
                            have p4300_3 := h4300c.2.2.2
                            linarith only [h3971, hc04, hc45, hlam, hphi, p4300_1]
                          · have p4300_0 := h4300c.1
                            have p4300_1 := h4300c.2.1
                            have p4300_2 := h4300c.2.2.1
                            have p4300_3 := h4300c.2.2.2
                            linarith only [hlam, p4300_0]
                    · linarith only [h1, h4, h4246, h4250, hlam]
                  · linarith only [h1, h4, h4245, h4249, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4346 | h4346
                · linarith only [h2, h3971, h4346, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4348 | h4348
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4349 | h4349
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4350 | h4350
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4351 | h4351
                        · linarith only [h3970, h3971, h4245, h4246, h4351, hc04, hc05, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h0bigk with h4353c | h4353c | h4353c | h4353c | h4353c | h4353c | h4353c | h4353c | h4353c | h4353c | h4353c | h4353c | h4353c | h4353c | h4353c | h4353c | h4353c | h4353c | h4353c | h4353c | h4353c | h4353c | h4353c | h4353c | h4353c
                          · have p4353_0 := h4353c.1
                            have p4353_1 := h4353c.2.1
                            have p4353_2 := h4353c.2.2.1
                            have p4353_3 := h4353c.2.2.2
                            linarith only [hlam, p4353_0]
                          · have p4353_0 := h4353c.1
                            have p4353_1 := h4353c.2.1
                            have p4353_2 := h4353c.2.2.1
                            have p4353_3 := h4353c.2.2.2
                            rcases p4353_3 (m.d 0 1) (by simp) with h4355 | h4355
                            · rcases p4353_3 (m.d 0 2) (by simp) with h4356 | h4356
                              · linarith only [h0, h4356, hlam]
                              · rcases p4353_3 (m.d 0 3) (by simp) with h4358 | h4358
                                · linarith only [h1, h4358, hlam]
                                · linarith only [h4, h4358, hlam]
                            · linarith only [h0, h4355, hlam]
                          · have p4353_0 := h4353c.1
                            have p4353_1 := h4353c.2.1
                            have p4353_2 := h4353c.2.2.1
                            have p4353_3 := h4353c.2.2.2
                            linarith only [h1, h4245, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4353_1]
                          · have p4353_0 := h4353c.1
                            have p4353_1 := h4353c.2.1
                            have p4353_2 := h4353c.2.2.1
                            have p4353_3 := h4353c.2.2.2
                            rcases p4353_3 (m.d 0 1) (by simp) with h4363 | h4363
                            · rcases p4353_3 (m.d 0 2) (by simp) with h4364 | h4364
                              · linarith only [h0, h4364, hlam]
                              · rcases p4353_3 (m.d 0 3) (by simp) with h4366 | h4366
                                · linarith only [h1, h4366, hlam]
                                · linarith only [h3969, h4366, hlam]
                            · linarith only [h2, h4363, hlam]
                          · have p4353_0 := h4353c.1
                            have p4353_1 := h4353c.2.1
                            have p4353_2 := h4353c.2.2.1
                            have p4353_3 := h4353c.2.2.2
                            linarith only [h3970, h4245, h4246, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4353_1]
                          · have p4353_0 := h4353c.1
                            have p4353_1 := h4353c.2.1
                            have p4353_2 := h4353c.2.2.1
                            have p4353_3 := h4353c.2.2.2
                            linarith only [h0, hlam, p4353_0]
                          · have p4353_0 := h4353c.1
                            have p4353_1 := h4353c.2.1
                            have p4353_2 := h4353c.2.2.1
                            have p4353_3 := h4353c.2.2.2
                            linarith only [hlam, p4353_0]
                          · have p4353_0 := h4353c.1
                            have p4353_1 := h4353c.2.1
                            have p4353_2 := h4353c.2.2.1
                            have p4353_3 := h4353c.2.2.2
                            linarith only [h4, hlam, p4353_0]
                          · have p4353_0 := h4353c.1
                            have p4353_1 := h4353c.2.1
                            have p4353_2 := h4353c.2.2.1
                            have p4353_3 := h4353c.2.2.2
                            linarith only [h3397, hlam, p4353_1]
                          · have p4353_0 := h4353c.1
                            have p4353_1 := h4353c.2.1
                            have p4353_2 := h4353c.2.2.1
                            have p4353_3 := h4353c.2.2.2
                            linarith only [h3738, hlam, p4353_0]
                          · have p4353_0 := h4353c.1
                            have p4353_1 := h4353c.2.1
                            have p4353_2 := h4353c.2.2.1
                            have p4353_3 := h4353c.2.2.2
                            linarith only [h1, hlam, p4353_1]
                          · have p4353_0 := h4353c.1
                            have p4353_1 := h4353c.2.1
                            have p4353_2 := h4353c.2.2.1
                            have p4353_3 := h4353c.2.2.2
                            linarith only [h0, h4, hc12, hc23, hlam, hphi, p4353_1]
                          · have p4353_0 := h4353c.1
                            have p4353_1 := h4353c.2.1
                            have p4353_2 := h4353c.2.2.1
                            have p4353_3 := h4353c.2.2.2
                            linarith only [hlam, p4353_0]
                          · have p4353_0 := h4353c.1
                            have p4353_1 := h4353c.2.1
                            have p4353_2 := h4353c.2.2.1
                            have p4353_3 := h4353c.2.2.2
                            linarith only [h0, h3397, h4, hc12, hc23, hlam, hphi, p4353_1]
                          · have p4353_0 := h4353c.1
                            have p4353_1 := h4353c.2.1
                            have p4353_2 := h4353c.2.2.1
                            have p4353_3 := h4353c.2.2.2
                            linarith only [h3970, h4, h4245, h4246, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4353_1]
                          · have p4353_0 := h4353c.1
                            have p4353_1 := h4353c.2.1
                            have p4353_2 := h4353c.2.2.1
                            have p4353_3 := h4353c.2.2.2
                            linarith only [h2, hlam, p4353_0]
                          · have p4353_0 := h4353c.1
                            have p4353_1 := h4353c.2.1
                            have p4353_2 := h4353c.2.2.1
                            have p4353_3 := h4353c.2.2.2
                            linarith only [h0, h3397, h4348, hc12, hc23, hlam, hphi, p4353_1]
                          · have p4353_0 := h4353c.1
                            have p4353_1 := h4353c.2.1
                            have p4353_2 := h4353c.2.2.1
                            have p4353_3 := h4353c.2.2.2
                            linarith only [h3969, hlam, p4353_0]
                          · have p4353_0 := h4353c.1
                            have p4353_1 := h4353c.2.1
                            have p4353_2 := h4353c.2.2.1
                            have p4353_3 := h4353c.2.2.2
                            linarith only [hlam, p4353_0]
                          · have p4353_0 := h4353c.1
                            have p4353_1 := h4353c.2.1
                            have p4353_2 := h4353c.2.2.1
                            have p4353_3 := h4353c.2.2.2
                            linarith only [h3971, hlam, p4353_0]
                          · have p4353_0 := h4353c.1
                            have p4353_1 := h4353c.2.1
                            have p4353_2 := h4353c.2.2.1
                            have p4353_3 := h4353c.2.2.2
                            linarith only [h3, hlam, p4353_0]
                          · have p4353_0 := h4353c.1
                            have p4353_1 := h4353c.2.1
                            have p4353_2 := h4353c.2.2.1
                            have p4353_3 := h4353c.2.2.2
                            linarith only [h0, h3738, h4348, h4350, hc12, hc23, hlam, hphi, p4353_1]
                          · have p4353_0 := h4353c.1
                            have p4353_1 := h4353c.2.1
                            have p4353_2 := h4353c.2.2.1
                            have p4353_3 := h4353c.2.2.2
                            linarith only [h3970, hlam, p4353_0]
                          · have p4353_0 := h4353c.1
                            have p4353_1 := h4353c.2.1
                            have p4353_2 := h4353c.2.2.1
                            have p4353_3 := h4353c.2.2.2
                            linarith only [h3971, h4348, h4350, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4353_1]
                          · have p4353_0 := h4353c.1
                            have p4353_1 := h4353c.2.1
                            have p4353_2 := h4353c.2.2.1
                            have p4353_3 := h4353c.2.2.2
                            linarith only [hlam, p4353_0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4391 | h4391
                        · linarith only [h1, h3970, h4245, h4246, h4350, h4391, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h0bigk with h4393c | h4393c | h4393c | h4393c | h4393c | h4393c | h4393c | h4393c | h4393c | h4393c | h4393c | h4393c | h4393c | h4393c | h4393c | h4393c | h4393c | h4393c | h4393c | h4393c | h4393c | h4393c | h4393c | h4393c | h4393c
                          · have p4393_0 := h4393c.1
                            have p4393_1 := h4393c.2.1
                            have p4393_2 := h4393c.2.2.1
                            have p4393_3 := h4393c.2.2.2
                            linarith only [hlam, p4393_0]
                          · have p4393_0 := h4393c.1
                            have p4393_1 := h4393c.2.1
                            have p4393_2 := h4393c.2.2.1
                            have p4393_3 := h4393c.2.2.2
                            rcases p4393_3 (m.d 0 1) (by simp) with h4395 | h4395
                            · rcases p4393_3 (m.d 0 2) (by simp) with h4396 | h4396
                              · linarith only [h0, h4396, hlam]
                              · rcases p4393_3 (m.d 0 3) (by simp) with h4398 | h4398
                                · linarith only [h1, h4398, hlam]
                                · linarith only [h4, h4398, hlam]
                            · linarith only [h0, h4395, hlam]
                          · have p4393_0 := h4393c.1
                            have p4393_1 := h4393c.2.1
                            have p4393_2 := h4393c.2.2.1
                            have p4393_3 := h4393c.2.2.2
                            linarith only [h3970, h4246, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4393_1]
                          · have p4393_0 := h4393c.1
                            have p4393_1 := h4393c.2.1
                            have p4393_2 := h4393c.2.2.1
                            have p4393_3 := h4393c.2.2.2
                            rcases p4393_3 (m.d 0 1) (by simp) with h4403 | h4403
                            · rcases p4393_3 (m.d 0 2) (by simp) with h4404 | h4404
                              · linarith only [h0, h4404, hlam]
                              · rcases p4393_3 (m.d 0 3) (by simp) with h4406 | h4406
                                · linarith only [h1, h4406, hlam]
                                · linarith only [h3969, h4406, hlam]
                            · linarith only [h2, h4403, hlam]
                          · have p4393_0 := h4393c.1
                            have p4393_1 := h4393c.2.1
                            have p4393_2 := h4393c.2.2.1
                            have p4393_3 := h4393c.2.2.2
                            linarith only [h3, h4245, h4246, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4393_1]
                          · have p4393_0 := h4393c.1
                            have p4393_1 := h4393c.2.1
                            have p4393_2 := h4393c.2.2.1
                            have p4393_3 := h4393c.2.2.2
                            linarith only [h0, hlam, p4393_0]
                          · have p4393_0 := h4393c.1
                            have p4393_1 := h4393c.2.1
                            have p4393_2 := h4393c.2.2.1
                            have p4393_3 := h4393c.2.2.2
                            linarith only [hlam, p4393_0]
                          · have p4393_0 := h4393c.1
                            have p4393_1 := h4393c.2.1
                            have p4393_2 := h4393c.2.2.1
                            have p4393_3 := h4393c.2.2.2
                            linarith only [h4, hlam, p4393_0]
                          · have p4393_0 := h4393c.1
                            have p4393_1 := h4393c.2.1
                            have p4393_2 := h4393c.2.2.1
                            have p4393_3 := h4393c.2.2.2
                            linarith only [h3397, hlam, p4393_1]
                          · have p4393_0 := h4393c.1
                            have p4393_1 := h4393c.2.1
                            have p4393_2 := h4393c.2.2.1
                            have p4393_3 := h4393c.2.2.2
                            linarith only [h3738, hlam, p4393_0]
                          · have p4393_0 := h4393c.1
                            have p4393_1 := h4393c.2.1
                            have p4393_2 := h4393c.2.2.1
                            have p4393_3 := h4393c.2.2.2
                            linarith only [h1, hlam, p4393_1]
                          · have p4393_0 := h4393c.1
                            have p4393_1 := h4393c.2.1
                            have p4393_2 := h4393c.2.2.1
                            have p4393_3 := h4393c.2.2.2
                            linarith only [h0, h4, hc12, hc23, hlam, hphi, p4393_1]
                          · have p4393_0 := h4393c.1
                            have p4393_1 := h4393c.2.1
                            have p4393_2 := h4393c.2.2.1
                            have p4393_3 := h4393c.2.2.2
                            linarith only [hlam, p4393_0]
                          · have p4393_0 := h4393c.1
                            have p4393_1 := h4393c.2.1
                            have p4393_2 := h4393c.2.2.1
                            have p4393_3 := h4393c.2.2.2
                            linarith only [h2, h4, h4241, hc12, hc23, hlam, hphi, p4393_1]
                          · have p4393_0 := h4393c.1
                            have p4393_1 := h4393c.2.1
                            have p4393_2 := h4393c.2.2.1
                            have p4393_3 := h4393c.2.2.2
                            linarith only [h3, h4, h4245, h4246, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4393_1]
                          · have p4393_0 := h4393c.1
                            have p4393_1 := h4393c.2.1
                            have p4393_2 := h4393c.2.2.1
                            have p4393_3 := h4393c.2.2.2
                            linarith only [h2, hlam, p4393_0]
                          · have p4393_0 := h4393c.1
                            have p4393_1 := h4393c.2.1
                            have p4393_2 := h4393c.2.2.1
                            have p4393_3 := h4393c.2.2.2
                            linarith only [h0, h3397, hc12, hc24, hlam, hphi, p4393_1]
                          · have p4393_0 := h4393c.1
                            have p4393_1 := h4393c.2.1
                            have p4393_2 := h4393c.2.2.1
                            have p4393_3 := h4393c.2.2.2
                            linarith only [h3969, hlam, p4393_0]
                          · have p4393_0 := h4393c.1
                            have p4393_1 := h4393c.2.1
                            have p4393_2 := h4393c.2.2.1
                            have p4393_3 := h4393c.2.2.2
                            linarith only [hlam, p4393_0]
                          · have p4393_0 := h4393c.1
                            have p4393_1 := h4393c.2.1
                            have p4393_2 := h4393c.2.2.1
                            have p4393_3 := h4393c.2.2.2
                            linarith only [h3971, hlam, p4393_0]
                          · have p4393_0 := h4393c.1
                            have p4393_1 := h4393c.2.1
                            have p4393_2 := h4393c.2.2.1
                            have p4393_3 := h4393c.2.2.2
                            linarith only [h3, hlam, p4393_0]
                          · have p4393_0 := h4393c.1
                            have p4393_1 := h4393c.2.1
                            have p4393_2 := h4393c.2.2.1
                            have p4393_3 := h4393c.2.2.2
                            linarith only [h0, h3738, hc12, hc25, hlam, hphi, p4393_1]
                          · have p4393_0 := h4393c.1
                            have p4393_1 := h4393c.2.1
                            have p4393_2 := h4393c.2.2.1
                            have p4393_3 := h4393c.2.2.2
                            linarith only [h3970, hlam, p4393_0]
                          · have p4393_0 := h4393c.1
                            have p4393_1 := h4393c.2.1
                            have p4393_2 := h4393c.2.2.1
                            have p4393_3 := h4393c.2.2.2
                            linarith only [h3971, hc04, hc45, hlam, hphi, p4393_1]
                          · have p4393_0 := h4393c.1
                            have p4393_1 := h4393c.2.1
                            have p4393_2 := h4393c.2.2.1
                            have p4393_3 := h4393c.2.2.2
                            linarith only [hlam, p4393_0]
                    · linarith only [h3970, h4, h4349, hlam]
                  · linarith only [h3970, h4, h4245, h4246, h4348, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4433 | h4433
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4434 | h4434
                · linarith only [h3969, h3971, h4245, h4433, h4434, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h4245, h4433, h4434, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4437 | h4437
                · linarith only [h2, h3971, h4437, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4439 | h4439
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4440 | h4440
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4441 | h4441
                      · linarith only [h3969, h3971, h4239, h4245, h4441, hc12, hc24, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4443 | h4443
                        · linarith only [h0, h3397, h4441, h4443, hc12, hc34, hlam, hphi, ht23]
                        · rcases h0bigk with h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c | h4445c
                          · have p4445_0 := h4445c.1
                            have p4445_1 := h4445c.2.1
                            have p4445_2 := h4445c.2.2.1
                            have p4445_3 := h4445c.2.2.2
                            linarith only [hlam, p4445_0]
                          · have p4445_0 := h4445c.1
                            have p4445_1 := h4445c.2.1
                            have p4445_2 := h4445c.2.2.1
                            have p4445_3 := h4445c.2.2.2
                            rcases p4445_3 (m.d 0 1) (by simp) with h4447 | h4447
                            · rcases p4445_3 (m.d 0 2) (by simp) with h4448 | h4448
                              · linarith only [h0, h4448, hlam]
                              · rcases p4445_3 (m.d 0 3) (by simp) with h4450 | h4450
                                · linarith only [h1, h4450, hlam]
                                · linarith only [h4, h4450, hlam]
                            · linarith only [h0, h4447, hlam]
                          · have p4445_0 := h4445c.1
                            have p4445_1 := h4445c.2.1
                            have p4445_2 := h4445c.2.2.1
                            have p4445_3 := h4445c.2.2.2
                            linarith only [h3970, hc01, hc35, hlam, hphi, ht0b, ht5b, p4445_1]
                          · have p4445_0 := h4445c.1
                            have p4445_1 := h4445c.2.1
                            have p4445_2 := h4445c.2.2.1
                            have p4445_3 := h4445c.2.2.2
                            linarith only [h3969, h4239, h4245, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4445_1]
                          · have p4445_0 := h4445c.1
                            have p4445_1 := h4445c.2.1
                            have p4445_2 := h4445c.2.2.1
                            have p4445_3 := h4445c.2.2.2
                            linarith only [h3969, h3971, h4239, h4245, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4445_1]
                          · have p4445_0 := h4445c.1
                            have p4445_1 := h4445c.2.1
                            have p4445_2 := h4445c.2.2.1
                            have p4445_3 := h4445c.2.2.2
                            linarith only [h0, hlam, p4445_0]
                          · have p4445_0 := h4445c.1
                            have p4445_1 := h4445c.2.1
                            have p4445_2 := h4445c.2.2.1
                            have p4445_3 := h4445c.2.2.2
                            linarith only [hlam, p4445_0]
                          · have p4445_0 := h4445c.1
                            have p4445_1 := h4445c.2.1
                            have p4445_2 := h4445c.2.2.1
                            have p4445_3 := h4445c.2.2.2
                            linarith only [h4, hlam, p4445_0]
                          · have p4445_0 := h4445c.1
                            have p4445_1 := h4445c.2.1
                            have p4445_2 := h4445c.2.2.1
                            have p4445_3 := h4445c.2.2.2
                            linarith only [h3397, hlam, p4445_1]
                          · have p4445_0 := h4445c.1
                            have p4445_1 := h4445c.2.1
                            have p4445_2 := h4445c.2.2.1
                            have p4445_3 := h4445c.2.2.2
                            linarith only [h3738, hlam, p4445_0]
                          · have p4445_0 := h4445c.1
                            have p4445_1 := h4445c.2.1
                            have p4445_2 := h4445c.2.2.1
                            have p4445_3 := h4445c.2.2.2
                            linarith only [h1, hlam, p4445_1]
                          · have p4445_0 := h4445c.1
                            have p4445_1 := h4445c.2.1
                            have p4445_2 := h4445c.2.2.1
                            have p4445_3 := h4445c.2.2.2
                            linarith only [h0, h4, hc12, hc23, hlam, hphi, p4445_1]
                          · have p4445_0 := h4445c.1
                            have p4445_1 := h4445c.2.1
                            have p4445_2 := h4445c.2.2.1
                            have p4445_3 := h4445c.2.2.2
                            linarith only [hlam, p4445_0]
                          · have p4445_0 := h4445c.1
                            have p4445_1 := h4445c.2.1
                            have p4445_2 := h4445c.2.2.1
                            have p4445_3 := h4445c.2.2.2
                            linarith only [h3969, h4, h4239, h4245, hc12, hc23, hlam, hphi, p4445_1]
                          · have p4445_0 := h4445c.1
                            have p4445_1 := h4445c.2.1
                            have p4445_2 := h4445c.2.2.1
                            have p4445_3 := h4445c.2.2.2
                            linarith only [h3969, h3971, h4, h4239, h4245, hc12, hc23, hlam, hphi, p4445_1]
                          · have p4445_0 := h4445c.1
                            have p4445_1 := h4445c.2.1
                            have p4445_2 := h4445c.2.2.1
                            have p4445_3 := h4445c.2.2.2
                            linarith only [h2, hlam, p4445_0]
                          · have p4445_0 := h4445c.1
                            have p4445_1 := h4445c.2.1
                            have p4445_2 := h4445c.2.2.1
                            have p4445_3 := h4445c.2.2.2
                            linarith only [h0, h3397, hc12, hc24, hlam, hphi, p4445_1]
                          · have p4445_0 := h4445c.1
                            have p4445_1 := h4445c.2.1
                            have p4445_2 := h4445c.2.2.1
                            have p4445_3 := h4445c.2.2.2
                            linarith only [h3969, hlam, p4445_0]
                          · have p4445_0 := h4445c.1
                            have p4445_1 := h4445c.2.1
                            have p4445_2 := h4445c.2.2.1
                            have p4445_3 := h4445c.2.2.2
                            linarith only [hlam, p4445_0]
                          · have p4445_0 := h4445c.1
                            have p4445_1 := h4445c.2.1
                            have p4445_2 := h4445c.2.2.1
                            have p4445_3 := h4445c.2.2.2
                            linarith only [h3971, hlam, p4445_0]
                          · have p4445_0 := h4445c.1
                            have p4445_1 := h4445c.2.1
                            have p4445_2 := h4445c.2.2.1
                            have p4445_3 := h4445c.2.2.2
                            linarith only [h3, hlam, p4445_0]
                          · have p4445_0 := h4445c.1
                            have p4445_1 := h4445c.2.1
                            have p4445_2 := h4445c.2.2.1
                            have p4445_3 := h4445c.2.2.2
                            linarith only [h0, h3738, hc12, hc25, hlam, hphi, p4445_1]
                          · have p4445_0 := h4445c.1
                            have p4445_1 := h4445c.2.1
                            have p4445_2 := h4445c.2.2.1
                            have p4445_3 := h4445c.2.2.2
                            linarith only [h3970, hlam, p4445_0]
                          · have p4445_0 := h4445c.1
                            have p4445_1 := h4445c.2.1
                            have p4445_2 := h4445c.2.2.1
                            have p4445_3 := h4445c.2.2.2
                            linarith only [h3971, hc04, hc45, hlam, hphi, p4445_1]
                          · have p4445_0 := h4445c.1
                            have p4445_1 := h4445c.2.1
                            have p4445_2 := h4445c.2.2.1
                            have p4445_3 := h4445c.2.2.2
                            linarith only [hlam, p4445_0]
                    · linarith only [h3969, h4, h4239, h4245, h4440, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h3969, h4, h4439, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4479 | h4479
    · linarith only [h3969, h3970, h4479, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4481 | h4481
      · linarith only [h0, h4, h4481, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4483 | h4483
        · linarith only [h0, h3397, h4483, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4485 | h4485
          · linarith only [h0, h3738, h4485, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4487 | h4487
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4488 | h4488
              · linarith only [h1, h3970, h4488, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4490 | h4490
                · linarith only [h2, h4479, h4490, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4492 | h4492
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4493 | h4493
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4494 | h4494
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4495 | h4495
                        · linarith only [h3, h4479, h4487, h4488, h4495, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h0bigk with h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c | h4497c
                          · have p4497_0 := h4497c.1
                            have p4497_1 := h4497c.2.1
                            have p4497_2 := h4497c.2.2.1
                            have p4497_3 := h4497c.2.2.2
                            linarith only [hlam, p4497_0]
                          · have p4497_0 := h4497c.1
                            have p4497_1 := h4497c.2.1
                            have p4497_2 := h4497c.2.2.1
                            have p4497_3 := h4497c.2.2.2
                            rcases p4497_3 (m.d 0 1) (by simp) with h4499 | h4499
                            · rcases p4497_3 (m.d 0 2) (by simp) with h4500 | h4500
                              · linarith only [h0, h4500, hlam]
                              · rcases p4497_3 (m.d 0 3) (by simp) with h4502 | h4502
                                · linarith only [h1, h4502, hlam]
                                · linarith only [h4, h4502, hlam]
                            · linarith only [h0, h4499, hlam]
                          · have p4497_0 := h4497c.1
                            have p4497_1 := h4497c.2.1
                            have p4497_2 := h4497c.2.2.1
                            have p4497_3 := h4497c.2.2.2
                            linarith only [h1, h4487, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4497_1]
                          · have p4497_0 := h4497c.1
                            have p4497_1 := h4497c.2.1
                            have p4497_2 := h4497c.2.2.1
                            have p4497_3 := h4497c.2.2.2
                            rcases p4497_3 (m.d 0 1) (by simp) with h4507 | h4507
                            · rcases p4497_3 (m.d 0 2) (by simp) with h4508 | h4508
                              · linarith only [h0, h4508, hlam]
                              · rcases p4497_3 (m.d 0 3) (by simp) with h4510 | h4510
                                · linarith only [h1, h4510, hlam]
                                · linarith only [h3969, h4510, hlam]
                            · linarith only [h2, h4507, hlam]
                          · have p4497_0 := h4497c.1
                            have p4497_1 := h4497c.2.1
                            have p4497_2 := h4497c.2.2.1
                            have p4497_3 := h4497c.2.2.2
                            linarith only [h1, h3970, h4487, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4497_1]
                          · have p4497_0 := h4497c.1
                            have p4497_1 := h4497c.2.1
                            have p4497_2 := h4497c.2.2.1
                            have p4497_3 := h4497c.2.2.2
                            linarith only [h0, hlam, p4497_0]
                          · have p4497_0 := h4497c.1
                            have p4497_1 := h4497c.2.1
                            have p4497_2 := h4497c.2.2.1
                            have p4497_3 := h4497c.2.2.2
                            linarith only [hlam, p4497_0]
                          · have p4497_0 := h4497c.1
                            have p4497_1 := h4497c.2.1
                            have p4497_2 := h4497c.2.2.1
                            have p4497_3 := h4497c.2.2.2
                            linarith only [h4, hlam, p4497_0]
                          · have p4497_0 := h4497c.1
                            have p4497_1 := h4497c.2.1
                            have p4497_2 := h4497c.2.2.1
                            have p4497_3 := h4497c.2.2.2
                            linarith only [h3397, hlam, p4497_1]
                          · have p4497_0 := h4497c.1
                            have p4497_1 := h4497c.2.1
                            have p4497_2 := h4497c.2.2.1
                            have p4497_3 := h4497c.2.2.2
                            linarith only [h3738, hlam, p4497_0]
                          · have p4497_0 := h4497c.1
                            have p4497_1 := h4497c.2.1
                            have p4497_2 := h4497c.2.2.1
                            have p4497_3 := h4497c.2.2.2
                            linarith only [h1, hlam, p4497_1]
                          · have p4497_0 := h4497c.1
                            have p4497_1 := h4497c.2.1
                            have p4497_2 := h4497c.2.2.1
                            have p4497_3 := h4497c.2.2.2
                            linarith only [h0, h4, hc12, hc23, hlam, hphi, p4497_1]
                          · have p4497_0 := h4497c.1
                            have p4497_1 := h4497c.2.1
                            have p4497_2 := h4497c.2.2.1
                            have p4497_3 := h4497c.2.2.2
                            linarith only [hlam, p4497_0]
                          · have p4497_0 := h4497c.1
                            have p4497_1 := h4497c.2.1
                            have p4497_2 := h4497c.2.2.1
                            have p4497_3 := h4497c.2.2.2
                            linarith only [h0, h3397, h4, hc12, hc23, hlam, hphi, p4497_1]
                          · have p4497_0 := h4497c.1
                            have p4497_1 := h4497c.2.1
                            have p4497_2 := h4497c.2.2.1
                            have p4497_3 := h4497c.2.2.2
                            linarith only [h3970, hlam, p4497_1]
                          · have p4497_0 := h4497c.1
                            have p4497_1 := h4497c.2.1
                            have p4497_2 := h4497c.2.2.1
                            have p4497_3 := h4497c.2.2.2
                            linarith only [h2, hlam, p4497_0]
                          · have p4497_0 := h4497c.1
                            have p4497_1 := h4497c.2.1
                            have p4497_2 := h4497c.2.2.1
                            have p4497_3 := h4497c.2.2.2
                            linarith only [h0, h3397, h4492, hc12, hc23, hlam, hphi, p4497_1]
                          · have p4497_0 := h4497c.1
                            have p4497_1 := h4497c.2.1
                            have p4497_2 := h4497c.2.2.1
                            have p4497_3 := h4497c.2.2.2
                            linarith only [h3969, hlam, p4497_0]
                          · have p4497_0 := h4497c.1
                            have p4497_1 := h4497c.2.1
                            have p4497_2 := h4497c.2.2.1
                            have p4497_3 := h4497c.2.2.2
                            linarith only [hlam, p4497_0]
                          · have p4497_0 := h4497c.1
                            have p4497_1 := h4497c.2.1
                            have p4497_2 := h4497c.2.2.1
                            have p4497_3 := h4497c.2.2.2
                            linarith only [h4479, hlam, p4497_0]
                          · have p4497_0 := h4497c.1
                            have p4497_1 := h4497c.2.1
                            have p4497_2 := h4497c.2.2.1
                            have p4497_3 := h4497c.2.2.2
                            linarith only [h3, hlam, p4497_0]
                          · have p4497_0 := h4497c.1
                            have p4497_1 := h4497c.2.1
                            have p4497_2 := h4497c.2.2.1
                            have p4497_3 := h4497c.2.2.2
                            linarith only [h0, h3738, hc12, hc25, hlam, hphi, p4497_1]
                          · have p4497_0 := h4497c.1
                            have p4497_1 := h4497c.2.1
                            have p4497_2 := h4497c.2.2.1
                            have p4497_3 := h4497c.2.2.2
                            linarith only [h1, h3970, h4487, h4492, h4494, h4495, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4497_1]
                          · have p4497_0 := h4497c.1
                            have p4497_1 := h4497c.2.1
                            have p4497_2 := h4497c.2.2.1
                            have p4497_3 := h4497c.2.2.2
                            linarith only [h3970, h4492, h4494, h4495, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4497_1]
                          · have p4497_0 := h4497c.1
                            have p4497_1 := h4497c.2.1
                            have p4497_2 := h4497c.2.2.1
                            have p4497_3 := h4497c.2.2.2
                            linarith only [hlam, p4497_0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4535 | h4535
                        · linarith only [h1, h4487, h4494, h4535, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h0bigk with h4537c | h4537c | h4537c | h4537c | h4537c | h4537c | h4537c | h4537c | h4537c | h4537c | h4537c | h4537c | h4537c | h4537c | h4537c | h4537c | h4537c | h4537c | h4537c | h4537c | h4537c | h4537c | h4537c | h4537c | h4537c
                          · have p4537_0 := h4537c.1
                            have p4537_1 := h4537c.2.1
                            have p4537_2 := h4537c.2.2.1
                            have p4537_3 := h4537c.2.2.2
                            linarith only [hlam, p4537_0]
                          · have p4537_0 := h4537c.1
                            have p4537_1 := h4537c.2.1
                            have p4537_2 := h4537c.2.2.1
                            have p4537_3 := h4537c.2.2.2
                            rcases p4537_3 (m.d 0 1) (by simp) with h4539 | h4539
                            · rcases p4537_3 (m.d 0 2) (by simp) with h4540 | h4540
                              · linarith only [h0, h4540, hlam]
                              · rcases p4537_3 (m.d 0 3) (by simp) with h4542 | h4542
                                · linarith only [h1, h4542, hlam]
                                · linarith only [h4, h4542, hlam]
                            · linarith only [h0, h4539, hlam]
                          · have p4537_0 := h4537c.1
                            have p4537_1 := h4537c.2.1
                            have p4537_2 := h4537c.2.2.1
                            have p4537_3 := h4537c.2.2.2
                            linarith only [h1, h4487, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4537_1]
                          · have p4537_0 := h4537c.1
                            have p4537_1 := h4537c.2.1
                            have p4537_2 := h4537c.2.2.1
                            have p4537_3 := h4537c.2.2.2
                            rcases p4537_3 (m.d 0 1) (by simp) with h4547 | h4547
                            · rcases p4537_3 (m.d 0 2) (by simp) with h4548 | h4548
                              · linarith only [h0, h4548, hlam]
                              · rcases p4537_3 (m.d 0 3) (by simp) with h4550 | h4550
                                · linarith only [h1, h4550, hlam]
                                · linarith only [h3969, h4550, hlam]
                            · linarith only [h2, h4547, hlam]
                          · have p4537_0 := h4537c.1
                            have p4537_1 := h4537c.2.1
                            have p4537_2 := h4537c.2.2.1
                            have p4537_3 := h4537c.2.2.2
                            linarith only [h1, h3970, h4487, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4537_1]
                          · have p4537_0 := h4537c.1
                            have p4537_1 := h4537c.2.1
                            have p4537_2 := h4537c.2.2.1
                            have p4537_3 := h4537c.2.2.2
                            linarith only [h0, hlam, p4537_0]
                          · have p4537_0 := h4537c.1
                            have p4537_1 := h4537c.2.1
                            have p4537_2 := h4537c.2.2.1
                            have p4537_3 := h4537c.2.2.2
                            linarith only [hlam, p4537_0]
                          · have p4537_0 := h4537c.1
                            have p4537_1 := h4537c.2.1
                            have p4537_2 := h4537c.2.2.1
                            have p4537_3 := h4537c.2.2.2
                            linarith only [h4, hlam, p4537_0]
                          · have p4537_0 := h4537c.1
                            have p4537_1 := h4537c.2.1
                            have p4537_2 := h4537c.2.2.1
                            have p4537_3 := h4537c.2.2.2
                            linarith only [h3397, hlam, p4537_1]
                          · have p4537_0 := h4537c.1
                            have p4537_1 := h4537c.2.1
                            have p4537_2 := h4537c.2.2.1
                            have p4537_3 := h4537c.2.2.2
                            linarith only [h3738, hlam, p4537_0]
                          · have p4537_0 := h4537c.1
                            have p4537_1 := h4537c.2.1
                            have p4537_2 := h4537c.2.2.1
                            have p4537_3 := h4537c.2.2.2
                            linarith only [h1, hlam, p4537_1]
                          · have p4537_0 := h4537c.1
                            have p4537_1 := h4537c.2.1
                            have p4537_2 := h4537c.2.2.1
                            have p4537_3 := h4537c.2.2.2
                            linarith only [h0, h4, hc12, hc23, hlam, hphi, p4537_1]
                          · have p4537_0 := h4537c.1
                            have p4537_1 := h4537c.2.1
                            have p4537_2 := h4537c.2.2.1
                            have p4537_3 := h4537c.2.2.2
                            linarith only [hlam, p4537_0]
                          · have p4537_0 := h4537c.1
                            have p4537_1 := h4537c.2.1
                            have p4537_2 := h4537c.2.2.1
                            have p4537_3 := h4537c.2.2.2
                            linarith only [h2, h4, h4483, hc12, hc23, hlam, hphi, p4537_1]
                          · have p4537_0 := h4537c.1
                            have p4537_1 := h4537c.2.1
                            have p4537_2 := h4537c.2.2.1
                            have p4537_3 := h4537c.2.2.2
                            linarith only [h3970, hlam, p4537_1]
                          · have p4537_0 := h4537c.1
                            have p4537_1 := h4537c.2.1
                            have p4537_2 := h4537c.2.2.1
                            have p4537_3 := h4537c.2.2.2
                            linarith only [h2, hlam, p4537_0]
                          · have p4537_0 := h4537c.1
                            have p4537_1 := h4537c.2.1
                            have p4537_2 := h4537c.2.2.1
                            have p4537_3 := h4537c.2.2.2
                            linarith only [h0, h3397, hc12, hc24, hlam, hphi, p4537_1]
                          · have p4537_0 := h4537c.1
                            have p4537_1 := h4537c.2.1
                            have p4537_2 := h4537c.2.2.1
                            have p4537_3 := h4537c.2.2.2
                            linarith only [h3969, hlam, p4537_0]
                          · have p4537_0 := h4537c.1
                            have p4537_1 := h4537c.2.1
                            have p4537_2 := h4537c.2.2.1
                            have p4537_3 := h4537c.2.2.2
                            linarith only [hlam, p4537_0]
                          · have p4537_0 := h4537c.1
                            have p4537_1 := h4537c.2.1
                            have p4537_2 := h4537c.2.2.1
                            have p4537_3 := h4537c.2.2.2
                            linarith only [h4479, hlam, p4537_0]
                          · have p4537_0 := h4537c.1
                            have p4537_1 := h4537c.2.1
                            have p4537_2 := h4537c.2.2.1
                            have p4537_3 := h4537c.2.2.2
                            linarith only [h3, hlam, p4537_0]
                          · have p4537_0 := h4537c.1
                            have p4537_1 := h4537c.2.1
                            have p4537_2 := h4537c.2.2.1
                            have p4537_3 := h4537c.2.2.2
                            linarith only [h0, h3738, hc12, hc25, hlam, hphi, p4537_1]
                          · have p4537_0 := h4537c.1
                            have p4537_1 := h4537c.2.1
                            have p4537_2 := h4537c.2.2.1
                            have p4537_3 := h4537c.2.2.2
                            linarith only [h1, h4487, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p4537_1]
                          · have p4537_0 := h4537c.1
                            have p4537_1 := h4537c.2.1
                            have p4537_2 := h4537c.2.2.1
                            have p4537_3 := h4537c.2.2.2
                            linarith only [h4479, hc04, hc45, hlam, hphi, p4537_1]
                          · have p4537_0 := h4537c.1
                            have p4537_1 := h4537c.2.1
                            have p4537_2 := h4537c.2.2.1
                            have p4537_3 := h4537c.2.2.2
                            linarith only [hlam, p4537_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4575 | h4575
                      · linarith only [h0, h3397, h4479, h4492, h4493, h4575, hc12, hc35, hlam, hphi, ht23]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4577 | h4577
                        · linarith only [h1, h4487, h4575, h4577, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h0bigk with h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c | h4579c
                          · have p4579_0 := h4579c.1
                            have p4579_1 := h4579c.2.1
                            have p4579_2 := h4579c.2.2.1
                            have p4579_3 := h4579c.2.2.2
                            linarith only [hlam, p4579_0]
                          · have p4579_0 := h4579c.1
                            have p4579_1 := h4579c.2.1
                            have p4579_2 := h4579c.2.2.1
                            have p4579_3 := h4579c.2.2.2
                            rcases p4579_3 (m.d 0 1) (by simp) with h4581 | h4581
                            · rcases p4579_3 (m.d 0 2) (by simp) with h4582 | h4582
                              · linarith only [h0, h4582, hlam]
                              · rcases p4579_3 (m.d 0 3) (by simp) with h4584 | h4584
                                · linarith only [h1, h4584, hlam]
                                · linarith only [h4, h4584, hlam]
                            · linarith only [h0, h4581, hlam]
                          · have p4579_0 := h4579c.1
                            have p4579_1 := h4579c.2.1
                            have p4579_2 := h4579c.2.2.1
                            have p4579_3 := h4579c.2.2.2
                            linarith only [h1, h4487, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4579_1]
                          · have p4579_0 := h4579c.1
                            have p4579_1 := h4579c.2.1
                            have p4579_2 := h4579c.2.2.1
                            have p4579_3 := h4579c.2.2.2
                            rcases p4579_3 (m.d 0 1) (by simp) with h4589 | h4589
                            · rcases p4579_3 (m.d 0 2) (by simp) with h4590 | h4590
                              · linarith only [h0, h4590, hlam]
                              · rcases p4579_3 (m.d 0 3) (by simp) with h4592 | h4592
                                · linarith only [h1, h4592, hlam]
                                · linarith only [h3969, h4592, hlam]
                            · linarith only [h2, h4589, hlam]
                          · have p4579_0 := h4579c.1
                            have p4579_1 := h4579c.2.1
                            have p4579_2 := h4579c.2.2.1
                            have p4579_3 := h4579c.2.2.2
                            linarith only [h1, h3970, h4487, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4579_1]
                          · have p4579_0 := h4579c.1
                            have p4579_1 := h4579c.2.1
                            have p4579_2 := h4579c.2.2.1
                            have p4579_3 := h4579c.2.2.2
                            linarith only [h0, hlam, p4579_0]
                          · have p4579_0 := h4579c.1
                            have p4579_1 := h4579c.2.1
                            have p4579_2 := h4579c.2.2.1
                            have p4579_3 := h4579c.2.2.2
                            linarith only [hlam, p4579_0]
                          · have p4579_0 := h4579c.1
                            have p4579_1 := h4579c.2.1
                            have p4579_2 := h4579c.2.2.1
                            have p4579_3 := h4579c.2.2.2
                            linarith only [h4, hlam, p4579_0]
                          · have p4579_0 := h4579c.1
                            have p4579_1 := h4579c.2.1
                            have p4579_2 := h4579c.2.2.1
                            have p4579_3 := h4579c.2.2.2
                            linarith only [h3397, hlam, p4579_1]
                          · have p4579_0 := h4579c.1
                            have p4579_1 := h4579c.2.1
                            have p4579_2 := h4579c.2.2.1
                            have p4579_3 := h4579c.2.2.2
                            linarith only [h3738, hlam, p4579_0]
                          · have p4579_0 := h4579c.1
                            have p4579_1 := h4579c.2.1
                            have p4579_2 := h4579c.2.2.1
                            have p4579_3 := h4579c.2.2.2
                            linarith only [h1, hlam, p4579_1]
                          · have p4579_0 := h4579c.1
                            have p4579_1 := h4579c.2.1
                            have p4579_2 := h4579c.2.2.1
                            have p4579_3 := h4579c.2.2.2
                            linarith only [h0, h4, hc12, hc23, hlam, hphi, p4579_1]
                          · have p4579_0 := h4579c.1
                            have p4579_1 := h4579c.2.1
                            have p4579_2 := h4579c.2.2.1
                            have p4579_3 := h4579c.2.2.2
                            linarith only [hlam, p4579_0]
                          · have p4579_0 := h4579c.1
                            have p4579_1 := h4579c.2.1
                            have p4579_2 := h4579c.2.2.1
                            have p4579_3 := h4579c.2.2.2
                            linarith only [h0, h3397, h4, h4493, h4577, hc12, hc45, hlam, hphi, ht23, ht34, p4579_1]
                          · have p4579_0 := h4579c.1
                            have p4579_1 := h4579c.2.1
                            have p4579_2 := h4579c.2.2.1
                            have p4579_3 := h4579c.2.2.2
                            linarith only [h3970, hlam, p4579_1]
                          · have p4579_0 := h4579c.1
                            have p4579_1 := h4579c.2.1
                            have p4579_2 := h4579c.2.2.1
                            have p4579_3 := h4579c.2.2.2
                            linarith only [h2, hlam, p4579_0]
                          · have p4579_0 := h4579c.1
                            have p4579_1 := h4579c.2.1
                            have p4579_2 := h4579c.2.2.1
                            have p4579_3 := h4579c.2.2.2
                            linarith only [h0, h3397, hc12, hc24, hlam, hphi, p4579_1]
                          · have p4579_0 := h4579c.1
                            have p4579_1 := h4579c.2.1
                            have p4579_2 := h4579c.2.2.1
                            have p4579_3 := h4579c.2.2.2
                            linarith only [h3969, hlam, p4579_0]
                          · have p4579_0 := h4579c.1
                            have p4579_1 := h4579c.2.1
                            have p4579_2 := h4579c.2.2.1
                            have p4579_3 := h4579c.2.2.2
                            linarith only [hlam, p4579_0]
                          · have p4579_0 := h4579c.1
                            have p4579_1 := h4579c.2.1
                            have p4579_2 := h4579c.2.2.1
                            have p4579_3 := h4579c.2.2.2
                            linarith only [h4479, hlam, p4579_0]
                          · have p4579_0 := h4579c.1
                            have p4579_1 := h4579c.2.1
                            have p4579_2 := h4579c.2.2.1
                            have p4579_3 := h4579c.2.2.2
                            linarith only [h3, hlam, p4579_0]
                          · have p4579_0 := h4579c.1
                            have p4579_1 := h4579c.2.1
                            have p4579_2 := h4579c.2.2.1
                            have p4579_3 := h4579c.2.2.2
                            linarith only [h0, h3738, hc12, hc25, hlam, hphi, p4579_1]
                          · have p4579_0 := h4579c.1
                            have p4579_1 := h4579c.2.1
                            have p4579_2 := h4579c.2.2.1
                            have p4579_3 := h4579c.2.2.2
                            linarith only [h3970, h4577, hc03, hc45, hlam, hphi, ht34, p4579_1]
                          · have p4579_0 := h4579c.1
                            have p4579_1 := h4579c.2.1
                            have p4579_2 := h4579c.2.2.1
                            have p4579_3 := h4579c.2.2.2
                            linarith only [h3970, h4577, hc04, hc45, hlam, hphi, p4579_1]
                          · have p4579_0 := h4579c.1
                            have p4579_1 := h4579c.2.1
                            have p4579_2 := h4579c.2.2.1
                            have p4579_3 := h4579c.2.2.2
                            linarith only [hlam, p4579_0]
                  · linarith only [h0, h1, h4, h4487, h4492, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h3969, h3970, h4487, hc13, hc35, hlam, hphi]

end R2N4
