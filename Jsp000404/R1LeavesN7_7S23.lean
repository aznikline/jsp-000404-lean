import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_7S22

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8480000 in
set_option maxHeartbeats 8480000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s14 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg11379 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h10472 := hg10472
  have h11379 := hg11379
  rcases m.htr 0 1 5 (by decide) (by decide) with h12013 | h12013
  · rcases m.htr 0 2 3 (by decide) (by decide) with h12014 | h12014
    · rcases m.htr 0 2 4 (by decide) (by decide) with h12015 | h12015
      · rcases m.htr 0 2 5 (by decide) (by decide) with h12016 | h12016
        · rcases m.htr 0 3 4 (by decide) (by decide) with h12017 | h12017
          · rcases m.htr 0 3 5 (by decide) (by decide) with h12018 | h12018
            · rcases m.htr 0 4 5 (by decide) (by decide) with h12019 | h12019
              · rcases m.htr 1 2 3 (by decide) (by decide) with h12020 | h12020
                · rcases m.htr 1 2 4 (by decide) (by decide) with h12021 | h12021
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h12022 | h12022
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h12023 | h12023
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h12024 | h12024
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h12025 | h12025
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h12026 | h12026
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h12027 | h12027
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h12028 | h12028
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h12029 | h12029
                                  · linarith only [h12014, h12026, h12029, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · rcases h1bigk with h12031c | h12031c | h12031c | h12031c | h12031c | h12031c | h12031c | h12031c | h12031c | h12031c | h12031c | h12031c | h12031c | h12031c | h12031c | h12031c | h12031c | h12031c | h12031c | h12031c | h12031c | h12031c | h12031c | h12031c | h12031c
                                    · have p12031_0 := h12031c.1
                                      have p12031_1 := h12031c.2.1
                                      have p12031_2 := h12031c.2.2.1
                                      have p12031_3 := h12031c.2.2.2
                                      linarith only [hlam, p12031_0]
                                    · have p12031_0 := h12031c.1
                                      have p12031_1 := h12031c.2.1
                                      have p12031_2 := h12031c.2.2.1
                                      have p12031_3 := h12031c.2.2.2
                                      linarith only [h0, hlam, p12031_0]
                                    · have p12031_0 := h12031c.1
                                      have p12031_1 := h12031c.2.1
                                      have p12031_2 := h12031c.2.2.1
                                      have p12031_3 := h12031c.2.2.2
                                      linarith only [h10472, hlam, p12031_0]
                                    · have p12031_0 := h12031c.1
                                      have p12031_1 := h12031c.2.1
                                      have p12031_2 := h12031c.2.2.1
                                      have p12031_3 := h12031c.2.2.2
                                      linarith only [h11379, hlam, p12031_0]
                                    · have p12031_0 := h12031c.1
                                      have p12031_1 := h12031c.2.1
                                      have p12031_2 := h12031c.2.2.1
                                      have p12031_3 := h12031c.2.2.2
                                      linarith only [h11379, h12022, h12028, h12029, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12031_1]
                                    · have p12031_0 := h12031c.1
                                      have p12031_1 := h12031c.2.1
                                      have p12031_2 := h12031c.2.2.1
                                      have p12031_3 := h12031c.2.2.2
                                      linarith only [h12013, h12022, h12028, h12029, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12031_1]
                                    · have p12031_0 := h12031c.1
                                      have p12031_1 := h12031c.2.1
                                      have p12031_2 := h12031c.2.2.1
                                      have p12031_3 := h12031c.2.2.2
                                      linarith only [hlam, p12031_0]
                                    · have p12031_0 := h12031c.1
                                      have p12031_1 := h12031c.2.1
                                      have p12031_2 := h12031c.2.2.1
                                      have p12031_3 := h12031c.2.2.2
                                      linarith only [h10472, h12013, h12022, h12028, h12029, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12031_1]
                                    · have p12031_0 := h12031c.1
                                      have p12031_1 := h12031c.2.1
                                      have p12031_2 := h12031c.2.2.1
                                      have p12031_3 := h12031c.2.2.2
                                      linarith only [h11379, h12013, h12022, h12028, h12029, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12031_1]
                                    · have p12031_0 := h12031c.1
                                      have p12031_1 := h12031c.2.1
                                      have p12031_2 := h12031c.2.2.1
                                      have p12031_3 := h12031c.2.2.2
                                      rcases p12031_3 (m.d 0 1) (by simp) with h12041 | h12041
                                      · linarith only [h0, h12041, hlam]
                                      · linarith only [h12013, h12041, hlam]
                                    · have p12031_0 := h12031c.1
                                      have p12031_1 := h12031c.2.1
                                      have p12031_2 := h12031c.2.2.1
                                      have p12031_3 := h12031c.2.2.2
                                      linarith only [h12013, h12022, h12028, h12029, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12031_1]
                                    · have p12031_0 := h12031c.1
                                      have p12031_1 := h12031c.2.1
                                      have p12031_2 := h12031c.2.2.1
                                      have p12031_3 := h12031c.2.2.2
                                      linarith only [h12020, hlam, p12031_1]
                                    · have p12031_0 := h12031c.1
                                      have p12031_1 := h12031c.2.1
                                      have p12031_2 := h12031c.2.2.1
                                      have p12031_3 := h12031c.2.2.2
                                      linarith only [hlam, p12031_0]
                                    · have p12031_0 := h12031c.1
                                      have p12031_1 := h12031c.2.1
                                      have p12031_2 := h12031c.2.2.1
                                      have p12031_3 := h12031c.2.2.2
                                      linarith only [h11379, h12013, h12020, h12022, h12028, h12029, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12031_1]
                                    · have p12031_0 := h12031c.1
                                      have p12031_1 := h12031c.2.1
                                      have p12031_2 := h12031c.2.2.1
                                      have p12031_3 := h12031c.2.2.2
                                      rcases p12031_3 (m.d 0 1) (by simp) with h12048 | h12048
                                      · linarith only [h10472, h12048, hlam]
                                      · linarith only [h12013, h12048, hlam]
                                    · have p12031_0 := h12031c.1
                                      have p12031_1 := h12031c.2.1
                                      have p12031_2 := h12031c.2.2.1
                                      have p12031_3 := h12031c.2.2.2
                                      linarith only [h12013, h12022, h12028, h12029, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12031_1]
                                    · have p12031_0 := h12031c.1
                                      have p12031_1 := h12031c.2.1
                                      have p12031_2 := h12031c.2.2.1
                                      have p12031_3 := h12031c.2.2.2
                                      linarith only [h12021, hlam, p12031_1]
                                    · have p12031_0 := h12031c.1
                                      have p12031_1 := h12031c.2.1
                                      have p12031_2 := h12031c.2.2.1
                                      have p12031_3 := h12031c.2.2.2
                                      linarith only [h12023, hlam, p12031_0]
                                    · have p12031_0 := h12031c.1
                                      have p12031_1 := h12031c.2.1
                                      have p12031_2 := h12031c.2.2.1
                                      have p12031_3 := h12031c.2.2.2
                                      linarith only [hlam, p12031_0]
                                    · have p12031_0 := h12031c.1
                                      have p12031_1 := h12031c.2.1
                                      have p12031_2 := h12031c.2.2.1
                                      have p12031_3 := h12031c.2.2.2
                                      rcases p12031_3 (m.d 0 1) (by simp) with h12055 | h12055
                                      · linarith only [h11379, h12055, hlam]
                                      · linarith only [h12013, h12055, hlam]
                                    · have p12031_0 := h12031c.1
                                      have p12031_1 := h12031c.2.1
                                      have p12031_2 := h12031c.2.2.1
                                      have p12031_3 := h12031c.2.2.2
                                      linarith only [h12013, hlam, p12031_0]
                                    · have p12031_0 := h12031c.1
                                      have p12031_1 := h12031c.2.1
                                      have p12031_2 := h12031c.2.2.1
                                      have p12031_3 := h12031c.2.2.2
                                      linarith only [h12022, hlam, p12031_1]
                                    · have p12031_0 := h12031c.1
                                      have p12031_1 := h12031c.2.1
                                      have p12031_2 := h12031c.2.2.1
                                      have p12031_3 := h12031c.2.2.2
                                      linarith only [h12024, hlam, p12031_0]
                                    · have p12031_0 := h12031c.1
                                      have p12031_1 := h12031c.2.1
                                      have p12031_2 := h12031c.2.2.1
                                      have p12031_3 := h12031c.2.2.2
                                      linarith only [h12025, hlam, p12031_0]
                                    · have p12031_0 := h12031c.1
                                      have p12031_1 := h12031c.2.1
                                      have p12031_2 := h12031c.2.2.1
                                      have p12031_3 := h12031c.2.2.2
                                      linarith only [hlam, p12031_0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h12063 | h12063
                                  · linarith only [h0, h12014, h12026, h12028, h12063, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · rcases h1bigk with h12065c | h12065c | h12065c | h12065c | h12065c | h12065c | h12065c | h12065c | h12065c | h12065c | h12065c | h12065c | h12065c | h12065c | h12065c | h12065c | h12065c | h12065c | h12065c | h12065c | h12065c | h12065c | h12065c | h12065c | h12065c
                                    · have p12065_0 := h12065c.1
                                      have p12065_1 := h12065c.2.1
                                      have p12065_2 := h12065c.2.2.1
                                      have p12065_3 := h12065c.2.2.2
                                      linarith only [hlam, p12065_0]
                                    · have p12065_0 := h12065c.1
                                      have p12065_1 := h12065c.2.1
                                      have p12065_2 := h12065c.2.2.1
                                      have p12065_3 := h12065c.2.2.2
                                      linarith only [h0, hlam, p12065_0]
                                    · have p12065_0 := h12065c.1
                                      have p12065_1 := h12065c.2.1
                                      have p12065_2 := h12065c.2.2.1
                                      have p12065_3 := h12065c.2.2.2
                                      linarith only [h10472, hlam, p12065_0]
                                    · have p12065_0 := h12065c.1
                                      have p12065_1 := h12065c.2.1
                                      have p12065_2 := h12065c.2.2.1
                                      have p12065_3 := h12065c.2.2.2
                                      linarith only [h11379, hlam, p12065_0]
                                    · have p12065_0 := h12065c.1
                                      have p12065_1 := h12065c.2.1
                                      have p12065_2 := h12065c.2.2.1
                                      have p12065_3 := h12065c.2.2.2
                                      linarith only [h0, h12025, h12026, h12028, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12065_1]
                                    · have p12065_0 := h12065c.1
                                      have p12065_1 := h12065c.2.1
                                      have p12065_2 := h12065c.2.2.1
                                      have p12065_3 := h12065c.2.2.2
                                      linarith only [h12013, h12025, h12026, h12028, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12065_1]
                                    · have p12065_0 := h12065c.1
                                      have p12065_1 := h12065c.2.1
                                      have p12065_2 := h12065c.2.2.1
                                      have p12065_3 := h12065c.2.2.2
                                      linarith only [hlam, p12065_0]
                                    · have p12065_0 := h12065c.1
                                      have p12065_1 := h12065c.2.1
                                      have p12065_2 := h12065c.2.2.1
                                      have p12065_3 := h12065c.2.2.2
                                      linarith only [h10472, hc01, hc12, hlam, hphi, p12065_1]
                                    · have p12065_0 := h12065c.1
                                      have p12065_1 := h12065c.2.1
                                      have p12065_2 := h12065c.2.2.1
                                      have p12065_3 := h12065c.2.2.2
                                      linarith only [h11379, h12013, h12025, h12026, h12028, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12065_1]
                                    · have p12065_0 := h12065c.1
                                      have p12065_1 := h12065c.2.1
                                      have p12065_2 := h12065c.2.2.1
                                      have p12065_3 := h12065c.2.2.2
                                      rcases p12065_3 (m.d 0 1) (by simp) with h12075 | h12075
                                      · linarith only [h0, h12075, hlam]
                                      · linarith only [h12013, h12075, hlam]
                                    · have p12065_0 := h12065c.1
                                      have p12065_1 := h12065c.2.1
                                      have p12065_2 := h12065c.2.2.1
                                      have p12065_3 := h12065c.2.2.2
                                      linarith only [h12013, h12025, h12026, h12028, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12065_1]
                                    · have p12065_0 := h12065c.1
                                      have p12065_1 := h12065c.2.1
                                      have p12065_2 := h12065c.2.2.1
                                      have p12065_3 := h12065c.2.2.2
                                      linarith only [h12020, hlam, p12065_1]
                                    · have p12065_0 := h12065c.1
                                      have p12065_1 := h12065c.2.1
                                      have p12065_2 := h12065c.2.2.1
                                      have p12065_3 := h12065c.2.2.2
                                      linarith only [hlam, p12065_0]
                                    · have p12065_0 := h12065c.1
                                      have p12065_1 := h12065c.2.1
                                      have p12065_2 := h12065c.2.2.1
                                      have p12065_3 := h12065c.2.2.2
                                      linarith only [h11379, h12013, h12020, h12025, h12026, h12028, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12065_1]
                                    · have p12065_0 := h12065c.1
                                      have p12065_1 := h12065c.2.1
                                      have p12065_2 := h12065c.2.2.1
                                      have p12065_3 := h12065c.2.2.2
                                      rcases p12065_3 (m.d 0 1) (by simp) with h12082 | h12082
                                      · linarith only [h10472, h12082, hlam]
                                      · linarith only [h12013, h12082, hlam]
                                    · have p12065_0 := h12065c.1
                                      have p12065_1 := h12065c.2.1
                                      have p12065_2 := h12065c.2.2.1
                                      have p12065_3 := h12065c.2.2.2
                                      linarith only [h12013, h12025, h12026, h12028, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12065_1]
                                    · have p12065_0 := h12065c.1
                                      have p12065_1 := h12065c.2.1
                                      have p12065_2 := h12065c.2.2.1
                                      have p12065_3 := h12065c.2.2.2
                                      linarith only [h12021, hlam, p12065_1]
                                    · have p12065_0 := h12065c.1
                                      have p12065_1 := h12065c.2.1
                                      have p12065_2 := h12065c.2.2.1
                                      have p12065_3 := h12065c.2.2.2
                                      linarith only [h12023, hlam, p12065_0]
                                    · have p12065_0 := h12065c.1
                                      have p12065_1 := h12065c.2.1
                                      have p12065_2 := h12065c.2.2.1
                                      have p12065_3 := h12065c.2.2.2
                                      linarith only [hlam, p12065_0]
                                    · have p12065_0 := h12065c.1
                                      have p12065_1 := h12065c.2.1
                                      have p12065_2 := h12065c.2.2.1
                                      have p12065_3 := h12065c.2.2.2
                                      rcases p12065_3 (m.d 0 1) (by simp) with h12089 | h12089
                                      · linarith only [h11379, h12089, hlam]
                                      · linarith only [h12013, h12089, hlam]
                                    · have p12065_0 := h12065c.1
                                      have p12065_1 := h12065c.2.1
                                      have p12065_2 := h12065c.2.2.1
                                      have p12065_3 := h12065c.2.2.2
                                      linarith only [h12013, hlam, p12065_0]
                                    · have p12065_0 := h12065c.1
                                      have p12065_1 := h12065c.2.1
                                      have p12065_2 := h12065c.2.2.1
                                      have p12065_3 := h12065c.2.2.2
                                      linarith only [h12022, hlam, p12065_1]
                                    · have p12065_0 := h12065c.1
                                      have p12065_1 := h12065c.2.1
                                      have p12065_2 := h12065c.2.2.1
                                      have p12065_3 := h12065c.2.2.2
                                      linarith only [h12024, hlam, p12065_0]
                                    · have p12065_0 := h12065c.1
                                      have p12065_1 := h12065c.2.1
                                      have p12065_2 := h12065c.2.2.1
                                      have p12065_3 := h12065c.2.2.2
                                      linarith only [h12025, hlam, p12065_0]
                                    · have p12065_0 := h12065c.1
                                      have p12065_1 := h12065c.2.1
                                      have p12065_2 := h12065c.2.2.1
                                      have p12065_3 := h12065c.2.2.2
                                      linarith only [hlam, p12065_0]
                              · linarith only [h11379, h12013, h12020, h12023, h12024, h12026, h12027, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h12098 | h12098
                              · linarith only [h10472, h12017, h12020, h12026, h12098, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h12100 | h12100
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h12101 | h12101
                                  · rcases h1bigk with h12102c | h12102c | h12102c | h12102c | h12102c | h12102c | h12102c | h12102c | h12102c | h12102c | h12102c | h12102c | h12102c | h12102c | h12102c | h12102c | h12102c | h12102c | h12102c | h12102c | h12102c | h12102c | h12102c | h12102c | h12102c
                                    · have p12102_0 := h12102c.1
                                      have p12102_1 := h12102c.2.1
                                      have p12102_2 := h12102c.2.2.1
                                      have p12102_3 := h12102c.2.2.2
                                      linarith only [hlam, p12102_0]
                                    · have p12102_0 := h12102c.1
                                      have p12102_1 := h12102c.2.1
                                      have p12102_2 := h12102c.2.2.1
                                      have p12102_3 := h12102c.2.2.2
                                      linarith only [h0, hlam, p12102_0]
                                    · have p12102_0 := h12102c.1
                                      have p12102_1 := h12102c.2.1
                                      have p12102_2 := h12102c.2.2.1
                                      have p12102_3 := h12102c.2.2.2
                                      linarith only [h10472, hlam, p12102_0]
                                    · have p12102_0 := h12102c.1
                                      have p12102_1 := h12102c.2.1
                                      have p12102_2 := h12102c.2.2.1
                                      have p12102_3 := h12102c.2.2.2
                                      linarith only [h11379, hlam, p12102_0]
                                    · have p12102_0 := h12102c.1
                                      have p12102_1 := h12102c.2.1
                                      have p12102_2 := h12102c.2.2.1
                                      have p12102_3 := h12102c.2.2.2
                                      linarith only [h11379, h12020, h12023, hc12, hlam, hphi, ht01, ht0b, ht5b, p12102_1, u5ehi1]
                                    · have p12102_0 := h12102c.1
                                      have p12102_1 := h12102c.2.1
                                      have p12102_2 := h12102c.2.2.1
                                      have p12102_3 := h12102c.2.2.2
                                      linarith only [h12013, h12024, h12098, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12102_1]
                                    · have p12102_0 := h12102c.1
                                      have p12102_1 := h12102c.2.1
                                      have p12102_2 := h12102c.2.2.1
                                      have p12102_3 := h12102c.2.2.2
                                      linarith only [hlam, p12102_0]
                                    · have p12102_0 := h12102c.1
                                      have p12102_1 := h12102c.2.1
                                      have p12102_2 := h12102c.2.2.1
                                      have p12102_3 := h12102c.2.2.2
                                      linarith only [h10472, hc01, hc12, hlam, hphi, p12102_1]
                                    · have p12102_0 := h12102c.1
                                      have p12102_1 := h12102c.2.1
                                      have p12102_2 := h12102c.2.2.1
                                      have p12102_3 := h12102c.2.2.2
                                      linarith only [h11379, h12013, h12024, h12098, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12102_1]
                                    · have p12102_0 := h12102c.1
                                      have p12102_1 := h12102c.2.1
                                      have p12102_2 := h12102c.2.2.1
                                      have p12102_3 := h12102c.2.2.2
                                      rcases p12102_3 (m.d 0 1) (by simp) with h12112 | h12112
                                      · linarith only [h0, h12112, hlam]
                                      · linarith only [h12013, h12112, hlam]
                                    · have p12102_0 := h12102c.1
                                      have p12102_1 := h12102c.2.1
                                      have p12102_2 := h12102c.2.2.1
                                      have p12102_3 := h12102c.2.2.2
                                      linarith only [h12013, h12024, h12098, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12102_1]
                                    · have p12102_0 := h12102c.1
                                      have p12102_1 := h12102c.2.1
                                      have p12102_2 := h12102c.2.2.1
                                      have p12102_3 := h12102c.2.2.2
                                      linarith only [h12020, hlam, p12102_1]
                                    · have p12102_0 := h12102c.1
                                      have p12102_1 := h12102c.2.1
                                      have p12102_2 := h12102c.2.2.1
                                      have p12102_3 := h12102c.2.2.2
                                      linarith only [hlam, p12102_0]
                                    · have p12102_0 := h12102c.1
                                      have p12102_1 := h12102c.2.1
                                      have p12102_2 := h12102c.2.2.1
                                      have p12102_3 := h12102c.2.2.2
                                      linarith only [h11379, h12013, h12020, h12024, h12098, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12102_1]
                                    · have p12102_0 := h12102c.1
                                      have p12102_1 := h12102c.2.1
                                      have p12102_2 := h12102c.2.2.1
                                      have p12102_3 := h12102c.2.2.2
                                      rcases p12102_3 (m.d 0 1) (by simp) with h12119 | h12119
                                      · linarith only [h10472, h12119, hlam]
                                      · linarith only [h12013, h12119, hlam]
                                    · have p12102_0 := h12102c.1
                                      have p12102_1 := h12102c.2.1
                                      have p12102_2 := h12102c.2.2.1
                                      have p12102_3 := h12102c.2.2.2
                                      linarith only [h12013, h12024, h12098, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12102_1]
                                    · have p12102_0 := h12102c.1
                                      have p12102_1 := h12102c.2.1
                                      have p12102_2 := h12102c.2.2.1
                                      have p12102_3 := h12102c.2.2.2
                                      linarith only [h12021, hlam, p12102_1]
                                    · have p12102_0 := h12102c.1
                                      have p12102_1 := h12102c.2.1
                                      have p12102_2 := h12102c.2.2.1
                                      have p12102_3 := h12102c.2.2.2
                                      linarith only [h12023, hlam, p12102_0]
                                    · have p12102_0 := h12102c.1
                                      have p12102_1 := h12102c.2.1
                                      have p12102_2 := h12102c.2.2.1
                                      have p12102_3 := h12102c.2.2.2
                                      linarith only [hlam, p12102_0]
                                    · have p12102_0 := h12102c.1
                                      have p12102_1 := h12102c.2.1
                                      have p12102_2 := h12102c.2.2.1
                                      have p12102_3 := h12102c.2.2.2
                                      rcases p12102_3 (m.d 0 1) (by simp) with h12126 | h12126
                                      · linarith only [h11379, h12126, hlam]
                                      · linarith only [h12013, h12126, hlam]
                                    · have p12102_0 := h12102c.1
                                      have p12102_1 := h12102c.2.1
                                      have p12102_2 := h12102c.2.2.1
                                      have p12102_3 := h12102c.2.2.2
                                      linarith only [h12013, hlam, p12102_0]
                                    · have p12102_0 := h12102c.1
                                      have p12102_1 := h12102c.2.1
                                      have p12102_2 := h12102c.2.2.1
                                      have p12102_3 := h12102c.2.2.2
                                      linarith only [h12022, hlam, p12102_1]
                                    · have p12102_0 := h12102c.1
                                      have p12102_1 := h12102c.2.1
                                      have p12102_2 := h12102c.2.2.1
                                      have p12102_3 := h12102c.2.2.2
                                      linarith only [h12024, hlam, p12102_0]
                                    · have p12102_0 := h12102c.1
                                      have p12102_1 := h12102c.2.1
                                      have p12102_2 := h12102c.2.2.1
                                      have p12102_3 := h12102c.2.2.2
                                      linarith only [h12025, hlam, p12102_0]
                                    · have p12102_0 := h12102c.1
                                      have p12102_1 := h12102c.2.1
                                      have p12102_2 := h12102c.2.2.1
                                      have p12102_3 := h12102c.2.2.2
                                      linarith only [hlam, p12102_0]
                                  · linarith only [h0, h12015, h12026, h12100, h12101, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h12135 | h12135
                                  · rcases h1bigk with h12136c | h12136c | h12136c | h12136c | h12136c | h12136c | h12136c | h12136c | h12136c | h12136c | h12136c | h12136c | h12136c | h12136c | h12136c | h12136c | h12136c | h12136c | h12136c | h12136c | h12136c | h12136c | h12136c | h12136c | h12136c
                                    · have p12136_0 := h12136c.1
                                      have p12136_1 := h12136c.2.1
                                      have p12136_2 := h12136c.2.2.1
                                      have p12136_3 := h12136c.2.2.2
                                      linarith only [hlam, p12136_0]
                                    · have p12136_0 := h12136c.1
                                      have p12136_1 := h12136c.2.1
                                      have p12136_2 := h12136c.2.2.1
                                      have p12136_3 := h12136c.2.2.2
                                      linarith only [h0, hlam, p12136_0]
                                    · have p12136_0 := h12136c.1
                                      have p12136_1 := h12136c.2.1
                                      have p12136_2 := h12136c.2.2.1
                                      have p12136_3 := h12136c.2.2.2
                                      linarith only [h10472, hlam, p12136_0]
                                    · have p12136_0 := h12136c.1
                                      have p12136_1 := h12136c.2.1
                                      have p12136_2 := h12136c.2.2.1
                                      have p12136_3 := h12136c.2.2.2
                                      linarith only [h11379, hlam, p12136_0]
                                    · have p12136_0 := h12136c.1
                                      have p12136_1 := h12136c.2.1
                                      have p12136_2 := h12136c.2.2.1
                                      have p12136_3 := h12136c.2.2.2
                                      linarith only [h0, h12024, h12026, h12100, h12135, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12136_1]
                                    · have p12136_0 := h12136c.1
                                      have p12136_1 := h12136c.2.1
                                      have p12136_2 := h12136c.2.2.1
                                      have p12136_3 := h12136c.2.2.2
                                      linarith only [h12013, h12024, h12026, h12100, h12135, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12136_1]
                                    · have p12136_0 := h12136c.1
                                      have p12136_1 := h12136c.2.1
                                      have p12136_2 := h12136c.2.2.1
                                      have p12136_3 := h12136c.2.2.2
                                      linarith only [hlam, p12136_0]
                                    · have p12136_0 := h12136c.1
                                      have p12136_1 := h12136c.2.1
                                      have p12136_2 := h12136c.2.2.1
                                      have p12136_3 := h12136c.2.2.2
                                      linarith only [h10472, hc01, hc12, hlam, hphi, p12136_1]
                                    · have p12136_0 := h12136c.1
                                      have p12136_1 := h12136c.2.1
                                      have p12136_2 := h12136c.2.2.1
                                      have p12136_3 := h12136c.2.2.2
                                      linarith only [h11379, h12013, h12024, h12026, h12100, h12135, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12136_1]
                                    · have p12136_0 := h12136c.1
                                      have p12136_1 := h12136c.2.1
                                      have p12136_2 := h12136c.2.2.1
                                      have p12136_3 := h12136c.2.2.2
                                      rcases p12136_3 (m.d 0 1) (by simp) with h12146 | h12146
                                      · linarith only [h0, h12146, hlam]
                                      · linarith only [h12013, h12146, hlam]
                                    · have p12136_0 := h12136c.1
                                      have p12136_1 := h12136c.2.1
                                      have p12136_2 := h12136c.2.2.1
                                      have p12136_3 := h12136c.2.2.2
                                      linarith only [h12013, h12024, h12026, h12100, h12135, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12136_1]
                                    · have p12136_0 := h12136c.1
                                      have p12136_1 := h12136c.2.1
                                      have p12136_2 := h12136c.2.2.1
                                      have p12136_3 := h12136c.2.2.2
                                      linarith only [h12020, hlam, p12136_1]
                                    · have p12136_0 := h12136c.1
                                      have p12136_1 := h12136c.2.1
                                      have p12136_2 := h12136c.2.2.1
                                      have p12136_3 := h12136c.2.2.2
                                      linarith only [hlam, p12136_0]
                                    · have p12136_0 := h12136c.1
                                      have p12136_1 := h12136c.2.1
                                      have p12136_2 := h12136c.2.2.1
                                      have p12136_3 := h12136c.2.2.2
                                      linarith only [h11379, h12013, h12020, h12024, h12026, h12100, h12135, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12136_1]
                                    · have p12136_0 := h12136c.1
                                      have p12136_1 := h12136c.2.1
                                      have p12136_2 := h12136c.2.2.1
                                      have p12136_3 := h12136c.2.2.2
                                      rcases p12136_3 (m.d 0 1) (by simp) with h12153 | h12153
                                      · linarith only [h10472, h12153, hlam]
                                      · linarith only [h12013, h12153, hlam]
                                    · have p12136_0 := h12136c.1
                                      have p12136_1 := h12136c.2.1
                                      have p12136_2 := h12136c.2.2.1
                                      have p12136_3 := h12136c.2.2.2
                                      linarith only [h12013, h12024, h12026, h12100, h12135, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12136_1]
                                    · have p12136_0 := h12136c.1
                                      have p12136_1 := h12136c.2.1
                                      have p12136_2 := h12136c.2.2.1
                                      have p12136_3 := h12136c.2.2.2
                                      linarith only [h12021, hlam, p12136_1]
                                    · have p12136_0 := h12136c.1
                                      have p12136_1 := h12136c.2.1
                                      have p12136_2 := h12136c.2.2.1
                                      have p12136_3 := h12136c.2.2.2
                                      linarith only [h12023, hlam, p12136_0]
                                    · have p12136_0 := h12136c.1
                                      have p12136_1 := h12136c.2.1
                                      have p12136_2 := h12136c.2.2.1
                                      have p12136_3 := h12136c.2.2.2
                                      linarith only [hlam, p12136_0]
                                    · have p12136_0 := h12136c.1
                                      have p12136_1 := h12136c.2.1
                                      have p12136_2 := h12136c.2.2.1
                                      have p12136_3 := h12136c.2.2.2
                                      rcases p12136_3 (m.d 0 1) (by simp) with h12160 | h12160
                                      · linarith only [h11379, h12160, hlam]
                                      · linarith only [h12013, h12160, hlam]
                                    · have p12136_0 := h12136c.1
                                      have p12136_1 := h12136c.2.1
                                      have p12136_2 := h12136c.2.2.1
                                      have p12136_3 := h12136c.2.2.2
                                      linarith only [h12013, hlam, p12136_0]
                                    · have p12136_0 := h12136c.1
                                      have p12136_1 := h12136c.2.1
                                      have p12136_2 := h12136c.2.2.1
                                      have p12136_3 := h12136c.2.2.2
                                      linarith only [h12022, hlam, p12136_1]
                                    · have p12136_0 := h12136c.1
                                      have p12136_1 := h12136c.2.1
                                      have p12136_2 := h12136c.2.2.1
                                      have p12136_3 := h12136c.2.2.2
                                      linarith only [h12024, hlam, p12136_0]
                                    · have p12136_0 := h12136c.1
                                      have p12136_1 := h12136c.2.1
                                      have p12136_2 := h12136c.2.2.1
                                      have p12136_3 := h12136c.2.2.2
                                      linarith only [h12025, hlam, p12136_0]
                                    · have p12136_0 := h12136c.1
                                      have p12136_1 := h12136c.2.1
                                      have p12136_2 := h12136c.2.2.1
                                      have p12136_3 := h12136c.2.2.2
                                      linarith only [hlam, p12136_0]
                                  · linarith only [h11379, h12013, h12020, h12023, h12025, h12026, h12135, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h11379, h12013, h12025, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
                        · linarith only [h11379, h12013, h12023, h12024, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                      · linarith only [h10472, h12013, h12022, h12023, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h10472, h12013, h12020, h12022, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h10472, h12013, h12020, h12021, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h12013, h12020, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h11379, h12013, h12019, hlam]
            · linarith only [h10472, h12013, h12018, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h12177 | h12177
            · rcases m.htr 0 4 5 (by decide) (by decide) with h12178 | h12178
              · rcases m.htr 1 2 3 (by decide) (by decide) with h12179 | h12179
                · rcases m.htr 1 2 4 (by decide) (by decide) with h12180 | h12180
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h12181 | h12181
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h12182 | h12182
                      · linarith only [h10472, h12013, h12017, h12179, h12182, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                      · linarith only [h10472, h12013, h12181, h12182, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h0, h12013, h12181, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h12015, h12180, hlam]
                · linarith only [h0, h12013, h12014, h12017, h12179, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
              · linarith only [h10472, h12013, h12017, h12178, hlam]
            · linarith only [h10472, h12013, h12177, hlam]
        · linarith only [h0, h12013, h12016, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h12191 | h12191
        · rcases m.htr 0 3 4 (by decide) (by decide) with h12192 | h12192
          · linarith only [h12014, h12015, h12192, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h12194 | h12194
            · rcases m.htr 0 4 5 (by decide) (by decide) with h12195 | h12195
              · rcases m.htr 1 2 3 (by decide) (by decide) with h12196 | h12196
                · rcases m.htr 1 2 4 (by decide) (by decide) with h12197 | h12197
                  · linarith only [h10472, h12013, h12014, h12015, h12197, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                  · linarith only [h0, h12013, h12197, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h12013, h12014, h12196, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
              · linarith only [h0, h12013, h12015, h12195, hlam]
            · linarith only [h10472, h12013, h12194, hlam]
        · linarith only [h10472, h12013, h12014, h12191, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h12204 | h12204
      · rcases m.htr 0 2 5 (by decide) (by decide) with h12205 | h12205
        · rcases m.htr 0 3 4 (by decide) (by decide) with h12206 | h12206
          · rcases m.htr 0 3 5 (by decide) (by decide) with h12207 | h12207
            · rcases m.htr 0 4 5 (by decide) (by decide) with h12208 | h12208
              · rcases m.htr 1 2 3 (by decide) (by decide) with h12209 | h12209
                · linarith only [h12014, h12205, h12209, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · linarith only [h0, h12013, h12209, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h11379, h12013, h12208, hlam]
            · linarith only [h11379, h12013, h12014, h12204, h12207, hlam]
          · linarith only [h12014, h12204, h12206, hlam]
        · linarith only [h11379, h12013, h12204, h12205, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h12216 | h12216
        · rcases m.htr 0 3 4 (by decide) (by decide) with h12217 | h12217
          · rcases m.htr 0 3 5 (by decide) (by decide) with h12218 | h12218
            · rcases m.htr 0 4 5 (by decide) (by decide) with h12219 | h12219
              · rcases m.htr 1 2 3 (by decide) (by decide) with h12220 | h12220
                · linarith only [h0, h12013, h12014, h12220, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                · linarith only [h0, h12013, h12220, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h12013, h12204, h12219, hlam]
            · linarith only [h0, h12013, h12204, h12217, h12218, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h12225 | h12225
            · rcases m.htr 0 4 5 (by decide) (by decide) with h12226 | h12226
              · rcases m.htr 1 2 3 (by decide) (by decide) with h12227 | h12227
                · linarith only [h0, h12013, h12014, h12227, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                · linarith only [h0, h12013, h12227, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h11379, h12013, h12226, hlam]
            · linarith only [h10472, h12013, h12225, hlam]
        · linarith only [h0, h12013, h12216, hlam]
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s15 m hb1 hb3 hb5 h0 h10472 h11379 h12013

set_option maxHeartbeats 9748000 in
set_option maxHeartbeats 9748000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s13 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h10472 := hg10472
  rcases m.htr 0 1 4 (by decide) (by decide) with h11379 | h11379
  · rcases m.htr 0 1 5 (by decide) (by decide) with h11380 | h11380
    · rcases m.htr 0 2 3 (by decide) (by decide) with h11381 | h11381
      · rcases m.htr 0 2 4 (by decide) (by decide) with h11382 | h11382
        · rcases m.htr 0 2 5 (by decide) (by decide) with h11383 | h11383
          · rcases m.htr 0 3 4 (by decide) (by decide) with h11384 | h11384
            · rcases m.htr 0 3 5 (by decide) (by decide) with h11385 | h11385
              · rcases m.htr 0 4 5 (by decide) (by decide) with h11386 | h11386
                · rcases m.htr 1 2 3 (by decide) (by decide) with h11387 | h11387
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h11388 | h11388
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h11389 | h11389
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11390 | h11390
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h11391 | h11391
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h11392 | h11392
                            · linarith only [h10472, h11379, h11392, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h11394 | h11394
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h11395 | h11395
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h11396 | h11396
                                  · linarith only [h11388, h11392, h11396, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h11398 | h11398
                                    · linarith only [h11388, h11392, h11394, h11398, hlam]
                                    · rcases h1bigk with h11400c | h11400c | h11400c | h11400c | h11400c | h11400c | h11400c | h11400c | h11400c | h11400c | h11400c | h11400c | h11400c | h11400c | h11400c | h11400c | h11400c | h11400c | h11400c | h11400c | h11400c | h11400c | h11400c | h11400c | h11400c
                                      · have p11400_0 := h11400c.1
                                        have p11400_1 := h11400c.2.1
                                        have p11400_2 := h11400c.2.2.1
                                        have p11400_3 := h11400c.2.2.2
                                        linarith only [hlam, p11400_0]
                                      · have p11400_0 := h11400c.1
                                        have p11400_1 := h11400c.2.1
                                        have p11400_2 := h11400c.2.2.1
                                        have p11400_3 := h11400c.2.2.2
                                        linarith only [h0, hlam, p11400_0]
                                      · have p11400_0 := h11400c.1
                                        have p11400_1 := h11400c.2.1
                                        have p11400_2 := h11400c.2.2.1
                                        have p11400_3 := h11400c.2.2.2
                                        linarith only [h10472, hlam, p11400_0]
                                      · have p11400_0 := h11400c.1
                                        have p11400_1 := h11400c.2.1
                                        have p11400_2 := h11400c.2.2.1
                                        have p11400_3 := h11400c.2.2.2
                                        rcases p11400_3 (m.d 0 1) (by simp) with h11404 | h11404
                                        · rcases p11400_3 (m.d 1 2) (by simp) with h11405 | h11405
                                          · rcases p11400_3 (m.d 1 3) (by simp) with h11406 | h11406
                                            · rcases p11400_3 (m.d 1 4) (by simp) with h11407 | h11407
                                              · linarith only [h11407, hlam, p11400_0]
                                              · rcases p11400_3 (m.d 1 5) (by simp) with h11409 | h11409
                                                · linarith only [h11380, h11409, hlam]
                                                · linarith only [h11392, h11409, hlam]
                                            · linarith only [h11390, h11406, hlam]
                                          · linarith only [h11388, h11405, hlam]
                                        · linarith only [h11404, hlam, p11400_0]
                                      · have p11400_0 := h11400c.1
                                        have p11400_1 := h11400c.2.1
                                        have p11400_2 := h11400c.2.2.1
                                        have p11400_3 := h11400c.2.2.2
                                        linarith only [h10472, h11387, hc12, hlam, hphi, ht01, ht0b, ht5b, p11400_1, u5ehi1]
                                      · have p11400_0 := h11400c.1
                                        have p11400_1 := h11400c.2.1
                                        have p11400_2 := h11400c.2.2.1
                                        have p11400_3 := h11400c.2.2.2
                                        linarith only [h11379, h11386, h11392, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p11400_1]
                                      · have p11400_0 := h11400c.1
                                        have p11400_1 := h11400c.2.1
                                        have p11400_2 := h11400c.2.2.1
                                        have p11400_3 := h11400c.2.2.2
                                        linarith only [hlam, p11400_0]
                                      · have p11400_0 := h11400c.1
                                        have p11400_1 := h11400c.2.1
                                        have p11400_2 := h11400c.2.2.1
                                        have p11400_3 := h11400c.2.2.2
                                        linarith only [h10472, h11379, h11386, h11388, h11392, h11394, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11400_1]
                                      · have p11400_0 := h11400c.1
                                        have p11400_1 := h11400c.2.1
                                        have p11400_2 := h11400c.2.2.1
                                        have p11400_3 := h11400c.2.2.2
                                        linarith only [h0, h11379, h11386, h11392, hlam, p11400_2]
                                      · have p11400_0 := h11400c.1
                                        have p11400_1 := h11400c.2.1
                                        have p11400_2 := h11400c.2.2.1
                                        have p11400_3 := h11400c.2.2.2
                                        rcases p11400_3 (m.d 0 1) (by simp) with h11420 | h11420
                                        · linarith only [h0, h11420, hlam]
                                        · linarith only [h11380, h11420, hlam]
                                      · have p11400_0 := h11400c.1
                                        have p11400_1 := h11400c.2.1
                                        have p11400_2 := h11400c.2.2.1
                                        have p11400_3 := h11400c.2.2.2
                                        linarith only [h11379, h11386, h11387, h11388, h11392, h11394, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11400_1]
                                      · have p11400_0 := h11400c.1
                                        have p11400_1 := h11400c.2.1
                                        have p11400_2 := h11400c.2.2.1
                                        have p11400_3 := h11400c.2.2.2
                                        linarith only [h11387, hlam, p11400_1]
                                      · have p11400_0 := h11400c.1
                                        have p11400_1 := h11400c.2.1
                                        have p11400_2 := h11400c.2.2.1
                                        have p11400_3 := h11400c.2.2.2
                                        linarith only [hlam, p11400_0]
                                      · have p11400_0 := h11400c.1
                                        have p11400_1 := h11400c.2.1
                                        have p11400_2 := h11400c.2.2.1
                                        have p11400_3 := h11400c.2.2.2
                                        linarith only [h10472, h11379, h11386, h11392, hlam, p11400_2]
                                      · have p11400_0 := h11400c.1
                                        have p11400_1 := h11400c.2.1
                                        have p11400_2 := h11400c.2.2.1
                                        have p11400_3 := h11400c.2.2.2
                                        rcases p11400_3 (m.d 0 1) (by simp) with h11427 | h11427
                                        · linarith only [h10472, h11427, hlam]
                                        · linarith only [h11380, h11427, hlam]
                                      · have p11400_0 := h11400c.1
                                        have p11400_1 := h11400c.2.1
                                        have p11400_2 := h11400c.2.2.1
                                        have p11400_3 := h11400c.2.2.2
                                        linarith only [h11379, hlam, p11400_0]
                                      · have p11400_0 := h11400c.1
                                        have p11400_1 := h11400c.2.1
                                        have p11400_2 := h11400c.2.2.1
                                        have p11400_3 := h11400c.2.2.2
                                        linarith only [h11388, hlam, p11400_1]
                                      · have p11400_0 := h11400c.1
                                        have p11400_1 := h11400c.2.1
                                        have p11400_2 := h11400c.2.2.1
                                        have p11400_3 := h11400c.2.2.2
                                        linarith only [h11390, hlam, p11400_0]
                                      · have p11400_0 := h11400c.1
                                        have p11400_1 := h11400c.2.1
                                        have p11400_2 := h11400c.2.2.1
                                        have p11400_3 := h11400c.2.2.2
                                        linarith only [hlam, p11400_0]
                                      · have p11400_0 := h11400c.1
                                        have p11400_1 := h11400c.2.1
                                        have p11400_2 := h11400c.2.2.1
                                        have p11400_3 := h11400c.2.2.2
                                        linarith only [h11392, hlam, p11400_1]
                                      · have p11400_0 := h11400c.1
                                        have p11400_1 := h11400c.2.1
                                        have p11400_2 := h11400c.2.2.1
                                        have p11400_3 := h11400c.2.2.2
                                        linarith only [h11380, hlam, p11400_0]
                                      · have p11400_0 := h11400c.1
                                        have p11400_1 := h11400c.2.1
                                        have p11400_2 := h11400c.2.2.1
                                        have p11400_3 := h11400c.2.2.2
                                        linarith only [h11389, hlam, p11400_1]
                                      · have p11400_0 := h11400c.1
                                        have p11400_1 := h11400c.2.1
                                        have p11400_2 := h11400c.2.2.1
                                        have p11400_3 := h11400c.2.2.2
                                        linarith only [h11391, hlam, p11400_0]
                                      · have p11400_0 := h11400c.1
                                        have p11400_1 := h11400c.2.1
                                        have p11400_2 := h11400c.2.2.1
                                        have p11400_3 := h11400c.2.2.2
                                        linarith only [h10472, h11380, h11388, h11394, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11400_1]
                                      · have p11400_0 := h11400c.1
                                        have p11400_1 := h11400c.2.1
                                        have p11400_2 := h11400c.2.2.1
                                        have p11400_3 := h11400c.2.2.2
                                        linarith only [hlam, p11400_0]
                                · linarith only [h10472, h11379, h11386, h11387, h11391, h11392, h11394, h11395, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h10472, h11379, h11386, h11387, h11390, h11392, h11394, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h10472, h11379, h11386, h11391, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                        · linarith only [h10472, h11379, h11386, h11390, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · linarith only [h0, h11379, h11386, h11389, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · linarith only [h10472, h11379, h11386, h11387, h11388, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · linarith only [h0, h11379, h11386, h11387, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h11447 | h11447
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h11448 | h11448
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h11449 | h11449
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11450 | h11450
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h11451 | h11451
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h11452 | h11452
                            · linarith only [h10472, h11379, h11386, h11447, h11452, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h11454 | h11454
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h11455 | h11455
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h11456 | h11456
                                  · linarith only [h11379, h11386, h11448, h11456, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h11458 | h11458
                                    · linarith only [h11381, h11386, h11454, h11458, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                                    · rcases h1bigk with h11460c | h11460c | h11460c | h11460c | h11460c | h11460c | h11460c | h11460c | h11460c | h11460c | h11460c | h11460c | h11460c | h11460c | h11460c | h11460c | h11460c | h11460c | h11460c | h11460c | h11460c | h11460c | h11460c | h11460c | h11460c
                                      · have p11460_0 := h11460c.1
                                        have p11460_1 := h11460c.2.1
                                        have p11460_2 := h11460c.2.2.1
                                        have p11460_3 := h11460c.2.2.2
                                        linarith only [hlam, p11460_0]
                                      · have p11460_0 := h11460c.1
                                        have p11460_1 := h11460c.2.1
                                        have p11460_2 := h11460c.2.2.1
                                        have p11460_3 := h11460c.2.2.2
                                        linarith only [h0, hlam, p11460_0]
                                      · have p11460_0 := h11460c.1
                                        have p11460_1 := h11460c.2.1
                                        have p11460_2 := h11460c.2.2.1
                                        have p11460_3 := h11460c.2.2.2
                                        linarith only [h10472, hlam, p11460_0]
                                      · have p11460_0 := h11460c.1
                                        have p11460_1 := h11460c.2.1
                                        have p11460_2 := h11460c.2.2.1
                                        have p11460_3 := h11460c.2.2.2
                                        rcases p11460_3 (m.d 0 1) (by simp) with h11464 | h11464
                                        · rcases p11460_3 (m.d 1 2) (by simp) with h11465 | h11465
                                          · rcases p11460_3 (m.d 1 3) (by simp) with h11466 | h11466
                                            · rcases p11460_3 (m.d 1 4) (by simp) with h11467 | h11467
                                              · linarith only [h11467, hlam, p11460_0]
                                              · rcases p11460_3 (m.d 1 5) (by simp) with h11469 | h11469
                                                · linarith only [h11380, h11469, hlam]
                                                · linarith only [h11452, h11469, hlam]
                                            · linarith only [h11450, h11466, hlam]
                                          · linarith only [h11448, h11465, hlam]
                                        · linarith only [h11464, hlam, p11460_0]
                                      · have p11460_0 := h11460c.1
                                        have p11460_1 := h11460c.2.1
                                        have p11460_2 := h11460c.2.2.1
                                        have p11460_3 := h11460c.2.2.2
                                        linarith only [h10472, h11447, hc12, hlam, hphi, ht01, ht0b, ht5b, p11460_1, u5ehi1]
                                      · have p11460_0 := h11460c.1
                                        have p11460_1 := h11460c.2.1
                                        have p11460_2 := h11460c.2.2.1
                                        have p11460_3 := h11460c.2.2.2
                                        linarith only [h11380, h11449, hc12, hlam, hphi, ht01, ht0b, ht5b, p11460_1, u5ehi2]
                                      · have p11460_0 := h11460c.1
                                        have p11460_1 := h11460c.2.1
                                        have p11460_2 := h11460c.2.2.1
                                        have p11460_3 := h11460c.2.2.2
                                        linarith only [hlam, p11460_0]
                                      · have p11460_0 := h11460c.1
                                        have p11460_1 := h11460c.2.1
                                        have p11460_2 := h11460c.2.2.1
                                        have p11460_3 := h11460c.2.2.2
                                        linarith only [h10472, hc01, hc12, hlam, hphi, p11460_1]
                                      · have p11460_0 := h11460c.1
                                        have p11460_1 := h11460c.2.1
                                        have p11460_2 := h11460c.2.2.1
                                        have p11460_3 := h11460c.2.2.2
                                        rcases p11460_3 (m.d 0 1) (by simp) with h11479 | h11479
                                        · linarith only [h0, h11479, hlam]
                                        · linarith only [h11379, h11479, hlam]
                                      · have p11460_0 := h11460c.1
                                        have p11460_1 := h11460c.2.1
                                        have p11460_2 := h11460c.2.2.1
                                        have p11460_3 := h11460c.2.2.2
                                        rcases p11460_3 (m.d 0 1) (by simp) with h11482 | h11482
                                        · linarith only [h0, h11482, hlam]
                                        · linarith only [h11380, h11482, hlam]
                                      · have p11460_0 := h11460c.1
                                        have p11460_1 := h11460c.2.1
                                        have p11460_2 := h11460c.2.2.1
                                        have p11460_3 := h11460c.2.2.2
                                        linarith only [h11380, h11447, h11449, h11455, hc12, hlam, hphi, ht01, ht0b, ht5b, p11460_1, u5ehi3]
                                      · have p11460_0 := h11460c.1
                                        have p11460_1 := h11460c.2.1
                                        have p11460_2 := h11460c.2.2.1
                                        have p11460_3 := h11460c.2.2.2
                                        linarith only [h11447, hlam, p11460_1]
                                      · have p11460_0 := h11460c.1
                                        have p11460_1 := h11460c.2.1
                                        have p11460_2 := h11460c.2.2.1
                                        have p11460_3 := h11460c.2.2.2
                                        linarith only [hlam, p11460_0]
                                      · have p11460_0 := h11460c.1
                                        have p11460_1 := h11460c.2.1
                                        have p11460_2 := h11460c.2.2.1
                                        have p11460_3 := h11460c.2.2.2
                                        rcases p11460_3 (m.d 0 1) (by simp) with h11488 | h11488
                                        · linarith only [h10472, h11488, hlam]
                                        · linarith only [h11379, h11488, hlam]
                                      · have p11460_0 := h11460c.1
                                        have p11460_1 := h11460c.2.1
                                        have p11460_2 := h11460c.2.2.1
                                        have p11460_3 := h11460c.2.2.2
                                        rcases p11460_3 (m.d 0 1) (by simp) with h11491 | h11491
                                        · linarith only [h10472, h11491, hlam]
                                        · linarith only [h11380, h11491, hlam]
                                      · have p11460_0 := h11460c.1
                                        have p11460_1 := h11460c.2.1
                                        have p11460_2 := h11460c.2.2.1
                                        have p11460_3 := h11460c.2.2.2
                                        linarith only [h11379, hlam, p11460_0]
                                      · have p11460_0 := h11460c.1
                                        have p11460_1 := h11460c.2.1
                                        have p11460_2 := h11460c.2.2.1
                                        have p11460_3 := h11460c.2.2.2
                                        linarith only [h11448, hlam, p11460_1]
                                      · have p11460_0 := h11460c.1
                                        have p11460_1 := h11460c.2.1
                                        have p11460_2 := h11460c.2.2.1
                                        have p11460_3 := h11460c.2.2.2
                                        linarith only [h11450, hlam, p11460_0]
                                      · have p11460_0 := h11460c.1
                                        have p11460_1 := h11460c.2.1
                                        have p11460_2 := h11460c.2.2.1
                                        have p11460_3 := h11460c.2.2.2
                                        linarith only [hlam, p11460_0]
                                      · have p11460_0 := h11460c.1
                                        have p11460_1 := h11460c.2.1
                                        have p11460_2 := h11460c.2.2.1
                                        have p11460_3 := h11460c.2.2.2
                                        linarith only [h11452, hlam, p11460_1]
                                      · have p11460_0 := h11460c.1
                                        have p11460_1 := h11460c.2.1
                                        have p11460_2 := h11460c.2.2.1
                                        have p11460_3 := h11460c.2.2.2
                                        linarith only [h11380, hlam, p11460_0]
                                      · have p11460_0 := h11460c.1
                                        have p11460_1 := h11460c.2.1
                                        have p11460_2 := h11460c.2.2.1
                                        have p11460_3 := h11460c.2.2.2
                                        linarith only [h11449, hlam, p11460_1]
                                      · have p11460_0 := h11460c.1
                                        have p11460_1 := h11460c.2.1
                                        have p11460_2 := h11460c.2.2.1
                                        have p11460_3 := h11460c.2.2.2
                                        linarith only [h11451, hlam, p11460_0]
                                      · have p11460_0 := h11460c.1
                                        have p11460_1 := h11460c.2.1
                                        have p11460_2 := h11460c.2.2.1
                                        have p11460_3 := h11460c.2.2.2
                                        linarith only [h0, h11380, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p11460_1]
                                      · have p11460_0 := h11460c.1
                                        have p11460_1 := h11460c.2.1
                                        have p11460_2 := h11460c.2.2.1
                                        have p11460_3 := h11460c.2.2.2
                                        linarith only [hlam, p11460_0]
                                · linarith only [h10472, h11380, h11447, h11451, h11454, h11455, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h11505 | h11505
                                · linarith only [h10472, h11380, h11447, h11450, h11452, h11454, h11505, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h11507 | h11507
                                  · linarith only [h11379, h11386, h11450, h11454, h11507, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h11509 | h11509
                                    · linarith only [h11379, h11386, h11450, h11509, hlam]
                                    · rcases h1bigk with h11511c | h11511c | h11511c | h11511c | h11511c | h11511c | h11511c | h11511c | h11511c | h11511c | h11511c | h11511c | h11511c | h11511c | h11511c | h11511c | h11511c | h11511c | h11511c | h11511c | h11511c | h11511c | h11511c | h11511c | h11511c
                                      · have p11511_0 := h11511c.1
                                        have p11511_1 := h11511c.2.1
                                        have p11511_2 := h11511c.2.2.1
                                        have p11511_3 := h11511c.2.2.2
                                        linarith only [hlam, p11511_0]
                                      · have p11511_0 := h11511c.1
                                        have p11511_1 := h11511c.2.1
                                        have p11511_2 := h11511c.2.2.1
                                        have p11511_3 := h11511c.2.2.2
                                        linarith only [h0, hlam, p11511_0]
                                      · have p11511_0 := h11511c.1
                                        have p11511_1 := h11511c.2.1
                                        have p11511_2 := h11511c.2.2.1
                                        have p11511_3 := h11511c.2.2.2
                                        linarith only [h10472, hlam, p11511_0]
                                      · have p11511_0 := h11511c.1
                                        have p11511_1 := h11511c.2.1
                                        have p11511_2 := h11511c.2.2.1
                                        have p11511_3 := h11511c.2.2.2
                                        linarith only [h10472, h11447, h11450, h11454, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11511_1]
                                      · have p11511_0 := h11511c.1
                                        have p11511_1 := h11511c.2.1
                                        have p11511_2 := h11511c.2.2.1
                                        have p11511_3 := h11511c.2.2.2
                                        linarith only [h10472, h11447, hc12, hlam, hphi, ht01, ht0b, ht5b, p11511_1, u5ehi1]
                                      · have p11511_0 := h11511c.1
                                        have p11511_1 := h11511c.2.1
                                        have p11511_2 := h11511c.2.2.1
                                        have p11511_3 := h11511c.2.2.2
                                        linarith only [h11379, h11450, h11454, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11511_1]
                                      · have p11511_0 := h11511c.1
                                        have p11511_1 := h11511c.2.1
                                        have p11511_2 := h11511c.2.2.1
                                        have p11511_3 := h11511c.2.2.2
                                        linarith only [hlam, p11511_0]
                                      · have p11511_0 := h11511c.1
                                        have p11511_1 := h11511c.2.1
                                        have p11511_2 := h11511c.2.2.1
                                        have p11511_3 := h11511c.2.2.2
                                        linarith only [h10472, hc01, hc12, hlam, hphi, p11511_1]
                                      · have p11511_0 := h11511c.1
                                        have p11511_1 := h11511c.2.1
                                        have p11511_2 := h11511c.2.2.1
                                        have p11511_3 := h11511c.2.2.2
                                        rcases p11511_3 (m.d 0 1) (by simp) with h11520 | h11520
                                        · linarith only [h0, h11520, hlam]
                                        · linarith only [h11379, h11520, hlam]
                                      · have p11511_0 := h11511c.1
                                        have p11511_1 := h11511c.2.1
                                        have p11511_2 := h11511c.2.2.1
                                        have p11511_3 := h11511c.2.2.2
                                        rcases p11511_3 (m.d 0 1) (by simp) with h11523 | h11523
                                        · linarith only [h0, h11523, hlam]
                                        · linarith only [h11380, h11523, hlam]
                                      · have p11511_0 := h11511c.1
                                        have p11511_1 := h11511c.2.1
                                        have p11511_2 := h11511c.2.2.1
                                        have p11511_3 := h11511c.2.2.2
                                        linarith only [h11380, hc13, hlam, hphi, ht01, ht0b, ht5b, p11511_1, u5ehi1]
                                      · have p11511_0 := h11511c.1
                                        have p11511_1 := h11511c.2.1
                                        have p11511_2 := h11511c.2.2.1
                                        have p11511_3 := h11511c.2.2.2
                                        linarith only [h11447, hlam, p11511_1]
                                      · have p11511_0 := h11511c.1
                                        have p11511_1 := h11511c.2.1
                                        have p11511_2 := h11511c.2.2.1
                                        have p11511_3 := h11511c.2.2.2
                                        linarith only [hlam, p11511_0]
                                      · have p11511_0 := h11511c.1
                                        have p11511_1 := h11511c.2.1
                                        have p11511_2 := h11511c.2.2.1
                                        have p11511_3 := h11511c.2.2.2
                                        rcases p11511_3 (m.d 0 1) (by simp) with h11529 | h11529
                                        · linarith only [h10472, h11529, hlam]
                                        · linarith only [h11379, h11529, hlam]
                                      · have p11511_0 := h11511c.1
                                        have p11511_1 := h11511c.2.1
                                        have p11511_2 := h11511c.2.2.1
                                        have p11511_3 := h11511c.2.2.2
                                        rcases p11511_3 (m.d 0 1) (by simp) with h11532 | h11532
                                        · linarith only [h10472, h11532, hlam]
                                        · linarith only [h11380, h11532, hlam]
                                      · have p11511_0 := h11511c.1
                                        have p11511_1 := h11511c.2.1
                                        have p11511_2 := h11511c.2.2.1
                                        have p11511_3 := h11511c.2.2.2
                                        linarith only [h11379, hlam, p11511_0]
                                      · have p11511_0 := h11511c.1
                                        have p11511_1 := h11511c.2.1
                                        have p11511_2 := h11511c.2.2.1
                                        have p11511_3 := h11511c.2.2.2
                                        linarith only [h11448, hlam, p11511_1]
                                      · have p11511_0 := h11511c.1
                                        have p11511_1 := h11511c.2.1
                                        have p11511_2 := h11511c.2.2.1
                                        have p11511_3 := h11511c.2.2.2
                                        linarith only [h11450, hlam, p11511_0]
                                      · have p11511_0 := h11511c.1
                                        have p11511_1 := h11511c.2.1
                                        have p11511_2 := h11511c.2.2.1
                                        have p11511_3 := h11511c.2.2.2
                                        linarith only [hlam, p11511_0]
                                      · have p11511_0 := h11511c.1
                                        have p11511_1 := h11511c.2.1
                                        have p11511_2 := h11511c.2.2.1
                                        have p11511_3 := h11511c.2.2.2
                                        linarith only [h11452, hlam, p11511_1]
                                      · have p11511_0 := h11511c.1
                                        have p11511_1 := h11511c.2.1
                                        have p11511_2 := h11511c.2.2.1
                                        have p11511_3 := h11511c.2.2.2
                                        linarith only [h11380, hlam, p11511_0]
                                      · have p11511_0 := h11511c.1
                                        have p11511_1 := h11511c.2.1
                                        have p11511_2 := h11511c.2.2.1
                                        have p11511_3 := h11511c.2.2.2
                                        linarith only [h11449, hlam, p11511_1]
                                      · have p11511_0 := h11511c.1
                                        have p11511_1 := h11511c.2.1
                                        have p11511_2 := h11511c.2.2.1
                                        have p11511_3 := h11511c.2.2.2
                                        linarith only [h11451, hlam, p11511_0]
                                      · have p11511_0 := h11511c.1
                                        have p11511_1 := h11511c.2.1
                                        have p11511_2 := h11511c.2.2.1
                                        have p11511_3 := h11511c.2.2.2
                                        linarith only [h11380, h11450, h11454, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p11511_1]
                                      · have p11511_0 := h11511c.1
                                        have p11511_1 := h11511c.2.1
                                        have p11511_2 := h11511c.2.2.1
                                        have p11511_3 := h11511c.2.2.2
                                        linarith only [hlam, p11511_0]
                          · linarith only [h10472, h11380, h11451, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                        · linarith only [h10472, h11380, h11384, h11449, h11450, hc04, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · linarith only [h0, h11380, h11449, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h10472, h11380, h11447, h11448, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h11380, h11447, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h10472, h11380, h11385, hlam]
            · linarith only [h10472, h11379, h11384, hlam]
          · linarith only [h0, h11380, h11383, hlam]
        · linarith only [h10472, h11379, h11381, h11382, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h11554 | h11554
        · rcases m.htr 0 2 5 (by decide) (by decide) with h11555 | h11555
          · rcases m.htr 0 3 4 (by decide) (by decide) with h11556 | h11556
            · rcases m.htr 0 3 5 (by decide) (by decide) with h11557 | h11557
              · rcases m.htr 0 4 5 (by decide) (by decide) with h11558 | h11558
                · rcases m.htr 1 2 3 (by decide) (by decide) with h11559 | h11559
                  · linarith only [h11381, h11555, h11559, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · linarith only [h0, h11379, h11558, h11559, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h11562 | h11562
                  · linarith only [h0, h11380, h11381, h11562, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                  · linarith only [h0, h11380, h11562, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h11380, h11381, h11557, hlam]
            · linarith only [h0, h11379, h11381, h11556, hlam]
          · linarith only [h0, h11380, h11555, hlam]
        · linarith only [h0, h11379, h11554, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h11569 | h11569
      · rcases m.htr 0 2 4 (by decide) (by decide) with h11570 | h11570
        · rcases m.htr 0 2 5 (by decide) (by decide) with h11571 | h11571
          · rcases m.htr 0 3 4 (by decide) (by decide) with h11572 | h11572
            · rcases m.htr 0 3 5 (by decide) (by decide) with h11573 | h11573
              · rcases m.htr 0 4 5 (by decide) (by decide) with h11574 | h11574
                · linarith only [h11379, h11380, h11574, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h11576 | h11576
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h11577 | h11577
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h11578 | h11578
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11579 | h11579
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h11580 | h11580
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h11581 | h11581
                            · linarith only [h11379, h11380, h11574, h11576, h11580, h11581, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h11583 | h11583
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h11584 | h11584
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h11585 | h11585
                                  · linarith only [h11379, h11380, h11577, h11581, h11585, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h11587 | h11587
                                    · linarith only [h11380, h11569, h11581, h11583, h11587, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                    · rcases h1bigk with h11589c | h11589c | h11589c | h11589c | h11589c | h11589c | h11589c | h11589c | h11589c | h11589c | h11589c | h11589c | h11589c | h11589c | h11589c | h11589c | h11589c | h11589c | h11589c | h11589c | h11589c | h11589c | h11589c | h11589c | h11589c
                                      · have p11589_0 := h11589c.1
                                        have p11589_1 := h11589c.2.1
                                        have p11589_2 := h11589c.2.2.1
                                        have p11589_3 := h11589c.2.2.2
                                        linarith only [hlam, p11589_0]
                                      · have p11589_0 := h11589c.1
                                        have p11589_1 := h11589c.2.1
                                        have p11589_2 := h11589c.2.2.1
                                        have p11589_3 := h11589c.2.2.2
                                        linarith only [h0, hlam, p11589_0]
                                      · have p11589_0 := h11589c.1
                                        have p11589_1 := h11589c.2.1
                                        have p11589_2 := h11589c.2.2.1
                                        have p11589_3 := h11589c.2.2.2
                                        linarith only [h10472, hlam, p11589_0]
                                      · have p11589_0 := h11589c.1
                                        have p11589_1 := h11589c.2.1
                                        have p11589_2 := h11589c.2.2.1
                                        have p11589_3 := h11589c.2.2.2
                                        linarith only [h11380, h11577, h11581, h11583, hc34, hc45, hlam, hphi, p11589_1]
                                      · have p11589_0 := h11589c.1
                                        have p11589_1 := h11589c.2.1
                                        have p11589_2 := h11589c.2.2.1
                                        have p11589_3 := h11589c.2.2.2
                                        linarith only [h11380, hlam, p11589_0]
                                      · have p11589_0 := h11589c.1
                                        have p11589_1 := h11589c.2.1
                                        have p11589_2 := h11589c.2.2.1
                                        have p11589_3 := h11589c.2.2.2
                                        rcases p11589_3 (m.d 0 1) (by simp) with h11595 | h11595
                                        · linarith only [h11595, hlam, p11589_0]
                                        · rcases p11589_3 (m.d 1 2) (by simp) with h11597 | h11597
                                          · rcases p11589_3 (m.d 1 3) (by simp) with h11598 | h11598
                                            · linarith only [h11576, h11598, hlam]
                                            · linarith only [h10472, h11598, hlam]
                                          · linarith only [h11597, hlam, p11589_0]
                                      · have p11589_0 := h11589c.1
                                        have p11589_1 := h11589c.2.1
                                        have p11589_2 := h11589c.2.2.1
                                        have p11589_3 := h11589c.2.2.2
                                        linarith only [hlam, p11589_0]
                                      · have p11589_0 := h11589c.1
                                        have p11589_1 := h11589c.2.1
                                        have p11589_2 := h11589c.2.2.1
                                        have p11589_3 := h11589c.2.2.2
                                        linarith only [h10472, hc01, hc12, hlam, hphi, p11589_1]
                                      · have p11589_0 := h11589c.1
                                        have p11589_1 := h11589c.2.1
                                        have p11589_2 := h11589c.2.2.1
                                        have p11589_3 := h11589c.2.2.2
                                        rcases p11589_3 (m.d 0 1) (by simp) with h11604 | h11604
                                        · linarith only [h0, h11604, hlam]
                                        · linarith only [h11379, h11604, hlam]
                                      · have p11589_0 := h11589c.1
                                        have p11589_1 := h11589c.2.1
                                        have p11589_2 := h11589c.2.2.1
                                        have p11589_3 := h11589c.2.2.2
                                        linarith only [h11379, h11380, h11577, h11583, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11589_1]
                                      · have p11589_0 := h11589c.1
                                        have p11589_1 := h11589c.2.1
                                        have p11589_2 := h11589c.2.2.1
                                        have p11589_3 := h11589c.2.2.2
                                        rcases p11589_3 (m.d 0 1) (by simp) with h11608 | h11608
                                        · linarith only [h11608, hlam, p11589_0]
                                        · rcases p11589_3 (m.d 1 2) (by simp) with h11610 | h11610
                                          · rcases p11589_3 (m.d 1 3) (by simp) with h11611 | h11611
                                            · rcases p11589_3 (m.d 1 4) (by simp) with h11612 | h11612
                                              · linarith only [h11579, h11612, hlam]
                                              · rcases p11589_3 (m.d 1 5) (by simp) with h11614 | h11614
                                                · linarith only [h11580, h11614, hlam]
                                                · linarith only [h11380, h11614, hlam]
                                            · linarith only [h11611, hlam, p11589_0]
                                          · linarith only [h0, h11610, hlam]
                                      · have p11589_0 := h11589c.1
                                        have p11589_1 := h11589c.2.1
                                        have p11589_2 := h11589c.2.2.1
                                        have p11589_3 := h11589c.2.2.2
                                        linarith only [h11576, hlam, p11589_1]
                                      · have p11589_0 := h11589c.1
                                        have p11589_1 := h11589c.2.1
                                        have p11589_2 := h11589c.2.2.1
                                        have p11589_3 := h11589c.2.2.2
                                        linarith only [hlam, p11589_0]
                                      · have p11589_0 := h11589c.1
                                        have p11589_1 := h11589c.2.1
                                        have p11589_2 := h11589c.2.2.1
                                        have p11589_3 := h11589c.2.2.2
                                        rcases p11589_3 (m.d 0 1) (by simp) with h11621 | h11621
                                        · linarith only [h10472, h11621, hlam]
                                        · linarith only [h11379, h11621, hlam]
                                      · have p11589_0 := h11589c.1
                                        have p11589_1 := h11589c.2.1
                                        have p11589_2 := h11589c.2.2.1
                                        have p11589_3 := h11589c.2.2.2
                                        linarith only [h11379, h11380, h11577, h11583, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11589_1]
                                      · have p11589_0 := h11589c.1
                                        have p11589_1 := h11589c.2.1
                                        have p11589_2 := h11589c.2.2.1
                                        have p11589_3 := h11589c.2.2.2
                                        linarith only [h11379, hlam, p11589_0]
                                      · have p11589_0 := h11589c.1
                                        have p11589_1 := h11589c.2.1
                                        have p11589_2 := h11589c.2.2.1
                                        have p11589_3 := h11589c.2.2.2
                                        linarith only [h11577, hlam, p11589_1]
                                      · have p11589_0 := h11589c.1
                                        have p11589_1 := h11589c.2.1
                                        have p11589_2 := h11589c.2.2.1
                                        have p11589_3 := h11589c.2.2.2
                                        linarith only [h11579, hlam, p11589_0]
                                      · have p11589_0 := h11589c.1
                                        have p11589_1 := h11589c.2.1
                                        have p11589_2 := h11589c.2.2.1
                                        have p11589_3 := h11589c.2.2.2
                                        linarith only [hlam, p11589_0]
                                      · have p11589_0 := h11589c.1
                                        have p11589_1 := h11589c.2.1
                                        have p11589_2 := h11589c.2.2.1
                                        have p11589_3 := h11589c.2.2.2
                                        linarith only [h11581, hlam, p11589_1]
                                      · have p11589_0 := h11589c.1
                                        have p11589_1 := h11589c.2.1
                                        have p11589_2 := h11589c.2.2.1
                                        have p11589_3 := h11589c.2.2.2
                                        linarith only [h11379, h11577, h11581, h11583, hc34, hc45, hlam, hphi, p11589_1]
                                      · have p11589_0 := h11589c.1
                                        have p11589_1 := h11589c.2.1
                                        have p11589_2 := h11589c.2.2.1
                                        have p11589_3 := h11589c.2.2.2
                                        linarith only [h11578, hlam, p11589_1]
                                      · have p11589_0 := h11589c.1
                                        have p11589_1 := h11589c.2.1
                                        have p11589_2 := h11589c.2.2.1
                                        have p11589_3 := h11589c.2.2.2
                                        linarith only [h11580, hlam, p11589_0]
                                      · have p11589_0 := h11589c.1
                                        have p11589_1 := h11589c.2.1
                                        have p11589_2 := h11589c.2.2.1
                                        have p11589_3 := h11589c.2.2.2
                                        rcases p11589_3 (m.d 0 1) (by simp) with h11633 | h11633
                                        · linarith only [h11380, h11633, hlam]
                                        · linarith only [h11379, h11633, hlam]
                                      · have p11589_0 := h11589c.1
                                        have p11589_1 := h11589c.2.1
                                        have p11589_2 := h11589c.2.2.1
                                        have p11589_3 := h11589c.2.2.2
                                        linarith only [hlam, p11589_0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h11637 | h11637
                                  · linarith only [h0, h11379, h11577, h11581, h11637, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h11639 | h11639
                                    · linarith only [h11380, h11569, h11573, h11581, h11583, h11584, h11639, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                    · rcases h1bigk with h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c | h11641c
                                      · have p11641_0 := h11641c.1
                                        have p11641_1 := h11641c.2.1
                                        have p11641_2 := h11641c.2.2.1
                                        have p11641_3 := h11641c.2.2.2
                                        linarith only [hlam, p11641_0]
                                      · have p11641_0 := h11641c.1
                                        have p11641_1 := h11641c.2.1
                                        have p11641_2 := h11641c.2.2.1
                                        have p11641_3 := h11641c.2.2.2
                                        linarith only [h0, hlam, p11641_0]
                                      · have p11641_0 := h11641c.1
                                        have p11641_1 := h11641c.2.1
                                        have p11641_2 := h11641c.2.2.1
                                        have p11641_3 := h11641c.2.2.2
                                        linarith only [h10472, hlam, p11641_0]
                                      · have p11641_0 := h11641c.1
                                        have p11641_1 := h11641c.2.1
                                        have p11641_2 := h11641c.2.2.1
                                        have p11641_3 := h11641c.2.2.2
                                        linarith only [h11380, h11577, h11581, h11583, hc34, hc45, hlam, hphi, p11641_1]
                                      · have p11641_0 := h11641c.1
                                        have p11641_1 := h11641c.2.1
                                        have p11641_2 := h11641c.2.2.1
                                        have p11641_3 := h11641c.2.2.2
                                        linarith only [h11380, hlam, p11641_0]
                                      · have p11641_0 := h11641c.1
                                        have p11641_1 := h11641c.2.1
                                        have p11641_2 := h11641c.2.2.1
                                        have p11641_3 := h11641c.2.2.2
                                        rcases p11641_3 (m.d 0 1) (by simp) with h11647 | h11647
                                        · linarith only [h11647, hlam, p11641_0]
                                        · rcases p11641_3 (m.d 1 2) (by simp) with h11649 | h11649
                                          · rcases p11641_3 (m.d 1 3) (by simp) with h11650 | h11650
                                            · linarith only [h11576, h11650, hlam]
                                            · linarith only [h10472, h11650, hlam]
                                          · linarith only [h11649, hlam, p11641_0]
                                      · have p11641_0 := h11641c.1
                                        have p11641_1 := h11641c.2.1
                                        have p11641_2 := h11641c.2.2.1
                                        have p11641_3 := h11641c.2.2.2
                                        linarith only [hlam, p11641_0]
                                      · have p11641_0 := h11641c.1
                                        have p11641_1 := h11641c.2.1
                                        have p11641_2 := h11641c.2.2.1
                                        have p11641_3 := h11641c.2.2.2
                                        linarith only [h10472, h11573, h11584, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p11641_1]
                                      · have p11641_0 := h11641c.1
                                        have p11641_1 := h11641c.2.1
                                        have p11641_2 := h11641c.2.2.1
                                        have p11641_3 := h11641c.2.2.2
                                        rcases p11641_3 (m.d 0 1) (by simp) with h11656 | h11656
                                        · linarith only [h0, h11656, hlam]
                                        · linarith only [h11379, h11656, hlam]
                                      · have p11641_0 := h11641c.1
                                        have p11641_1 := h11641c.2.1
                                        have p11641_2 := h11641c.2.2.1
                                        have p11641_3 := h11641c.2.2.2
                                        linarith only [h11380, hc01, hc12, hlam, hphi, p11641_1]
                                      · have p11641_0 := h11641c.1
                                        have p11641_1 := h11641c.2.1
                                        have p11641_2 := h11641c.2.2.1
                                        have p11641_3 := h11641c.2.2.2
                                        rcases p11641_3 (m.d 0 1) (by simp) with h11660 | h11660
                                        · linarith only [h11660, hlam, p11641_0]
                                        · rcases p11641_3 (m.d 1 2) (by simp) with h11662 | h11662
                                          · rcases p11641_3 (m.d 1 3) (by simp) with h11663 | h11663
                                            · rcases p11641_3 (m.d 1 4) (by simp) with h11664 | h11664
                                              · linarith only [h11579, h11664, hlam]
                                              · rcases p11641_3 (m.d 1 5) (by simp) with h11666 | h11666
                                                · linarith only [h11580, h11666, hlam]
                                                · linarith only [h11380, h11666, hlam]
                                            · linarith only [h11663, hlam, p11641_0]
                                          · linarith only [h0, h11662, hlam]
                                      · have p11641_0 := h11641c.1
                                        have p11641_1 := h11641c.2.1
                                        have p11641_2 := h11641c.2.2.1
                                        have p11641_3 := h11641c.2.2.2
                                        linarith only [h11576, hlam, p11641_1]
                                      · have p11641_0 := h11641c.1
                                        have p11641_1 := h11641c.2.1
                                        have p11641_2 := h11641c.2.2.1
                                        have p11641_3 := h11641c.2.2.2
                                        linarith only [hlam, p11641_0]
                                      · have p11641_0 := h11641c.1
                                        have p11641_1 := h11641c.2.1
                                        have p11641_2 := h11641c.2.2.1
                                        have p11641_3 := h11641c.2.2.2
                                        rcases p11641_3 (m.d 0 1) (by simp) with h11673 | h11673
                                        · linarith only [h10472, h11673, hlam]
                                        · linarith only [h11379, h11673, hlam]
                                      · have p11641_0 := h11641c.1
                                        have p11641_1 := h11641c.2.1
                                        have p11641_2 := h11641c.2.2.1
                                        have p11641_3 := h11641c.2.2.2
                                        linarith only [h11380, h11573, h11583, h11584, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11641_1]
                                      · have p11641_0 := h11641c.1
                                        have p11641_1 := h11641c.2.1
                                        have p11641_2 := h11641c.2.2.1
                                        have p11641_3 := h11641c.2.2.2
                                        linarith only [h11379, hlam, p11641_0]
                                      · have p11641_0 := h11641c.1
                                        have p11641_1 := h11641c.2.1
                                        have p11641_2 := h11641c.2.2.1
                                        have p11641_3 := h11641c.2.2.2
                                        linarith only [h11577, hlam, p11641_1]
                                      · have p11641_0 := h11641c.1
                                        have p11641_1 := h11641c.2.1
                                        have p11641_2 := h11641c.2.2.1
                                        have p11641_3 := h11641c.2.2.2
                                        linarith only [h11579, hlam, p11641_0]
                                      · have p11641_0 := h11641c.1
                                        have p11641_1 := h11641c.2.1
                                        have p11641_2 := h11641c.2.2.1
                                        have p11641_3 := h11641c.2.2.2
                                        linarith only [hlam, p11641_0]
                                      · have p11641_0 := h11641c.1
                                        have p11641_1 := h11641c.2.1
                                        have p11641_2 := h11641c.2.2.1
                                        have p11641_3 := h11641c.2.2.2
                                        linarith only [h11581, hlam, p11641_1]
                                      · have p11641_0 := h11641c.1
                                        have p11641_1 := h11641c.2.1
                                        have p11641_2 := h11641c.2.2.1
                                        have p11641_3 := h11641c.2.2.2
                                        linarith only [h11379, h11577, h11581, h11583, hc34, hc45, hlam, hphi, p11641_1]
                                      · have p11641_0 := h11641c.1
                                        have p11641_1 := h11641c.2.1
                                        have p11641_2 := h11641c.2.2.1
                                        have p11641_3 := h11641c.2.2.2
                                        linarith only [h11578, hlam, p11641_1]
                                      · have p11641_0 := h11641c.1
                                        have p11641_1 := h11641c.2.1
                                        have p11641_2 := h11641c.2.2.1
                                        have p11641_3 := h11641c.2.2.2
                                        linarith only [h11580, hlam, p11641_0]
                                      · have p11641_0 := h11641c.1
                                        have p11641_1 := h11641c.2.1
                                        have p11641_2 := h11641c.2.2.1
                                        have p11641_3 := h11641c.2.2.2
                                        rcases p11641_3 (m.d 0 1) (by simp) with h11685 | h11685
                                        · linarith only [h11380, h11685, hlam]
                                        · linarith only [h11379, h11685, hlam]
                                      · have p11641_0 := h11641c.1
                                        have p11641_1 := h11641c.2.1
                                        have p11641_2 := h11641c.2.2.1
                                        have p11641_3 := h11641c.2.2.2
                                        linarith only [hlam, p11641_0]
                              · linarith only [h11379, h11380, h11579, h11581, h11583, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h10472, h11379, h11573, h11580, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h10472, h11572, h11579, hlam]
                      · linarith only [h0, h11571, h11578, hlam]
                    · linarith only [h0, h11570, h11577, hlam]
                  · linarith only [h0, h11569, h11576, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h11695 | h11695
                · linarith only [h10472, h11379, h11573, h11695, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h11697 | h11697
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h11698 | h11698
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h11699 | h11699
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11700 | h11700
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h11701 | h11701
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h11702 | h11702
                            · linarith only [h10472, h11379, h11573, h11695, h11697, h11701, h11702, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h11704 | h11704
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h11705 | h11705
                                · linarith only [h10472, h11379, h11569, h11573, h11705, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h11707 | h11707
                                  · linarith only [h10472, h11379, h11573, h11698, h11701, h11702, h11707, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h11709 | h11709
                                    · linarith only [h10472, h11379, h11573, h11698, h11701, h11702, h11704, h11709, hlam]
                                    · rcases h1bigk with h11711c | h11711c | h11711c | h11711c | h11711c | h11711c | h11711c | h11711c | h11711c | h11711c | h11711c | h11711c | h11711c | h11711c | h11711c | h11711c | h11711c | h11711c | h11711c | h11711c | h11711c | h11711c | h11711c | h11711c | h11711c
                                      · have p11711_0 := h11711c.1
                                        have p11711_1 := h11711c.2.1
                                        have p11711_2 := h11711c.2.2.1
                                        have p11711_3 := h11711c.2.2.2
                                        linarith only [hlam, p11711_0]
                                      · have p11711_0 := h11711c.1
                                        have p11711_1 := h11711c.2.1
                                        have p11711_2 := h11711c.2.2.1
                                        have p11711_3 := h11711c.2.2.2
                                        linarith only [h0, hlam, p11711_0]
                                      · have p11711_0 := h11711c.1
                                        have p11711_1 := h11711c.2.1
                                        have p11711_2 := h11711c.2.2.1
                                        have p11711_3 := h11711c.2.2.2
                                        linarith only [h10472, hlam, p11711_0]
                                      · have p11711_0 := h11711c.1
                                        have p11711_1 := h11711c.2.1
                                        have p11711_2 := h11711c.2.2.1
                                        have p11711_3 := h11711c.2.2.2
                                        linarith only [h10472, h11573, h11697, h11698, h11701, h11704, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11711_1]
                                      · have p11711_0 := h11711c.1
                                        have p11711_1 := h11711c.2.1
                                        have p11711_2 := h11711c.2.2.1
                                        have p11711_3 := h11711c.2.2.2
                                        linarith only [h11380, hlam, p11711_0]
                                      · have p11711_0 := h11711c.1
                                        have p11711_1 := h11711c.2.1
                                        have p11711_2 := h11711c.2.2.1
                                        have p11711_3 := h11711c.2.2.2
                                        rcases p11711_3 (m.d 0 1) (by simp) with h11717 | h11717
                                        · linarith only [h11717, hlam, p11711_0]
                                        · rcases p11711_3 (m.d 1 2) (by simp) with h11719 | h11719
                                          · rcases p11711_3 (m.d 1 3) (by simp) with h11720 | h11720
                                            · linarith only [h11697, h11720, hlam]
                                            · linarith only [h10472, h11720, hlam]
                                          · linarith only [h11719, hlam, p11711_0]
                                      · have p11711_0 := h11711c.1
                                        have p11711_1 := h11711c.2.1
                                        have p11711_2 := h11711c.2.2.1
                                        have p11711_3 := h11711c.2.2.2
                                        linarith only [hlam, p11711_0]
                                      · have p11711_0 := h11711c.1
                                        have p11711_1 := h11711c.2.1
                                        have p11711_2 := h11711c.2.2.1
                                        have p11711_3 := h11711c.2.2.2
                                        linarith only [h10472, h11573, h11701, hc01, hc12, hlam, hphi, p11711_1]
                                      · have p11711_0 := h11711c.1
                                        have p11711_1 := h11711c.2.1
                                        have p11711_2 := h11711c.2.2.1
                                        have p11711_3 := h11711c.2.2.2
                                        linarith only [h10472, h11379, h11573, h11697, h11701, hlam, p11711_2]
                                      · have p11711_0 := h11711c.1
                                        have p11711_1 := h11711c.2.1
                                        have p11711_2 := h11711c.2.2.1
                                        have p11711_3 := h11711c.2.2.2
                                        linarith only [h10472, h11379, h11573, h11698, h11701, h11704, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11711_1]
                                      · have p11711_0 := h11711c.1
                                        have p11711_1 := h11711c.2.1
                                        have p11711_2 := h11711c.2.2.1
                                        have p11711_3 := h11711c.2.2.2
                                        rcases p11711_3 (m.d 0 1) (by simp) with h11728 | h11728
                                        · linarith only [h11728, hlam, p11711_0]
                                        · rcases p11711_3 (m.d 1 2) (by simp) with h11730 | h11730
                                          · rcases p11711_3 (m.d 1 3) (by simp) with h11731 | h11731
                                            · rcases p11711_3 (m.d 1 4) (by simp) with h11732 | h11732
                                              · linarith only [h11700, h11732, hlam]
                                              · rcases p11711_3 (m.d 1 5) (by simp) with h11734 | h11734
                                                · linarith only [h11701, h11734, hlam]
                                                · linarith only [h11380, h11734, hlam]
                                            · linarith only [h11731, hlam, p11711_0]
                                          · linarith only [h0, h11730, hlam]
                                      · have p11711_0 := h11711c.1
                                        have p11711_1 := h11711c.2.1
                                        have p11711_2 := h11711c.2.2.1
                                        have p11711_3 := h11711c.2.2.2
                                        linarith only [h11697, hlam, p11711_1]
                                      · have p11711_0 := h11711c.1
                                        have p11711_1 := h11711c.2.1
                                        have p11711_2 := h11711c.2.2.1
                                        have p11711_3 := h11711c.2.2.2
                                        linarith only [hlam, p11711_0]
                                      · have p11711_0 := h11711c.1
                                        have p11711_1 := h11711c.2.1
                                        have p11711_2 := h11711c.2.2.1
                                        have p11711_3 := h11711c.2.2.2
                                        linarith only [h10472, h11379, h11573, h11701, hlam, p11711_2]
                                      · have p11711_0 := h11711c.1
                                        have p11711_1 := h11711c.2.1
                                        have p11711_2 := h11711c.2.2.1
                                        have p11711_3 := h11711c.2.2.2
                                        linarith only [h10472, h11379, h11573, h11698, h11701, h11704, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11711_1]
                                      · have p11711_0 := h11711c.1
                                        have p11711_1 := h11711c.2.1
                                        have p11711_2 := h11711c.2.2.1
                                        have p11711_3 := h11711c.2.2.2
                                        linarith only [h11379, hlam, p11711_0]
                                      · have p11711_0 := h11711c.1
                                        have p11711_1 := h11711c.2.1
                                        have p11711_2 := h11711c.2.2.1
                                        have p11711_3 := h11711c.2.2.2
                                        linarith only [h11698, hlam, p11711_1]
                                      · have p11711_0 := h11711c.1
                                        have p11711_1 := h11711c.2.1
                                        have p11711_2 := h11711c.2.2.1
                                        have p11711_3 := h11711c.2.2.2
                                        linarith only [h11700, hlam, p11711_0]
                                      · have p11711_0 := h11711c.1
                                        have p11711_1 := h11711c.2.1
                                        have p11711_2 := h11711c.2.2.1
                                        have p11711_3 := h11711c.2.2.2
                                        linarith only [hlam, p11711_0]
                                      · have p11711_0 := h11711c.1
                                        have p11711_1 := h11711c.2.1
                                        have p11711_2 := h11711c.2.2.1
                                        have p11711_3 := h11711c.2.2.2
                                        linarith only [h11702, hlam, p11711_1]
                                      · have p11711_0 := h11711c.1
                                        have p11711_1 := h11711c.2.1
                                        have p11711_2 := h11711c.2.2.1
                                        have p11711_3 := h11711c.2.2.2
                                        linarith only [h11379, h11698, h11702, h11704, hc34, hc45, hlam, hphi, p11711_1]
                                      · have p11711_0 := h11711c.1
                                        have p11711_1 := h11711c.2.1
                                        have p11711_2 := h11711c.2.2.1
                                        have p11711_3 := h11711c.2.2.2
                                        linarith only [h11699, hlam, p11711_1]
                                      · have p11711_0 := h11711c.1
                                        have p11711_1 := h11711c.2.1
                                        have p11711_2 := h11711c.2.2.1
                                        have p11711_3 := h11711c.2.2.2
                                        linarith only [h11701, hlam, p11711_0]
                                      · have p11711_0 := h11711c.1
                                        have p11711_1 := h11711c.2.1
                                        have p11711_2 := h11711c.2.2.1
                                        have p11711_3 := h11711c.2.2.2
                                        rcases p11711_3 (m.d 0 1) (by simp) with h11751 | h11751
                                        · linarith only [h11380, h11751, hlam]
                                        · linarith only [h11379, h11751, hlam]
                                      · have p11711_0 := h11711c.1
                                        have p11711_1 := h11711c.2.1
                                        have p11711_2 := h11711c.2.2.1
                                        have p11711_3 := h11711c.2.2.2
                                        linarith only [hlam, p11711_0]
                              · linarith only [h11572, h11573, h11704, hc23, hc35, hlam, hphi]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h11756 | h11756
                            · linarith only [h10472, h11379, h11701, h11756, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h11758 | h11758
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h11759 | h11759
                                · linarith only [h10472, h11379, h11698, h11701, h11758, h11759, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h11761 | h11761
                                  · linarith only [h10472, h11379, h11698, h11701, h11756, h11761, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h11763 | h11763
                                    · linarith only [h10472, h11701, h11756, h11758, h11763, hc01, hc23, hlam, hphi, ht12]
                                    · linarith only [h10472, h11379, h11698, h11701, h11758, h11763, hc34, hc45, hlam, hphi]
                              · linarith only [h10472, h11572, h11701, h11758, hc23, hc35, hlam, hphi]
                        · linarith only [h10472, h11379, h11572, h11700, hlam]
                      · linarith only [h0, h11571, h11699, hlam]
                    · linarith only [h0, h11570, h11698, hlam]
                  · linarith only [h0, h11569, h11697, hlam]
            · linarith only [h10472, h11379, h11572, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h11772 | h11772
            · rcases m.htr 0 3 5 (by decide) (by decide) with h11773 | h11773
              · linarith only [h11569, h11571, h11773, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h11775 | h11775
                · linarith only [h0, h11379, h11571, h11775, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h11777 | h11777
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h11778 | h11778
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h11779 | h11779
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11780 | h11780
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h11781 | h11781
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h11782 | h11782
                            · linarith only [h10472, h11379, h11569, h11571, h11775, h11779, h11782, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h11784 | h11784
                              · linarith only [h11569, h11571, h11779, h11784, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h11569, h11571, h11772, h11779, h11784, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h11787 | h11787
                            · linarith only [h10472, h11379, h11569, h11571, h11779, h11787, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h11789 | h11789
                              · linarith only [h11569, h11571, h11779, h11789, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h11569, h11571, h11772, h11779, h11789, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h10472, h11379, h11772, h11780, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11793 | h11793
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h11794 | h11794
                          · linarith only [h10472, h11773, h11777, h11779, h11794, hc01, hc25, hlam, hphi, ht12]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h11796 | h11796
                            · linarith only [h10472, h11379, h11796, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h11798 | h11798
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h11799 | h11799
                                · linarith only [h0, h11569, h11779, h11799, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h11801 | h11801
                                  · linarith only [h10472, h11379, h11380, h11777, h11778, h11779, h11796, h11799, h11801, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                                  · linarith only [h10472, h11379, h11777, h11779, h11801, hc14, hc45, hlam, hphi]
                              · linarith only [h10472, h11772, h11794, h11798, hc23, hc35, hlam, hphi]
                        · linarith only [h10472, h11379, h11772, h11793, hlam]
                    · linarith only [h0, h11570, h11778, hlam]
                  · linarith only [h0, h11569, h11777, hlam]
            · linarith only [h10472, h11379, h11772, hlam]
        · linarith only [h0, h11379, h11570, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h11810 | h11810
        · rcases m.htr 0 2 5 (by decide) (by decide) with h11811 | h11811
          · rcases m.htr 0 3 4 (by decide) (by decide) with h11812 | h11812
            · rcases m.htr 0 3 5 (by decide) (by decide) with h11813 | h11813
              · rcases m.htr 0 4 5 (by decide) (by decide) with h11814 | h11814
                · linarith only [h11379, h11380, h11814, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h11816 | h11816
                  · linarith only [h11569, h11811, h11816, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h11818 | h11818
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h11819 | h11819
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11820 | h11820
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h11821 | h11821
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h11822 | h11822
                            · linarith only [h11379, h11380, h11814, h11819, h11822, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h11824 | h11824
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h11825 | h11825
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h11826 | h11826
                                  · linarith only [h11379, h11380, h11818, h11822, h11826, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h11828 | h11828
                                    · linarith only [h11379, h11380, h11818, h11822, h11824, h11828, hlam]
                                    · rcases h1bigk with h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c | h11830c
                                      · have p11830_0 := h11830c.1
                                        have p11830_1 := h11830c.2.1
                                        have p11830_2 := h11830c.2.2.1
                                        have p11830_3 := h11830c.2.2.2
                                        linarith only [hlam, p11830_0]
                                      · have p11830_0 := h11830c.1
                                        have p11830_1 := h11830c.2.1
                                        have p11830_2 := h11830c.2.2.1
                                        have p11830_3 := h11830c.2.2.2
                                        linarith only [h0, hlam, p11830_0]
                                      · have p11830_0 := h11830c.1
                                        have p11830_1 := h11830c.2.1
                                        have p11830_2 := h11830c.2.2.1
                                        have p11830_3 := h11830c.2.2.2
                                        linarith only [h10472, hlam, p11830_0]
                                      · have p11830_0 := h11830c.1
                                        have p11830_1 := h11830c.2.1
                                        have p11830_2 := h11830c.2.2.1
                                        have p11830_3 := h11830c.2.2.2
                                        linarith only [h11380, h11816, h11819, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11830_1]
                                      · have p11830_0 := h11830c.1
                                        have p11830_1 := h11830c.2.1
                                        have p11830_2 := h11830c.2.2.1
                                        have p11830_3 := h11830c.2.2.2
                                        linarith only [h11380, hlam, p11830_0]
                                      · have p11830_0 := h11830c.1
                                        have p11830_1 := h11830c.2.1
                                        have p11830_2 := h11830c.2.2.1
                                        have p11830_3 := h11830c.2.2.2
                                        linarith only [h11816, hc01, hc23, hlam, hphi, ht12, p11830_1]
                                      · have p11830_0 := h11830c.1
                                        have p11830_1 := h11830c.2.1
                                        have p11830_2 := h11830c.2.2.1
                                        have p11830_3 := h11830c.2.2.2
                                        linarith only [hlam, p11830_0]
                                      · have p11830_0 := h11830c.1
                                        have p11830_1 := h11830c.2.1
                                        have p11830_2 := h11830c.2.2.1
                                        have p11830_3 := h11830c.2.2.2
                                        linarith only [h11816, hlam, p11830_0]
                                      · have p11830_0 := h11830c.1
                                        have p11830_1 := h11830c.2.1
                                        have p11830_2 := h11830c.2.2.1
                                        have p11830_3 := h11830c.2.2.2
                                        rcases p11830_3 (m.d 0 1) (by simp) with h11839 | h11839
                                        · linarith only [h0, h11839, hlam]
                                        · linarith only [h11379, h11839, hlam]
                                      · have p11830_0 := h11830c.1
                                        have p11830_1 := h11830c.2.1
                                        have p11830_2 := h11830c.2.2.1
                                        have p11830_3 := h11830c.2.2.2
                                        linarith only [h11816, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p11830_1, u5ehi1]
                                      · have p11830_0 := h11830c.1
                                        have p11830_1 := h11830c.2.1
                                        have p11830_2 := h11830c.2.2.1
                                        have p11830_3 := h11830c.2.2.2
                                        rcases p11830_3 (m.d 0 1) (by simp) with h11843 | h11843
                                        · linarith only [h11843, hlam, p11830_0]
                                        · rcases p11830_3 (m.d 1 2) (by simp) with h11845 | h11845
                                          · linarith only [h11816, h11845, hlam]
                                          · linarith only [h0, h11845, hlam]
                                      · have p11830_0 := h11830c.1
                                        have p11830_1 := h11830c.2.1
                                        have p11830_2 := h11830c.2.2.1
                                        have p11830_3 := h11830c.2.2.2
                                        linarith only [h0, h11379, h11816, h11818, h11824, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11830_1]
                                      · have p11830_0 := h11830c.1
                                        have p11830_1 := h11830c.2.1
                                        have p11830_2 := h11830c.2.2.1
                                        have p11830_3 := h11830c.2.2.2
                                        linarith only [hlam, p11830_0]
                                      · have p11830_0 := h11830c.1
                                        have p11830_1 := h11830c.2.1
                                        have p11830_2 := h11830c.2.2.1
                                        have p11830_3 := h11830c.2.2.2
                                        rcases p11830_3 (m.d 0 1) (by simp) with h11850 | h11850
                                        · linarith only [h10472, h11850, hlam]
                                        · linarith only [h11379, h11850, hlam]
                                      · have p11830_0 := h11830c.1
                                        have p11830_1 := h11830c.2.1
                                        have p11830_2 := h11830c.2.2.1
                                        have p11830_3 := h11830c.2.2.2
                                        linarith only [h11379, h11380, h11818, h11824, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11830_1]
                                      · have p11830_0 := h11830c.1
                                        have p11830_1 := h11830c.2.1
                                        have p11830_2 := h11830c.2.2.1
                                        have p11830_3 := h11830c.2.2.2
                                        linarith only [h11379, hlam, p11830_0]
                                      · have p11830_0 := h11830c.1
                                        have p11830_1 := h11830c.2.1
                                        have p11830_2 := h11830c.2.2.1
                                        have p11830_3 := h11830c.2.2.2
                                        linarith only [h11818, hlam, p11830_1]
                                      · have p11830_0 := h11830c.1
                                        have p11830_1 := h11830c.2.1
                                        have p11830_2 := h11830c.2.2.1
                                        have p11830_3 := h11830c.2.2.2
                                        linarith only [h11820, hlam, p11830_0]
                                      · have p11830_0 := h11830c.1
                                        have p11830_1 := h11830c.2.1
                                        have p11830_2 := h11830c.2.2.1
                                        have p11830_3 := h11830c.2.2.2
                                        linarith only [hlam, p11830_0]
                                      · have p11830_0 := h11830c.1
                                        have p11830_1 := h11830c.2.1
                                        have p11830_2 := h11830c.2.2.1
                                        have p11830_3 := h11830c.2.2.2
                                        linarith only [h11822, hlam, p11830_1]
                                      · have p11830_0 := h11830c.1
                                        have p11830_1 := h11830c.2.1
                                        have p11830_2 := h11830c.2.2.1
                                        have p11830_3 := h11830c.2.2.2
                                        linarith only [h11379, h11818, h11822, h11824, hc34, hc45, hlam, hphi, p11830_1]
                                      · have p11830_0 := h11830c.1
                                        have p11830_1 := h11830c.2.1
                                        have p11830_2 := h11830c.2.2.1
                                        have p11830_3 := h11830c.2.2.2
                                        linarith only [h11819, hlam, p11830_1]
                                      · have p11830_0 := h11830c.1
                                        have p11830_1 := h11830c.2.1
                                        have p11830_2 := h11830c.2.2.1
                                        have p11830_3 := h11830c.2.2.2
                                        linarith only [h11821, hlam, p11830_0]
                                      · have p11830_0 := h11830c.1
                                        have p11830_1 := h11830c.2.1
                                        have p11830_2 := h11830c.2.2.1
                                        have p11830_3 := h11830c.2.2.2
                                        rcases p11830_3 (m.d 0 1) (by simp) with h11862 | h11862
                                        · linarith only [h11380, h11862, hlam]
                                        · linarith only [h11379, h11862, hlam]
                                      · have p11830_0 := h11830c.1
                                        have p11830_1 := h11830c.2.1
                                        have p11830_2 := h11830c.2.2.1
                                        have p11830_3 := h11830c.2.2.2
                                        linarith only [hlam, p11830_0]
                                · linarith only [h0, h11379, h11816, h11818, h11824, h11825, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h11379, h11380, h11816, h11818, h11819, h11824, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h10472, h11379, h11813, h11818, h11821, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h10472, h11812, h11820, hlam]
                      · linarith only [h0, h11811, h11819, hlam]
                    · linarith only [h0, h11810, h11818, hlam]
              · linarith only [h11569, h11811, h11813, hlam]
            · linarith only [h0, h11379, h11569, h11812, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h11874 | h11874
            · rcases m.htr 0 3 5 (by decide) (by decide) with h11875 | h11875
              · rcases m.htr 0 4 5 (by decide) (by decide) with h11876 | h11876
                · linarith only [h0, h11379, h11811, h11876, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h11878 | h11878
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h11879 | h11879
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h11880 | h11880
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11881 | h11881
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h11882 | h11882
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h11883 | h11883
                            · linarith only [h0, h11379, h11569, h11876, h11878, h11883, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h11885 | h11885
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h11886 | h11886
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h11887 | h11887
                                  · linarith only [h0, h11379, h11811, h11878, h11879, h11883, h11886, h11887, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h11889 | h11889
                                    · linarith only [h0, h11379, h11811, h11879, h11880, h11883, h11885, h11889, hlam]
                                    · rcases h1bigk with h11891c | h11891c | h11891c | h11891c | h11891c | h11891c | h11891c | h11891c | h11891c | h11891c | h11891c | h11891c | h11891c | h11891c | h11891c | h11891c | h11891c | h11891c | h11891c | h11891c | h11891c | h11891c | h11891c | h11891c | h11891c
                                      · have p11891_0 := h11891c.1
                                        have p11891_1 := h11891c.2.1
                                        have p11891_2 := h11891c.2.2.1
                                        have p11891_3 := h11891c.2.2.2
                                        linarith only [hlam, p11891_0]
                                      · have p11891_0 := h11891c.1
                                        have p11891_1 := h11891c.2.1
                                        have p11891_2 := h11891c.2.2.1
                                        have p11891_3 := h11891c.2.2.2
                                        linarith only [h0, hlam, p11891_0]
                                      · have p11891_0 := h11891c.1
                                        have p11891_1 := h11891c.2.1
                                        have p11891_2 := h11891c.2.2.1
                                        have p11891_3 := h11891c.2.2.2
                                        linarith only [h10472, hlam, p11891_0]
                                      · have p11891_0 := h11891c.1
                                        have p11891_1 := h11891c.2.1
                                        have p11891_2 := h11891c.2.2.1
                                        have p11891_3 := h11891c.2.2.2
                                        linarith only [h0, h11811, h11878, h11879, h11885, h11886, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11891_1]
                                      · have p11891_0 := h11891c.1
                                        have p11891_1 := h11891c.2.1
                                        have p11891_2 := h11891c.2.2.1
                                        have p11891_3 := h11891c.2.2.2
                                        linarith only [h11380, hlam, p11891_0]
                                      · have p11891_0 := h11891c.1
                                        have p11891_1 := h11891c.2.1
                                        have p11891_2 := h11891c.2.2.1
                                        have p11891_3 := h11891c.2.2.2
                                        rcases p11891_3 (m.d 0 1) (by simp) with h11897 | h11897
                                        · linarith only [h11897, hlam, p11891_0]
                                        · rcases p11891_3 (m.d 1 2) (by simp) with h11899 | h11899
                                          · rcases p11891_3 (m.d 1 3) (by simp) with h11900 | h11900
                                            · linarith only [h11878, h11900, hlam]
                                            · linarith only [h10472, h11900, hlam]
                                          · linarith only [h11899, hlam, p11891_0]
                                      · have p11891_0 := h11891c.1
                                        have p11891_1 := h11891c.2.1
                                        have p11891_2 := h11891c.2.2.1
                                        have p11891_3 := h11891c.2.2.2
                                        linarith only [hlam, p11891_0]
                                      · have p11891_0 := h11891c.1
                                        have p11891_1 := h11891c.2.1
                                        have p11891_2 := h11891c.2.2.1
                                        have p11891_3 := h11891c.2.2.2
                                        linarith only [h10472, hc01, hc12, hlam, hphi, p11891_1]
                                      · have p11891_0 := h11891c.1
                                        have p11891_1 := h11891c.2.1
                                        have p11891_2 := h11891c.2.2.1
                                        have p11891_3 := h11891c.2.2.2
                                        linarith only [h0, h11379, h11811, h11878, h11886, hlam, p11891_2]
                                      · have p11891_0 := h11891c.1
                                        have p11891_1 := h11891c.2.1
                                        have p11891_2 := h11891c.2.2.1
                                        have p11891_3 := h11891c.2.2.2
                                        linarith only [h0, h11811, h11880, hc01, hc12, hlam, hphi, p11891_1]
                                      · have p11891_0 := h11891c.1
                                        have p11891_1 := h11891c.2.1
                                        have p11891_2 := h11891c.2.2.1
                                        have p11891_3 := h11891c.2.2.2
                                        rcases p11891_3 (m.d 0 1) (by simp) with h11908 | h11908
                                        · linarith only [h11908, hlam, p11891_0]
                                        · rcases p11891_3 (m.d 1 2) (by simp) with h11910 | h11910
                                          · rcases p11891_3 (m.d 1 3) (by simp) with h11911 | h11911
                                            · rcases p11891_3 (m.d 1 4) (by simp) with h11912 | h11912
                                              · linarith only [h11881, h11912, hlam]
                                              · rcases p11891_3 (m.d 1 5) (by simp) with h11914 | h11914
                                                · linarith only [h11882, h11914, hlam]
                                                · linarith only [h11380, h11914, hlam]
                                            · linarith only [h11911, hlam, p11891_0]
                                          · linarith only [h0, h11910, hlam]
                                      · have p11891_0 := h11891c.1
                                        have p11891_1 := h11891c.2.1
                                        have p11891_2 := h11891c.2.2.1
                                        have p11891_3 := h11891c.2.2.2
                                        linarith only [h11878, hlam, p11891_1]
                                      · have p11891_0 := h11891c.1
                                        have p11891_1 := h11891c.2.1
                                        have p11891_2 := h11891c.2.2.1
                                        have p11891_3 := h11891c.2.2.2
                                        linarith only [hlam, p11891_0]
                                      · have p11891_0 := h11891c.1
                                        have p11891_1 := h11891c.2.1
                                        have p11891_2 := h11891c.2.2.1
                                        have p11891_3 := h11891c.2.2.2
                                        rcases p11891_3 (m.d 0 1) (by simp) with h11921 | h11921
                                        · linarith only [h10472, h11921, hlam]
                                        · linarith only [h11379, h11921, hlam]
                                      · have p11891_0 := h11891c.1
                                        have p11891_1 := h11891c.2.1
                                        have p11891_2 := h11891c.2.2.1
                                        have p11891_3 := h11891c.2.2.2
                                        linarith only [h0, h11379, h11811, h11879, h11880, h11885, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p11891_1]
                                      · have p11891_0 := h11891c.1
                                        have p11891_1 := h11891c.2.1
                                        have p11891_2 := h11891c.2.2.1
                                        have p11891_3 := h11891c.2.2.2
                                        linarith only [h11379, hlam, p11891_0]
                                      · have p11891_0 := h11891c.1
                                        have p11891_1 := h11891c.2.1
                                        have p11891_2 := h11891c.2.2.1
                                        have p11891_3 := h11891c.2.2.2
                                        linarith only [h11879, hlam, p11891_1]
                                      · have p11891_0 := h11891c.1
                                        have p11891_1 := h11891c.2.1
                                        have p11891_2 := h11891c.2.2.1
                                        have p11891_3 := h11891c.2.2.2
                                        linarith only [h11881, hlam, p11891_0]
                                      · have p11891_0 := h11891c.1
                                        have p11891_1 := h11891c.2.1
                                        have p11891_2 := h11891c.2.2.1
                                        have p11891_3 := h11891c.2.2.2
                                        linarith only [hlam, p11891_0]
                                      · have p11891_0 := h11891c.1
                                        have p11891_1 := h11891c.2.1
                                        have p11891_2 := h11891c.2.2.1
                                        have p11891_3 := h11891c.2.2.2
                                        linarith only [h11883, hlam, p11891_1]
                                      · have p11891_0 := h11891c.1
                                        have p11891_1 := h11891c.2.1
                                        have p11891_2 := h11891c.2.2.1
                                        have p11891_3 := h11891c.2.2.2
                                        linarith only [h11379, h11879, h11883, h11885, hc34, hc45, hlam, hphi, p11891_1]
                                      · have p11891_0 := h11891c.1
                                        have p11891_1 := h11891c.2.1
                                        have p11891_2 := h11891c.2.2.1
                                        have p11891_3 := h11891c.2.2.2
                                        linarith only [h11880, hlam, p11891_1]
                                      · have p11891_0 := h11891c.1
                                        have p11891_1 := h11891c.2.1
                                        have p11891_2 := h11891c.2.2.1
                                        have p11891_3 := h11891c.2.2.2
                                        linarith only [h11882, hlam, p11891_0]
                                      · have p11891_0 := h11891c.1
                                        have p11891_1 := h11891c.2.1
                                        have p11891_2 := h11891c.2.2.1
                                        have p11891_3 := h11891c.2.2.2
                                        rcases p11891_3 (m.d 0 1) (by simp) with h11933 | h11933
                                        · linarith only [h11380, h11933, hlam]
                                        · linarith only [h11379, h11933, hlam]
                                      · have p11891_0 := h11891c.1
                                        have p11891_1 := h11891c.2.1
                                        have p11891_2 := h11891c.2.2.1
                                        have p11891_3 := h11891c.2.2.2
                                        linarith only [hlam, p11891_0]
                                · linarith only [h0, h11379, h11569, h11875, h11879, h11885, h11886, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b]
                              · linarith only [h0, h11379, h11569, h11874, h11879, h11885, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h10472, h11875, h11882, hlam]
                        · linarith only [h11569, h11874, h11878, h11881, hlam]
                      · linarith only [h0, h11379, h11569, h11878, h11879, h11880, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h11379, h11569, h11878, h11879, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h11943 | h11943
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h11944 | h11944
                      · linarith only [h0, h11379, h11811, h11878, h11943, h11944, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11946 | h11946
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h11947 | h11947
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h11948 | h11948
                            · linarith only [h0, h11379, h11876, h11878, h11948, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h11950 | h11950
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h11951 | h11951
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h11952 | h11952
                                  · linarith only [h0, h11379, h11943, h11944, h11948, h11951, h11952, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                                  · linarith only [h0, h11379, h11943, h11944, h11950, h11952, hc34, hc45, hlam, hphi]
                                · linarith only [h10472, h11875, h11878, h11951, hlam]
                              · linarith only [h0, h11878, h11950, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h10472, h11875, h11947, hlam]
                        · linarith only [h10472, h11874, h11946, hlam]
                    · linarith only [h0, h11379, h11810, h11943, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h11960 | h11960
                · linarith only [h11379, h11380, h11960, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h11962 | h11962
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h11963 | h11963
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h11964 | h11964
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11965 | h11965
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h11966 | h11966
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h11967 | h11967
                            · linarith only [h0, h11379, h11569, h11875, h11960, h11962, h11966, h11967, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h11969 | h11969
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h11970 | h11970
                                · linarith only [h0, h11569, h11875, h11962, h11970, hc01, hc12, hlam, hphi]
                                · linarith only [h0, h11379, h11569, h11963, h11966, h11969, h11970, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h0, h11379, h11569, h11874, h11963, h11969, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h11974 | h11974
                            · linarith only [h0, h11379, h11569, h11974, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h11976 | h11976
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h11977 | h11977
                                · linarith only [h11962, h11966, h11977, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h11979 | h11979
                                  · linarith only [h0, h11379, h11569, h11962, h11963, h11966, h11974, h11979, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h11981 | h11981
                                    · linarith only [h0, h11379, h11569, h11811, h11875, h11962, h11963, h11964, h11966, h11974, h11976, h11981, hc03, hc35, hlam, hphi]
                                    · linarith only [h0, h11379, h11569, h11962, h11963, h11966, h11976, h11981, hc34, hc45, hlam, hphi]
                              · linarith only [h0, h11379, h11569, h11874, h11963, h11976, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h0, h11379, h11569, h11874, h11875, h11962, h11965, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h0, h11379, h11569, h11962, h11963, h11964, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h11379, h11569, h11962, h11963, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h11988 | h11988
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h11989 | h11989
                      · linarith only [h0, h11379, h11811, h11962, h11988, h11989, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11991 | h11991
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h11992 | h11992
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h11993 | h11993
                            · linarith only [h0, h11379, h11962, h11993, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h11995 | h11995
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h11996 | h11996
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h11997 | h11997
                                  · linarith only [h0, h11379, h11569, h11875, h11962, h11988, h11992, h11993, h11997, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                                  · linarith only [h0, h11379, h11988, h11989, h11995, h11997, hc34, hc45, hlam, hphi]
                                · linarith only [h11962, h11992, h11996, hlam]
                              · linarith only [h0, h11379, h11569, h11875, h11962, h11988, h11992, h11995, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h12002 | h12002
                            · linarith only [h0, h11379, h11960, h11962, h11992, h12002, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h12004 | h12004
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h12005 | h12005
                                · linarith only [h0, h11379, h11962, h11988, h11992, h12004, h12005, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h0, h11379, h11962, h11988, h12004, h12005, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h0, h11379, h11962, h11988, h12004, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h11379, h11874, h11962, h11988, h11991, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h11810, h11988, hlam]
            · linarith only [h10472, h11379, h11874, hlam]
        · linarith only [h0, h11379, h11810, hlam]
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s14 m hb1 hb3 hb5 h0 h10472 h11379

end R2N4
