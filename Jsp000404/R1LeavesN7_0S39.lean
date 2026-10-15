import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x0_x0_x1_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg23339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg23340 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg23342 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg23344 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h23346 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h23347 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h23348 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h23945 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h23946 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h23947 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h23948 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h19744 := hg19744
  have h22010 := hg22010
  have h23337 := hg23337
  have h23338 := hg23338
  have h23339 := hg23339
  have h23340 := hg23340
  have h23342 := hg23342
  have h23344 := hg23344
  rcases h1bigk with h23950c | h23950c | h23950c | h23950c | h23950c | h23950c | h23950c | h23950c | h23950c | h23950c | h23950c | h23950c | h23950c | h23950c | h23950c | h23950c | h23950c | h23950c | h23950c | h23950c | h23950c | h23950c | h23950c | h23950c | h23950c
  · have p23950_0 := h23950c.1
    have p23950_1 := h23950c.2.1
    have p23950_2 := h23950c.2.2.1
    have p23950_3 := h23950c.2.2.2
    linarith only [hlam, p23950_0]
  · have p23950_0 := h23950c.1
    have p23950_1 := h23950c.2.1
    have p23950_2 := h23950c.2.2.1
    have p23950_3 := h23950c.2.2.2
    rcases p23950_3 (m.d 0 1) (by simp) with h23952 | h23952
    · rcases p23950_3 (m.d 1 2) (by simp) with h23953 | h23953
      · linarith only [h23953, hlam, p23950_0]
      · rcases p23950_3 (m.d 1 3) (by simp) with h23955 | h23955
        · linarith only [h1, h23955, hlam]
        · linarith only [h23340, h23955, hlam]
    · linarith only [h23952, hlam, p23950_0]
  · have p23950_0 := h23950c.1
    have p23950_1 := h23950c.2.1
    have p23950_2 := h23950c.2.2.1
    have p23950_3 := h23950c.2.2.2
    rcases p23950_3 (m.d 0 1) (by simp) with h23959 | h23959
    · rcases p23950_3 (m.d 1 2) (by simp) with h23960 | h23960
      · linarith only [h0, h23960, hlam]
      · rcases p23950_3 (m.d 1 3) (by simp) with h23962 | h23962
        · linarith only [h23962, hlam, p23950_0]
        · rcases p23950_3 (m.d 1 4) (by simp) with h23964 | h23964
          · linarith only [h2, h23964, hlam]
          · rcases p23950_3 (m.d 1 5) (by simp) with h23966 | h23966
            · linarith only [h23966, h3, hlam]
            · rcases h1emax with h23968 | h23968 | h23968 | h23968 | h23968
              · linarith only [h23968, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p23950_1]
              · rcases h2bigk with h23970c | h23970c | h23970c | h23970c | h23970c | h23970c | h23970c | h23970c | h23970c | h23970c | h23970c | h23970c | h23970c | h23970c | h23970c | h23970c | h23970c | h23970c | h23970c | h23970c | h23970c | h23970c | h23970c | h23970c | h23970c
                · have p23970_0 := h23970c.1
                  have p23970_1 := h23970c.2.1
                  have p23970_2 := h23970c.2.2.1
                  have p23970_3 := h23970c.2.2.2
                  linarith only [hlam, p23970_0]
                · have p23970_0 := h23970c.1
                  have p23970_1 := h23970c.2.1
                  have p23970_2 := h23970c.2.2.1
                  have p23970_3 := h23970c.2.2.2
                  linarith only [h4, hc12, hc23, hlam, hphi, p23970_1]
                · have p23970_0 := h23970c.1
                  have p23970_1 := h23970c.2.1
                  have p23970_2 := h23970c.2.2.1
                  have p23970_3 := h23970c.2.2.2
                  linarith only [h4, hlam, p23970_0]
                · have p23970_0 := h23970c.1
                  have p23970_1 := h23970c.2.1
                  have p23970_2 := h23970c.2.2.1
                  have p23970_3 := h23970c.2.2.2
                  linarith only [h19744, hlam, p23970_0]
                · have p23970_0 := h23970c.1
                  have p23970_1 := h23970c.2.1
                  have p23970_2 := h23970c.2.2.1
                  have p23970_3 := h23970c.2.2.2
                  linarith only [h22010, hlam, p23970_0]
                · have p23970_0 := h23970c.1
                  have p23970_1 := h23970c.2.1
                  have p23970_2 := h23970c.2.2.1
                  have p23970_3 := h23970c.2.2.2
                  linarith only [h0, hlam, p23970_1]
                · have p23970_0 := h23970c.1
                  have p23970_1 := h23970c.2.1
                  have p23970_2 := h23970c.2.2.1
                  have p23970_3 := h23970c.2.2.2
                  linarith only [hlam, p23970_0]
                · have p23970_0 := h23970c.1
                  have p23970_1 := h23970c.2.1
                  have p23970_2 := h23970c.2.2.1
                  have p23970_3 := h23970c.2.2.2
                  linarith only [h23340, hlam, p23970_0]
                · have p23970_0 := h23970c.1
                  have p23970_1 := h23970c.2.1
                  have p23970_2 := h23970c.2.2.1
                  have p23970_3 := h23970c.2.2.2
                  linarith only [h23342, hlam, p23970_0]
                · have p23970_0 := h23970c.1
                  have p23970_1 := h23970c.2.1
                  have p23970_2 := h23970c.2.2.1
                  have p23970_3 := h23970c.2.2.2
                  linarith only [h23344, hlam, p23970_0]
                · have p23970_0 := h23970c.1
                  have p23970_1 := h23970c.2.1
                  have p23970_2 := h23970c.2.2.1
                  have p23970_3 := h23970c.2.2.2
                  rcases p23970_3 (m.d 0 2) (by simp) with h23981 | h23981
                  · linarith only [h23981, hlam, p23970_0]
                  · rcases p23970_3 (m.d 1 2) (by simp) with h23983 | h23983
                    · linarith only [h23340, h23983, hlam]
                    · rcases p23970_3 (m.d 2 3) (by simp) with h23985 | h23985
                      · rcases p23970_3 (m.d 2 4) (by simp) with h23986 | h23986
                        · linarith only [h23945, h23986, hlam]
                        · linarith only [h19744, h23986, hlam]
                      · linarith only [h23985, hlam, p23970_0]
                · have p23970_0 := h23970c.1
                  have p23970_1 := h23970c.2.1
                  have p23970_2 := h23970c.2.2.1
                  have p23970_3 := h23970c.2.2.2
                  rcases p23970_3 (m.d 0 2) (by simp) with h23990 | h23990
                  · linarith only [h23990, h4, hlam]
                  · linarith only [h0, h23990, hlam]
                · have p23970_0 := h23970c.1
                  have p23970_1 := h23970c.2.1
                  have p23970_2 := h23970c.2.2.1
                  have p23970_3 := h23970c.2.2.2
                  linarith only [hlam, p23970_0]
                · have p23970_0 := h23970c.1
                  have p23970_1 := h23970c.2.1
                  have p23970_2 := h23970c.2.2.1
                  have p23970_3 := h23970c.2.2.2
                  linarith only [h19744, h23339, h23342, h23348, hc12, hc23, hlam, hphi, p23970_1]
                · have p23970_0 := h23970c.1
                  have p23970_1 := h23970c.2.1
                  have p23970_2 := h23970c.2.2.1
                  have p23970_3 := h23970c.2.2.2
                  linarith only [h22010, hc02, hc23, hlam, hphi, p23970_1]
                · have p23970_0 := h23970c.1
                  have p23970_1 := h23970c.2.1
                  have p23970_2 := h23970c.2.2.1
                  have p23970_3 := h23970c.2.2.2
                  rcases p23970_3 (m.d 0 2) (by simp) with h23996 | h23996
                  · linarith only [h23996, hlam, p23970_0]
                  · rcases p23970_3 (m.d 1 2) (by simp) with h23998 | h23998
                    · linarith only [h23342, h23998, hlam]
                    · rcases p23970_3 (m.d 2 3) (by simp) with h24000 | h24000
                      · rcases p23970_3 (m.d 2 4) (by simp) with h24001 | h24001
                        · rcases p23970_3 (m.d 2 5) (by simp) with h24002 | h24002
                          · linarith only [h23947, h24002, hlam]
                          · linarith only [h22010, h24002, hlam]
                        · linarith only [h24001, hlam, p23970_0]
                      · linarith only [h24000, h4, hlam]
                · have p23970_0 := h23970c.1
                  have p23970_1 := h23970c.2.1
                  have p23970_2 := h23970c.2.2.1
                  have p23970_3 := h23970c.2.2.2
                  rcases p23970_3 (m.d 0 2) (by simp) with h24007 | h24007
                  · linarith only [h19744, h24007, hlam]
                  · linarith only [h0, h24007, hlam]
                · have p23970_0 := h23970c.1
                  have p23970_1 := h23970c.2.1
                  have p23970_2 := h23970c.2.2.1
                  have p23970_3 := h23970c.2.2.2
                  linarith only [h23945, hlam, p23970_0]
                · have p23970_0 := h23970c.1
                  have p23970_1 := h23970c.2.1
                  have p23970_2 := h23970c.2.2.1
                  have p23970_3 := h23970c.2.2.2
                  linarith only [hlam, p23970_0]
                · have p23970_0 := h23970c.1
                  have p23970_1 := h23970c.2.1
                  have p23970_2 := h23970c.2.2.1
                  have p23970_3 := h23970c.2.2.2
                  linarith only [h22010, h23339, h23342, h23348, hc12, hc24, hlam, hphi, p23970_1]
                · have p23970_0 := h23970c.1
                  have p23970_1 := h23970c.2.1
                  have p23970_2 := h23970c.2.2.1
                  have p23970_3 := h23970c.2.2.2
                  rcases p23970_3 (m.d 0 2) (by simp) with h24013 | h24013
                  · linarith only [h24013, hlam, p23970_0]
                  · rcases p23970_3 (m.d 1 2) (by simp) with h24015 | h24015
                    · linarith only [h23344, h24015, hlam]
                    · rcases p23970_3 (m.d 2 3) (by simp) with h24017 | h24017
                      · rcases p23970_3 (m.d 2 4) (by simp) with h24018 | h24018
                        · rcases p23970_3 (m.d 2 5) (by simp) with h24019 | h24019
                          · rcases h4bigk with h24020c | h24020c | h24020c | h24020c | h24020c | h24020c | h24020c | h24020c | h24020c | h24020c | h24020c | h24020c | h24020c | h24020c | h24020c | h24020c | h24020c | h24020c | h24020c | h24020c | h24020c | h24020c | h24020c | h24020c | h24020c
                            · have p24020_0 := h24020c.1
                              have p24020_1 := h24020c.2.1
                              have p24020_2 := h24020c.2.2.1
                              have p24020_3 := h24020c.2.2.2
                              linarith only [hlam, p24020_0]
                            · have p24020_0 := h24020c.1
                              have p24020_1 := h24020c.2.1
                              have p24020_2 := h24020c.2.2.1
                              have p24020_3 := h24020c.2.2.2
                              rcases p24020_3 (m.d 0 4) (by simp) with h24022 | h24022
                              · rcases p24020_3 (m.d 1 4) (by simp) with h24023 | h24023
                                · linarith only [h2, h24023, hlam]
                                · rcases p24020_3 (m.d 2 4) (by simp) with h24025 | h24025
                                  · rcases p24020_3 (m.d 3 4) (by simp) with h24026 | h24026
                                    · linarith only [h23337, h24026, hlam]
                                    · rcases p24020_3 (m.d 4 5) (by simp) with h24028 | h24028
                                      · linarith only [h23339, h24028, hlam]
                                      · linarith only [h23348, h24028, hlam]
                                  · linarith only [h23342, h24025, hlam]
                              · linarith only [h2, h24022, hlam]
                            · have p24020_0 := h24020c.1
                              have p24020_1 := h24020c.2.1
                              have p24020_2 := h24020c.2.2.1
                              have p24020_3 := h24020c.2.2.2
                              linarith only [h19744, hlam, p24020_1]
                            · have p24020_0 := h24020c.1
                              have p24020_1 := h24020c.2.1
                              have p24020_2 := h24020c.2.2.1
                              have p24020_3 := h24020c.2.2.2
                              rcases p24020_3 (m.d 0 4) (by simp) with h24034 | h24034
                              · rcases p24020_3 (m.d 1 4) (by simp) with h24035 | h24035
                                · linarith only [h2, h24035, hlam]
                                · linarith only [h23346, h24035, hlam]
                              · linarith only [h23337, h24034, hlam]
                            · have p24020_0 := h24020c.1
                              have p24020_1 := h24020c.2.1
                              have p24020_2 := h24020c.2.2.1
                              have p24020_3 := h24020c.2.2.2
                              linarith only [h23337, h23342, h23348, h4, hc12, hc23, hlam, hphi, p24020_1]
                            · have p24020_0 := h24020c.1
                              have p24020_1 := h24020c.2.1
                              have p24020_2 := h24020c.2.2.1
                              have p24020_3 := h24020c.2.2.2
                              linarith only [h2, hlam, p24020_0]
                            · have p24020_0 := h24020c.1
                              have p24020_1 := h24020c.2.1
                              have p24020_2 := h24020c.2.2.1
                              have p24020_3 := h24020c.2.2.2
                              linarith only [hlam, p24020_0]
                            · have p24020_0 := h24020c.1
                              have p24020_1 := h24020c.2.1
                              have p24020_2 := h24020c.2.2.1
                              have p24020_3 := h24020c.2.2.2
                              linarith only [h23342, hlam, p24020_1]
                            · have p24020_0 := h24020c.1
                              have p24020_1 := h24020c.2.1
                              have p24020_2 := h24020c.2.2.1
                              have p24020_3 := h24020c.2.2.2
                              linarith only [h23348, hc34, hc45, hlam, hphi, p24020_1]
                            · have p24020_0 := h24020c.1
                              have p24020_1 := h24020c.2.1
                              have p24020_2 := h24020c.2.2.1
                              have p24020_3 := h24020c.2.2.2
                              linarith only [h23348, hlam, p24020_0]
                            · have p24020_0 := h24020c.1
                              have p24020_1 := h24020c.2.1
                              have p24020_2 := h24020c.2.2.1
                              have p24020_3 := h24020c.2.2.2
                              linarith only [h23339, h23348, h23945, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p24020_1]
                            · have p24020_0 := h24020c.1
                              have p24020_1 := h24020c.2.1
                              have p24020_2 := h24020c.2.2.1
                              have p24020_3 := h24020c.2.2.2
                              rcases p24020_3 (m.d 0 4) (by simp) with h24046 | h24046
                              · linarith only [h19744, h24046, hlam]
                              · linarith only [h2, h24046, hlam]
                            · have p24020_0 := h24020c.1
                              have p24020_1 := h24020c.2.1
                              have p24020_2 := h24020c.2.2.1
                              have p24020_3 := h24020c.2.2.2
                              linarith only [hlam, p24020_0]
                            · have p24020_0 := h24020c.1
                              have p24020_1 := h24020c.2.1
                              have p24020_2 := h24020c.2.2.1
                              have p24020_3 := h24020c.2.2.2
                              rcases p24020_3 (m.d 0 4) (by simp) with h24050 | h24050
                              · linarith only [h19744, h24050, hlam]
                              · linarith only [h23337, h24050, hlam]
                            · have p24020_0 := h24020c.1
                              have p24020_1 := h24020c.2.1
                              have p24020_2 := h24020c.2.2.1
                              have p24020_3 := h24020c.2.2.2
                              linarith only [h23342, h23348, hc12, hc24, hlam, hphi, p24020_1]
                            · have p24020_0 := h24020c.1
                              have p24020_1 := h24020c.2.1
                              have p24020_2 := h24020c.2.2.1
                              have p24020_3 := h24020c.2.2.2
                              linarith only [h23337, hlam, p24020_0]
                            · have p24020_0 := h24020c.1
                              have p24020_1 := h24020c.2.1
                              have p24020_2 := h24020c.2.2.1
                              have p24020_3 := h24020c.2.2.2
                              linarith only [h23346, hlam, p24020_0]
                            · have p24020_0 := h24020c.1
                              have p24020_1 := h24020c.2.1
                              have p24020_2 := h24020c.2.2.1
                              have p24020_3 := h24020c.2.2.2
                              linarith only [h23945, hlam, p24020_0]
                            · have p24020_0 := h24020c.1
                              have p24020_1 := h24020c.2.1
                              have p24020_2 := h24020c.2.2.1
                              have p24020_3 := h24020c.2.2.2
                              linarith only [hlam, p24020_0]
                            · have p24020_0 := h24020c.1
                              have p24020_1 := h24020c.2.1
                              have p24020_2 := h24020c.2.2.1
                              have p24020_3 := h24020c.2.2.2
                              linarith only [h23948, hlam, p24020_0]
                            · have p24020_0 := h24020c.1
                              have p24020_1 := h24020c.2.1
                              have p24020_2 := h24020c.2.2.1
                              have p24020_3 := h24020c.2.2.2
                              linarith only [h23339, hlam, p24020_0]
                            · have p24020_0 := h24020c.1
                              have p24020_1 := h24020c.2.1
                              have p24020_2 := h24020c.2.2.1
                              have p24020_3 := h24020c.2.2.2
                              linarith only [h19744, h23339, h23342, hc12, hc24, hlam, hphi, p24020_1]
                            · have p24020_0 := h24020c.1
                              have p24020_1 := h24020c.2.1
                              have p24020_2 := h24020c.2.2.1
                              have p24020_3 := h24020c.2.2.2
                              linarith only [h23947, hlam, p24020_0]
                            · have p24020_0 := h24020c.1
                              have p24020_1 := h24020c.2.1
                              have p24020_2 := h24020c.2.2.1
                              have p24020_3 := h24020c.2.2.2
                              rcases p24020_3 (m.d 0 4) (by simp) with h24062 | h24062
                              · rcases p24020_3 (m.d 1 4) (by simp) with h24063 | h24063
                                · linarith only [h23348, h24063, hlam]
                                · linarith only [h23346, h24063, hlam]
                              · linarith only [h23337, h24062, hlam]
                            · have p24020_0 := h24020c.1
                              have p24020_1 := h24020c.2.1
                              have p24020_2 := h24020c.2.2.1
                              have p24020_3 := h24020c.2.2.2
                              linarith only [hlam, p24020_0]
                          · linarith only [h24019, hlam, p23970_0]
                        · linarith only [h19744, h24018, hlam]
                      · linarith only [h24017, h4, hlam]
                · have p23970_0 := h23970c.1
                  have p23970_1 := h23970c.2.1
                  have p23970_2 := h23970c.2.2.1
                  have p23970_3 := h23970c.2.2.2
                  rcases p23970_3 (m.d 0 2) (by simp) with h24071 | h24071
                  · linarith only [h22010, h24071, hlam]
                  · linarith only [h0, h24071, hlam]
                · have p23970_0 := h23970c.1
                  have p23970_1 := h23970c.2.1
                  have p23970_2 := h23970c.2.2.1
                  have p23970_3 := h23970c.2.2.2
                  linarith only [h23946, hlam, p23970_0]
                · have p23970_0 := h23970c.1
                  have p23970_1 := h23970c.2.1
                  have p23970_2 := h23970c.2.2.1
                  have p23970_3 := h23970c.2.2.2
                  linarith only [h23947, hlam, p23970_1]
                · have p23970_0 := h23970c.1
                  have p23970_1 := h23970c.2.1
                  have p23970_2 := h23970c.2.2.1
                  have p23970_3 := h23970c.2.2.2
                  linarith only [hlam, p23970_0]
              · rcases h2bigk with h24077c | h24077c | h24077c | h24077c | h24077c | h24077c | h24077c | h24077c | h24077c | h24077c | h24077c | h24077c | h24077c | h24077c | h24077c | h24077c | h24077c | h24077c | h24077c | h24077c | h24077c | h24077c | h24077c | h24077c | h24077c
                · have p24077_0 := h24077c.1
                  have p24077_1 := h24077c.2.1
                  have p24077_2 := h24077c.2.2.1
                  have p24077_3 := h24077c.2.2.2
                  linarith only [hlam, p24077_0]
                · have p24077_0 := h24077c.1
                  have p24077_1 := h24077c.2.1
                  have p24077_2 := h24077c.2.2.1
                  have p24077_3 := h24077c.2.2.2
                  linarith only [h4, hc12, hc23, hlam, hphi, p24077_1]
                · have p24077_0 := h24077c.1
                  have p24077_1 := h24077c.2.1
                  have p24077_2 := h24077c.2.2.1
                  have p24077_3 := h24077c.2.2.2
                  linarith only [h4, hlam, p24077_0]
                · have p24077_0 := h24077c.1
                  have p24077_1 := h24077c.2.1
                  have p24077_2 := h24077c.2.2.1
                  have p24077_3 := h24077c.2.2.2
                  linarith only [h19744, hlam, p24077_0]
                · have p24077_0 := h24077c.1
                  have p24077_1 := h24077c.2.1
                  have p24077_2 := h24077c.2.2.1
                  have p24077_3 := h24077c.2.2.2
                  linarith only [h22010, hlam, p24077_0]
                · have p24077_0 := h24077c.1
                  have p24077_1 := h24077c.2.1
                  have p24077_2 := h24077c.2.2.1
                  have p24077_3 := h24077c.2.2.2
                  linarith only [h0, hlam, p24077_1]
                · have p24077_0 := h24077c.1
                  have p24077_1 := h24077c.2.1
                  have p24077_2 := h24077c.2.2.1
                  have p24077_3 := h24077c.2.2.2
                  linarith only [hlam, p24077_0]
                · have p24077_0 := h24077c.1
                  have p24077_1 := h24077c.2.1
                  have p24077_2 := h24077c.2.2.1
                  have p24077_3 := h24077c.2.2.2
                  linarith only [h23340, hlam, p24077_0]
                · have p24077_0 := h24077c.1
                  have p24077_1 := h24077c.2.1
                  have p24077_2 := h24077c.2.2.1
                  have p24077_3 := h24077c.2.2.2
                  linarith only [h23342, hlam, p24077_0]
                · have p24077_0 := h24077c.1
                  have p24077_1 := h24077c.2.1
                  have p24077_2 := h24077c.2.2.1
                  have p24077_3 := h24077c.2.2.2
                  linarith only [h23344, hlam, p24077_0]
                · have p24077_0 := h24077c.1
                  have p24077_1 := h24077c.2.1
                  have p24077_2 := h24077c.2.2.1
                  have p24077_3 := h24077c.2.2.2
                  rcases p24077_3 (m.d 0 2) (by simp) with h24088 | h24088
                  · linarith only [h24088, hlam, p24077_0]
                  · rcases p24077_3 (m.d 1 2) (by simp) with h24090 | h24090
                    · linarith only [h23340, h24090, hlam]
                    · rcases p24077_3 (m.d 2 3) (by simp) with h24092 | h24092
                      · rcases p24077_3 (m.d 2 4) (by simp) with h24093 | h24093
                        · linarith only [h23945, h24093, hlam]
                        · linarith only [h19744, h24093, hlam]
                      · linarith only [h24092, hlam, p24077_0]
                · have p24077_0 := h24077c.1
                  have p24077_1 := h24077c.2.1
                  have p24077_2 := h24077c.2.2.1
                  have p24077_3 := h24077c.2.2.2
                  rcases p24077_3 (m.d 0 2) (by simp) with h24097 | h24097
                  · linarith only [h24097, h4, hlam]
                  · linarith only [h0, h24097, hlam]
                · have p24077_0 := h24077c.1
                  have p24077_1 := h24077c.2.1
                  have p24077_2 := h24077c.2.2.1
                  have p24077_3 := h24077c.2.2.2
                  linarith only [hlam, p24077_0]
                · have p24077_0 := h24077c.1
                  have p24077_1 := h24077c.2.1
                  have p24077_2 := h24077c.2.2.1
                  have p24077_3 := h24077c.2.2.2
                  linarith only [h19744, hc02, hc23, hlam, hphi, p24077_1]
                · have p24077_0 := h24077c.1
                  have p24077_1 := h24077c.2.1
                  have p24077_2 := h24077c.2.2.1
                  have p24077_3 := h24077c.2.2.2
                  linarith only [h0, h22010, hc12, hc23, hlam, hphi, p24077_1]
                · have p24077_0 := h24077c.1
                  have p24077_1 := h24077c.2.1
                  have p24077_2 := h24077c.2.2.1
                  have p24077_3 := h24077c.2.2.2
                  rcases p24077_3 (m.d 0 2) (by simp) with h24103 | h24103
                  · linarith only [h24103, hlam, p24077_0]
                  · rcases p24077_3 (m.d 1 2) (by simp) with h24105 | h24105
                    · linarith only [h23342, h24105, hlam]
                    · rcases p24077_3 (m.d 2 3) (by simp) with h24107 | h24107
                      · rcases p24077_3 (m.d 2 4) (by simp) with h24108 | h24108
                        · rcases p24077_3 (m.d 2 5) (by simp) with h24109 | h24109
                          · linarith only [h23947, h24109, hlam]
                          · linarith only [h22010, h24109, hlam]
                        · linarith only [h24108, hlam, p24077_0]
                      · linarith only [h24107, h4, hlam]
                · have p24077_0 := h24077c.1
                  have p24077_1 := h24077c.2.1
                  have p24077_2 := h24077c.2.2.1
                  have p24077_3 := h24077c.2.2.2
                  rcases p24077_3 (m.d 0 2) (by simp) with h24114 | h24114
                  · linarith only [h19744, h24114, hlam]
                  · linarith only [h0, h24114, hlam]
                · have p24077_0 := h24077c.1
                  have p24077_1 := h24077c.2.1
                  have p24077_2 := h24077c.2.2.1
                  have p24077_3 := h24077c.2.2.2
                  linarith only [h23945, hlam, p24077_0]
                · have p24077_0 := h24077c.1
                  have p24077_1 := h24077c.2.1
                  have p24077_2 := h24077c.2.2.1
                  have p24077_3 := h24077c.2.2.2
                  linarith only [hlam, p24077_0]
                · have p24077_0 := h24077c.1
                  have p24077_1 := h24077c.2.1
                  have p24077_2 := h24077c.2.2.1
                  have p24077_3 := h24077c.2.2.2
                  linarith only [h0, h22010, hc12, hc24, hlam, hphi, p24077_1]
                · have p24077_0 := h24077c.1
                  have p24077_1 := h24077c.2.1
                  have p24077_2 := h24077c.2.2.1
                  have p24077_3 := h24077c.2.2.2
                  rcases p24077_3 (m.d 0 2) (by simp) with h24120 | h24120
                  · linarith only [h24120, hlam, p24077_0]
                  · rcases p24077_3 (m.d 1 2) (by simp) with h24122 | h24122
                    · linarith only [h23344, h24122, hlam]
                    · rcases p24077_3 (m.d 2 3) (by simp) with h24124 | h24124
                      · rcases p24077_3 (m.d 2 4) (by simp) with h24125 | h24125
                        · rcases p24077_3 (m.d 2 5) (by simp) with h24126 | h24126
                          · rcases h4bigk with h24127c | h24127c | h24127c | h24127c | h24127c | h24127c | h24127c | h24127c | h24127c | h24127c | h24127c | h24127c | h24127c | h24127c | h24127c | h24127c | h24127c | h24127c | h24127c | h24127c | h24127c | h24127c | h24127c | h24127c | h24127c
                            · have p24127_0 := h24127c.1
                              have p24127_1 := h24127c.2.1
                              have p24127_2 := h24127c.2.2.1
                              have p24127_3 := h24127c.2.2.2
                              linarith only [hlam, p24127_0]
                            · have p24127_0 := h24127c.1
                              have p24127_1 := h24127c.2.1
                              have p24127_2 := h24127c.2.2.1
                              have p24127_3 := h24127c.2.2.2
                              rcases p24127_3 (m.d 0 4) (by simp) with h24129 | h24129
                              · rcases p24127_3 (m.d 1 4) (by simp) with h24130 | h24130
                                · linarith only [h2, h24130, hlam]
                                · rcases p24127_3 (m.d 2 4) (by simp) with h24132 | h24132
                                  · rcases p24127_3 (m.d 3 4) (by simp) with h24133 | h24133
                                    · linarith only [h23337, h24133, hlam]
                                    · rcases p24127_3 (m.d 4 5) (by simp) with h24135 | h24135
                                      · linarith only [h23339, h24135, hlam]
                                      · linarith only [h23348, h24135, hlam]
                                  · linarith only [h23342, h24132, hlam]
                              · linarith only [h2, h24129, hlam]
                            · have p24127_0 := h24127c.1
                              have p24127_1 := h24127c.2.1
                              have p24127_2 := h24127c.2.2.1
                              have p24127_3 := h24127c.2.2.2
                              linarith only [h19744, hlam, p24127_1]
                            · have p24127_0 := h24127c.1
                              have p24127_1 := h24127c.2.1
                              have p24127_2 := h24127c.2.2.1
                              have p24127_3 := h24127c.2.2.2
                              rcases p24127_3 (m.d 0 4) (by simp) with h24141 | h24141
                              · rcases p24127_3 (m.d 1 4) (by simp) with h24142 | h24142
                                · linarith only [h2, h24142, hlam]
                                · linarith only [h23346, h24142, hlam]
                              · linarith only [h23337, h24141, hlam]
                            · have p24127_0 := h24127c.1
                              have p24127_1 := h24127c.2.1
                              have p24127_2 := h24127c.2.2.1
                              have p24127_3 := h24127c.2.2.2
                              linarith only [h23337, h23342, h23348, h4, hc12, hc23, hlam, hphi, p24127_1]
                            · have p24127_0 := h24127c.1
                              have p24127_1 := h24127c.2.1
                              have p24127_2 := h24127c.2.2.1
                              have p24127_3 := h24127c.2.2.2
                              linarith only [h2, hlam, p24127_0]
                            · have p24127_0 := h24127c.1
                              have p24127_1 := h24127c.2.1
                              have p24127_2 := h24127c.2.2.1
                              have p24127_3 := h24127c.2.2.2
                              linarith only [hlam, p24127_0]
                            · have p24127_0 := h24127c.1
                              have p24127_1 := h24127c.2.1
                              have p24127_2 := h24127c.2.2.1
                              have p24127_3 := h24127c.2.2.2
                              linarith only [h23342, hlam, p24127_1]
                            · have p24127_0 := h24127c.1
                              have p24127_1 := h24127c.2.1
                              have p24127_2 := h24127c.2.2.1
                              have p24127_3 := h24127c.2.2.2
                              linarith only [h23346, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23950_1, p24127_1]
                            · have p24127_0 := h24127c.1
                              have p24127_1 := h24127c.2.1
                              have p24127_2 := h24127c.2.2.1
                              have p24127_3 := h24127c.2.2.2
                              linarith only [h23348, hlam, p24127_0]
                            · have p24127_0 := h24127c.1
                              have p24127_1 := h24127c.2.1
                              have p24127_2 := h24127c.2.2.1
                              have p24127_3 := h24127c.2.2.2
                              linarith only [h23339, h23348, h23945, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p24127_1]
                            · have p24127_0 := h24127c.1
                              have p24127_1 := h24127c.2.1
                              have p24127_2 := h24127c.2.2.1
                              have p24127_3 := h24127c.2.2.2
                              rcases p24127_3 (m.d 0 4) (by simp) with h24153 | h24153
                              · linarith only [h19744, h24153, hlam]
                              · linarith only [h2, h24153, hlam]
                            · have p24127_0 := h24127c.1
                              have p24127_1 := h24127c.2.1
                              have p24127_2 := h24127c.2.2.1
                              have p24127_3 := h24127c.2.2.2
                              linarith only [hlam, p24127_0]
                            · have p24127_0 := h24127c.1
                              have p24127_1 := h24127c.2.1
                              have p24127_2 := h24127c.2.2.1
                              have p24127_3 := h24127c.2.2.2
                              rcases p24127_3 (m.d 0 4) (by simp) with h24157 | h24157
                              · linarith only [h19744, h24157, hlam]
                              · linarith only [h23337, h24157, hlam]
                            · have p24127_0 := h24127c.1
                              have p24127_1 := h24127c.2.1
                              have p24127_2 := h24127c.2.2.1
                              have p24127_3 := h24127c.2.2.2
                              linarith only [h23342, h23348, hc12, hc24, hlam, hphi, p24127_1]
                            · have p24127_0 := h24127c.1
                              have p24127_1 := h24127c.2.1
                              have p24127_2 := h24127c.2.2.1
                              have p24127_3 := h24127c.2.2.2
                              linarith only [h23337, hlam, p24127_0]
                            · have p24127_0 := h24127c.1
                              have p24127_1 := h24127c.2.1
                              have p24127_2 := h24127c.2.2.1
                              have p24127_3 := h24127c.2.2.2
                              linarith only [h23346, hlam, p24127_0]
                            · have p24127_0 := h24127c.1
                              have p24127_1 := h24127c.2.1
                              have p24127_2 := h24127c.2.2.1
                              have p24127_3 := h24127c.2.2.2
                              linarith only [h23945, hlam, p24127_0]
                            · have p24127_0 := h24127c.1
                              have p24127_1 := h24127c.2.1
                              have p24127_2 := h24127c.2.2.1
                              have p24127_3 := h24127c.2.2.2
                              linarith only [hlam, p24127_0]
                            · have p24127_0 := h24127c.1
                              have p24127_1 := h24127c.2.1
                              have p24127_2 := h24127c.2.2.1
                              have p24127_3 := h24127c.2.2.2
                              linarith only [h23948, hlam, p24127_0]
                            · have p24127_0 := h24127c.1
                              have p24127_1 := h24127c.2.1
                              have p24127_2 := h24127c.2.2.1
                              have p24127_3 := h24127c.2.2.2
                              linarith only [h23339, hlam, p24127_0]
                            · have p24127_0 := h24127c.1
                              have p24127_1 := h24127c.2.1
                              have p24127_2 := h24127c.2.2.1
                              have p24127_3 := h24127c.2.2.2
                              linarith only [h23337, h23339, h23342, h4, hc12, hc23, hlam, hphi, p24127_1]
                            · have p24127_0 := h24127c.1
                              have p24127_1 := h24127c.2.1
                              have p24127_2 := h24127c.2.2.1
                              have p24127_3 := h24127c.2.2.2
                              linarith only [h23947, hlam, p24127_0]
                            · have p24127_0 := h24127c.1
                              have p24127_1 := h24127c.2.1
                              have p24127_2 := h24127c.2.2.1
                              have p24127_3 := h24127c.2.2.2
                              rcases p24127_3 (m.d 0 4) (by simp) with h24169 | h24169
                              · rcases p24127_3 (m.d 1 4) (by simp) with h24170 | h24170
                                · linarith only [h23348, h24170, hlam]
                                · linarith only [h23346, h24170, hlam]
                              · linarith only [h23337, h24169, hlam]
                            · have p24127_0 := h24127c.1
                              have p24127_1 := h24127c.2.1
                              have p24127_2 := h24127c.2.2.1
                              have p24127_3 := h24127c.2.2.2
                              linarith only [hlam, p24127_0]
                          · linarith only [h24126, hlam, p24077_0]
                        · linarith only [h19744, h24125, hlam]
                      · linarith only [h24124, h4, hlam]
                · have p24077_0 := h24077c.1
                  have p24077_1 := h24077c.2.1
                  have p24077_2 := h24077c.2.2.1
                  have p24077_3 := h24077c.2.2.2
                  rcases p24077_3 (m.d 0 2) (by simp) with h24178 | h24178
                  · linarith only [h22010, h24178, hlam]
                  · linarith only [h0, h24178, hlam]
                · have p24077_0 := h24077c.1
                  have p24077_1 := h24077c.2.1
                  have p24077_2 := h24077c.2.2.1
                  have p24077_3 := h24077c.2.2.2
                  linarith only [h23946, hlam, p24077_0]
                · have p24077_0 := h24077c.1
                  have p24077_1 := h24077c.2.1
                  have p24077_2 := h24077c.2.2.1
                  have p24077_3 := h24077c.2.2.2
                  linarith only [h23947, hlam, p24077_1]
                · have p24077_0 := h24077c.1
                  have p24077_1 := h24077c.2.1
                  have p24077_2 := h24077c.2.2.1
                  have p24077_3 := h24077c.2.2.2
                  linarith only [hlam, p24077_0]
              · rcases h2bigk with h24184c | h24184c | h24184c | h24184c | h24184c | h24184c | h24184c | h24184c | h24184c | h24184c | h24184c | h24184c | h24184c | h24184c | h24184c | h24184c | h24184c | h24184c | h24184c | h24184c | h24184c | h24184c | h24184c | h24184c | h24184c
                · have p24184_0 := h24184c.1
                  have p24184_1 := h24184c.2.1
                  have p24184_2 := h24184c.2.2.1
                  have p24184_3 := h24184c.2.2.2
                  linarith only [hlam, p24184_0]
                · have p24184_0 := h24184c.1
                  have p24184_1 := h24184c.2.1
                  have p24184_2 := h24184c.2.2.1
                  have p24184_3 := h24184c.2.2.2
                  linarith only [h4, hc12, hc23, hlam, hphi, p24184_1]
                · have p24184_0 := h24184c.1
                  have p24184_1 := h24184c.2.1
                  have p24184_2 := h24184c.2.2.1
                  have p24184_3 := h24184c.2.2.2
                  linarith only [h4, hlam, p24184_0]
                · have p24184_0 := h24184c.1
                  have p24184_1 := h24184c.2.1
                  have p24184_2 := h24184c.2.2.1
                  have p24184_3 := h24184c.2.2.2
                  linarith only [h19744, hlam, p24184_0]
                · have p24184_0 := h24184c.1
                  have p24184_1 := h24184c.2.1
                  have p24184_2 := h24184c.2.2.1
                  have p24184_3 := h24184c.2.2.2
                  linarith only [h22010, hlam, p24184_0]
                · have p24184_0 := h24184c.1
                  have p24184_1 := h24184c.2.1
                  have p24184_2 := h24184c.2.2.1
                  have p24184_3 := h24184c.2.2.2
                  linarith only [h0, hlam, p24184_1]
                · have p24184_0 := h24184c.1
                  have p24184_1 := h24184c.2.1
                  have p24184_2 := h24184c.2.2.1
                  have p24184_3 := h24184c.2.2.2
                  linarith only [hlam, p24184_0]
                · have p24184_0 := h24184c.1
                  have p24184_1 := h24184c.2.1
                  have p24184_2 := h24184c.2.2.1
                  have p24184_3 := h24184c.2.2.2
                  linarith only [h23340, hlam, p24184_0]
                · have p24184_0 := h24184c.1
                  have p24184_1 := h24184c.2.1
                  have p24184_2 := h24184c.2.2.1
                  have p24184_3 := h24184c.2.2.2
                  linarith only [h23342, hlam, p24184_0]
                · have p24184_0 := h24184c.1
                  have p24184_1 := h24184c.2.1
                  have p24184_2 := h24184c.2.2.1
                  have p24184_3 := h24184c.2.2.2
                  linarith only [h23344, hlam, p24184_0]
                · have p24184_0 := h24184c.1
                  have p24184_1 := h24184c.2.1
                  have p24184_2 := h24184c.2.2.1
                  have p24184_3 := h24184c.2.2.2
                  rcases p24184_3 (m.d 0 2) (by simp) with h24195 | h24195
                  · linarith only [h24195, hlam, p24184_0]
                  · rcases p24184_3 (m.d 1 2) (by simp) with h24197 | h24197
                    · linarith only [h23340, h24197, hlam]
                    · rcases p24184_3 (m.d 2 3) (by simp) with h24199 | h24199
                      · rcases p24184_3 (m.d 2 4) (by simp) with h24200 | h24200
                        · linarith only [h23945, h24200, hlam]
                        · linarith only [h19744, h24200, hlam]
                      · linarith only [h24199, hlam, p24184_0]
                · have p24184_0 := h24184c.1
                  have p24184_1 := h24184c.2.1
                  have p24184_2 := h24184c.2.2.1
                  have p24184_3 := h24184c.2.2.2
                  rcases p24184_3 (m.d 0 2) (by simp) with h24204 | h24204
                  · linarith only [h24204, h4, hlam]
                  · linarith only [h0, h24204, hlam]
                · have p24184_0 := h24184c.1
                  have p24184_1 := h24184c.2.1
                  have p24184_2 := h24184c.2.2.1
                  have p24184_3 := h24184c.2.2.2
                  linarith only [hlam, p24184_0]
                · have p24184_0 := h24184c.1
                  have p24184_1 := h24184c.2.1
                  have p24184_2 := h24184c.2.2.1
                  have p24184_3 := h24184c.2.2.2
                  linarith only [h19744, hc02, hc23, hlam, hphi, p24184_1]
                · have p24184_0 := h24184c.1
                  have p24184_1 := h24184c.2.1
                  have p24184_2 := h24184c.2.2.1
                  have p24184_3 := h24184c.2.2.2
                  linarith only [h0, h22010, hc12, hc23, hlam, hphi, p24184_1]
                · have p24184_0 := h24184c.1
                  have p24184_1 := h24184c.2.1
                  have p24184_2 := h24184c.2.2.1
                  have p24184_3 := h24184c.2.2.2
                  rcases p24184_3 (m.d 0 2) (by simp) with h24210 | h24210
                  · linarith only [h24210, hlam, p24184_0]
                  · rcases p24184_3 (m.d 1 2) (by simp) with h24212 | h24212
                    · linarith only [h23342, h24212, hlam]
                    · rcases p24184_3 (m.d 2 3) (by simp) with h24214 | h24214
                      · rcases p24184_3 (m.d 2 4) (by simp) with h24215 | h24215
                        · rcases p24184_3 (m.d 2 5) (by simp) with h24216 | h24216
                          · linarith only [h23947, h24216, hlam]
                          · linarith only [h22010, h24216, hlam]
                        · linarith only [h24215, hlam, p24184_0]
                      · linarith only [h24214, h4, hlam]
                · have p24184_0 := h24184c.1
                  have p24184_1 := h24184c.2.1
                  have p24184_2 := h24184c.2.2.1
                  have p24184_3 := h24184c.2.2.2
                  rcases p24184_3 (m.d 0 2) (by simp) with h24221 | h24221
                  · linarith only [h19744, h24221, hlam]
                  · linarith only [h0, h24221, hlam]
                · have p24184_0 := h24184c.1
                  have p24184_1 := h24184c.2.1
                  have p24184_2 := h24184c.2.2.1
                  have p24184_3 := h24184c.2.2.2
                  linarith only [h23945, hlam, p24184_0]
                · have p24184_0 := h24184c.1
                  have p24184_1 := h24184c.2.1
                  have p24184_2 := h24184c.2.2.1
                  have p24184_3 := h24184c.2.2.2
                  linarith only [hlam, p24184_0]
                · have p24184_0 := h24184c.1
                  have p24184_1 := h24184c.2.1
                  have p24184_2 := h24184c.2.2.1
                  have p24184_3 := h24184c.2.2.2
                  linarith only [h0, h22010, hc12, hc24, hlam, hphi, p24184_1]
                · have p24184_0 := h24184c.1
                  have p24184_1 := h24184c.2.1
                  have p24184_2 := h24184c.2.2.1
                  have p24184_3 := h24184c.2.2.2
                  rcases p24184_3 (m.d 0 2) (by simp) with h24227 | h24227
                  · linarith only [h24227, hlam, p24184_0]
                  · rcases p24184_3 (m.d 1 2) (by simp) with h24229 | h24229
                    · linarith only [h23344, h24229, hlam]
                    · rcases p24184_3 (m.d 2 3) (by simp) with h24231 | h24231
                      · rcases p24184_3 (m.d 2 4) (by simp) with h24232 | h24232
                        · rcases p24184_3 (m.d 2 5) (by simp) with h24233 | h24233
                          · rcases h4bigk with h24234c | h24234c | h24234c | h24234c | h24234c | h24234c | h24234c | h24234c | h24234c | h24234c | h24234c | h24234c | h24234c | h24234c | h24234c | h24234c | h24234c | h24234c | h24234c | h24234c | h24234c | h24234c | h24234c | h24234c | h24234c
                            · have p24234_0 := h24234c.1
                              have p24234_1 := h24234c.2.1
                              have p24234_2 := h24234c.2.2.1
                              have p24234_3 := h24234c.2.2.2
                              linarith only [hlam, p24234_0]
                            · have p24234_0 := h24234c.1
                              have p24234_1 := h24234c.2.1
                              have p24234_2 := h24234c.2.2.1
                              have p24234_3 := h24234c.2.2.2
                              rcases p24234_3 (m.d 0 4) (by simp) with h24236 | h24236
                              · rcases p24234_3 (m.d 1 4) (by simp) with h24237 | h24237
                                · linarith only [h2, h24237, hlam]
                                · rcases p24234_3 (m.d 2 4) (by simp) with h24239 | h24239
                                  · rcases p24234_3 (m.d 3 4) (by simp) with h24240 | h24240
                                    · linarith only [h23337, h24240, hlam]
                                    · rcases p24234_3 (m.d 4 5) (by simp) with h24242 | h24242
                                      · linarith only [h23339, h24242, hlam]
                                      · linarith only [h23348, h24242, hlam]
                                  · linarith only [h23342, h24239, hlam]
                              · linarith only [h2, h24236, hlam]
                            · have p24234_0 := h24234c.1
                              have p24234_1 := h24234c.2.1
                              have p24234_2 := h24234c.2.2.1
                              have p24234_3 := h24234c.2.2.2
                              linarith only [h19744, hlam, p24234_1]
                            · have p24234_0 := h24234c.1
                              have p24234_1 := h24234c.2.1
                              have p24234_2 := h24234c.2.2.1
                              have p24234_3 := h24234c.2.2.2
                              rcases p24234_3 (m.d 0 4) (by simp) with h24248 | h24248
                              · rcases p24234_3 (m.d 1 4) (by simp) with h24249 | h24249
                                · linarith only [h2, h24249, hlam]
                                · linarith only [h23346, h24249, hlam]
                              · linarith only [h23337, h24248, hlam]
                            · have p24234_0 := h24234c.1
                              have p24234_1 := h24234c.2.1
                              have p24234_2 := h24234c.2.2.1
                              have p24234_3 := h24234c.2.2.2
                              linarith only [h23337, h23342, h23348, h4, hc12, hc23, hlam, hphi, p24234_1]
                            · have p24234_0 := h24234c.1
                              have p24234_1 := h24234c.2.1
                              have p24234_2 := h24234c.2.2.1
                              have p24234_3 := h24234c.2.2.2
                              linarith only [h2, hlam, p24234_0]
                            · have p24234_0 := h24234c.1
                              have p24234_1 := h24234c.2.1
                              have p24234_2 := h24234c.2.2.1
                              have p24234_3 := h24234c.2.2.2
                              linarith only [hlam, p24234_0]
                            · have p24234_0 := h24234c.1
                              have p24234_1 := h24234c.2.1
                              have p24234_2 := h24234c.2.2.1
                              have p24234_3 := h24234c.2.2.2
                              linarith only [h23342, hlam, p24234_1]
                            · have p24234_0 := h24234c.1
                              have p24234_1 := h24234c.2.1
                              have p24234_2 := h24234c.2.2.1
                              have p24234_3 := h24234c.2.2.2
                              linarith only [h23346, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23950_1, p24234_1]
                            · have p24234_0 := h24234c.1
                              have p24234_1 := h24234c.2.1
                              have p24234_2 := h24234c.2.2.1
                              have p24234_3 := h24234c.2.2.2
                              linarith only [h23348, hlam, p24234_0]
                            · have p24234_0 := h24234c.1
                              have p24234_1 := h24234c.2.1
                              have p24234_2 := h24234c.2.2.1
                              have p24234_3 := h24234c.2.2.2
                              linarith only [h23339, h23348, h23945, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p24234_1]
                            · have p24234_0 := h24234c.1
                              have p24234_1 := h24234c.2.1
                              have p24234_2 := h24234c.2.2.1
                              have p24234_3 := h24234c.2.2.2
                              rcases p24234_3 (m.d 0 4) (by simp) with h24260 | h24260
                              · linarith only [h19744, h24260, hlam]
                              · linarith only [h2, h24260, hlam]
                            · have p24234_0 := h24234c.1
                              have p24234_1 := h24234c.2.1
                              have p24234_2 := h24234c.2.2.1
                              have p24234_3 := h24234c.2.2.2
                              linarith only [hlam, p24234_0]
                            · have p24234_0 := h24234c.1
                              have p24234_1 := h24234c.2.1
                              have p24234_2 := h24234c.2.2.1
                              have p24234_3 := h24234c.2.2.2
                              rcases p24234_3 (m.d 0 4) (by simp) with h24264 | h24264
                              · linarith only [h19744, h24264, hlam]
                              · linarith only [h23337, h24264, hlam]
                            · have p24234_0 := h24234c.1
                              have p24234_1 := h24234c.2.1
                              have p24234_2 := h24234c.2.2.1
                              have p24234_3 := h24234c.2.2.2
                              linarith only [h23342, h23348, hc12, hc24, hlam, hphi, p24234_1]
                            · have p24234_0 := h24234c.1
                              have p24234_1 := h24234c.2.1
                              have p24234_2 := h24234c.2.2.1
                              have p24234_3 := h24234c.2.2.2
                              linarith only [h23337, hlam, p24234_0]
                            · have p24234_0 := h24234c.1
                              have p24234_1 := h24234c.2.1
                              have p24234_2 := h24234c.2.2.1
                              have p24234_3 := h24234c.2.2.2
                              linarith only [h23346, hlam, p24234_0]
                            · have p24234_0 := h24234c.1
                              have p24234_1 := h24234c.2.1
                              have p24234_2 := h24234c.2.2.1
                              have p24234_3 := h24234c.2.2.2
                              linarith only [h23945, hlam, p24234_0]
                            · have p24234_0 := h24234c.1
                              have p24234_1 := h24234c.2.1
                              have p24234_2 := h24234c.2.2.1
                              have p24234_3 := h24234c.2.2.2
                              linarith only [hlam, p24234_0]
                            · have p24234_0 := h24234c.1
                              have p24234_1 := h24234c.2.1
                              have p24234_2 := h24234c.2.2.1
                              have p24234_3 := h24234c.2.2.2
                              linarith only [h23948, hlam, p24234_0]
                            · have p24234_0 := h24234c.1
                              have p24234_1 := h24234c.2.1
                              have p24234_2 := h24234c.2.2.1
                              have p24234_3 := h24234c.2.2.2
                              linarith only [h23339, hlam, p24234_0]
                            · have p24234_0 := h24234c.1
                              have p24234_1 := h24234c.2.1
                              have p24234_2 := h24234c.2.2.1
                              have p24234_3 := h24234c.2.2.2
                              linarith only [h23337, h23339, h23342, h4, hc12, hc23, hlam, hphi, p24234_1]
                            · have p24234_0 := h24234c.1
                              have p24234_1 := h24234c.2.1
                              have p24234_2 := h24234c.2.2.1
                              have p24234_3 := h24234c.2.2.2
                              linarith only [h23947, hlam, p24234_0]
                            · have p24234_0 := h24234c.1
                              have p24234_1 := h24234c.2.1
                              have p24234_2 := h24234c.2.2.1
                              have p24234_3 := h24234c.2.2.2
                              rcases p24234_3 (m.d 0 4) (by simp) with h24276 | h24276
                              · rcases p24234_3 (m.d 1 4) (by simp) with h24277 | h24277
                                · linarith only [h23348, h24277, hlam]
                                · linarith only [h23346, h24277, hlam]
                              · linarith only [h23337, h24276, hlam]
                            · have p24234_0 := h24234c.1
                              have p24234_1 := h24234c.2.1
                              have p24234_2 := h24234c.2.2.1
                              have p24234_3 := h24234c.2.2.2
                              linarith only [hlam, p24234_0]
                          · linarith only [h24233, hlam, p24184_0]
                        · linarith only [h19744, h24232, hlam]
                      · linarith only [h24231, h4, hlam]
                · have p24184_0 := h24184c.1
                  have p24184_1 := h24184c.2.1
                  have p24184_2 := h24184c.2.2.1
                  have p24184_3 := h24184c.2.2.2
                  rcases p24184_3 (m.d 0 2) (by simp) with h24285 | h24285
                  · linarith only [h22010, h24285, hlam]
                  · linarith only [h0, h24285, hlam]
                · have p24184_0 := h24184c.1
                  have p24184_1 := h24184c.2.1
                  have p24184_2 := h24184c.2.2.1
                  have p24184_3 := h24184c.2.2.2
                  linarith only [h23946, hlam, p24184_0]
                · have p24184_0 := h24184c.1
                  have p24184_1 := h24184c.2.1
                  have p24184_2 := h24184c.2.2.1
                  have p24184_3 := h24184c.2.2.2
                  linarith only [h23947, hlam, p24184_1]
                · have p24184_0 := h24184c.1
                  have p24184_1 := h24184c.2.1
                  have p24184_2 := h24184c.2.2.1
                  have p24184_3 := h24184c.2.2.2
                  linarith only [hlam, p24184_0]
              · rcases h2bigk with h24291c | h24291c | h24291c | h24291c | h24291c | h24291c | h24291c | h24291c | h24291c | h24291c | h24291c | h24291c | h24291c | h24291c | h24291c | h24291c | h24291c | h24291c | h24291c | h24291c | h24291c | h24291c | h24291c | h24291c | h24291c
                · have p24291_0 := h24291c.1
                  have p24291_1 := h24291c.2.1
                  have p24291_2 := h24291c.2.2.1
                  have p24291_3 := h24291c.2.2.2
                  linarith only [hlam, p24291_0]
                · have p24291_0 := h24291c.1
                  have p24291_1 := h24291c.2.1
                  have p24291_2 := h24291c.2.2.1
                  have p24291_3 := h24291c.2.2.2
                  linarith only [h4, hc12, hc23, hlam, hphi, p24291_1]
                · have p24291_0 := h24291c.1
                  have p24291_1 := h24291c.2.1
                  have p24291_2 := h24291c.2.2.1
                  have p24291_3 := h24291c.2.2.2
                  linarith only [h4, hlam, p24291_0]
                · have p24291_0 := h24291c.1
                  have p24291_1 := h24291c.2.1
                  have p24291_2 := h24291c.2.2.1
                  have p24291_3 := h24291c.2.2.2
                  linarith only [h19744, hlam, p24291_0]
                · have p24291_0 := h24291c.1
                  have p24291_1 := h24291c.2.1
                  have p24291_2 := h24291c.2.2.1
                  have p24291_3 := h24291c.2.2.2
                  linarith only [h22010, hlam, p24291_0]
                · have p24291_0 := h24291c.1
                  have p24291_1 := h24291c.2.1
                  have p24291_2 := h24291c.2.2.1
                  have p24291_3 := h24291c.2.2.2
                  linarith only [h0, hlam, p24291_1]
                · have p24291_0 := h24291c.1
                  have p24291_1 := h24291c.2.1
                  have p24291_2 := h24291c.2.2.1
                  have p24291_3 := h24291c.2.2.2
                  linarith only [hlam, p24291_0]
                · have p24291_0 := h24291c.1
                  have p24291_1 := h24291c.2.1
                  have p24291_2 := h24291c.2.2.1
                  have p24291_3 := h24291c.2.2.2
                  linarith only [h23340, hlam, p24291_0]
                · have p24291_0 := h24291c.1
                  have p24291_1 := h24291c.2.1
                  have p24291_2 := h24291c.2.2.1
                  have p24291_3 := h24291c.2.2.2
                  linarith only [h23342, hlam, p24291_0]
                · have p24291_0 := h24291c.1
                  have p24291_1 := h24291c.2.1
                  have p24291_2 := h24291c.2.2.1
                  have p24291_3 := h24291c.2.2.2
                  linarith only [h23344, hlam, p24291_0]
                · have p24291_0 := h24291c.1
                  have p24291_1 := h24291c.2.1
                  have p24291_2 := h24291c.2.2.1
                  have p24291_3 := h24291c.2.2.2
                  rcases p24291_3 (m.d 0 2) (by simp) with h24302 | h24302
                  · linarith only [h24302, hlam, p24291_0]
                  · rcases p24291_3 (m.d 1 2) (by simp) with h24304 | h24304
                    · linarith only [h23340, h24304, hlam]
                    · rcases p24291_3 (m.d 2 3) (by simp) with h24306 | h24306
                      · rcases p24291_3 (m.d 2 4) (by simp) with h24307 | h24307
                        · linarith only [h23945, h24307, hlam]
                        · linarith only [h19744, h24307, hlam]
                      · linarith only [h24306, hlam, p24291_0]
                · have p24291_0 := h24291c.1
                  have p24291_1 := h24291c.2.1
                  have p24291_2 := h24291c.2.2.1
                  have p24291_3 := h24291c.2.2.2
                  rcases p24291_3 (m.d 0 2) (by simp) with h24311 | h24311
                  · linarith only [h24311, h4, hlam]
                  · linarith only [h0, h24311, hlam]
                · have p24291_0 := h24291c.1
                  have p24291_1 := h24291c.2.1
                  have p24291_2 := h24291c.2.2.1
                  have p24291_3 := h24291c.2.2.2
                  linarith only [hlam, p24291_0]
                · have p24291_0 := h24291c.1
                  have p24291_1 := h24291c.2.1
                  have p24291_2 := h24291c.2.2.1
                  have p24291_3 := h24291c.2.2.2
                  linarith only [h19744, hc02, hc23, hlam, hphi, p24291_1]
                · have p24291_0 := h24291c.1
                  have p24291_1 := h24291c.2.1
                  have p24291_2 := h24291c.2.2.1
                  have p24291_3 := h24291c.2.2.2
                  linarith only [h0, h22010, hc12, hc23, hlam, hphi, p24291_1]
                · have p24291_0 := h24291c.1
                  have p24291_1 := h24291c.2.1
                  have p24291_2 := h24291c.2.2.1
                  have p24291_3 := h24291c.2.2.2
                  rcases p24291_3 (m.d 0 2) (by simp) with h24317 | h24317
                  · linarith only [h24317, hlam, p24291_0]
                  · rcases p24291_3 (m.d 1 2) (by simp) with h24319 | h24319
                    · linarith only [h23342, h24319, hlam]
                    · rcases p24291_3 (m.d 2 3) (by simp) with h24321 | h24321
                      · rcases p24291_3 (m.d 2 4) (by simp) with h24322 | h24322
                        · rcases p24291_3 (m.d 2 5) (by simp) with h24323 | h24323
                          · linarith only [h23947, h24323, hlam]
                          · linarith only [h22010, h24323, hlam]
                        · linarith only [h24322, hlam, p24291_0]
                      · linarith only [h24321, h4, hlam]
                · have p24291_0 := h24291c.1
                  have p24291_1 := h24291c.2.1
                  have p24291_2 := h24291c.2.2.1
                  have p24291_3 := h24291c.2.2.2
                  rcases p24291_3 (m.d 0 2) (by simp) with h24328 | h24328
                  · linarith only [h19744, h24328, hlam]
                  · linarith only [h0, h24328, hlam]
                · have p24291_0 := h24291c.1
                  have p24291_1 := h24291c.2.1
                  have p24291_2 := h24291c.2.2.1
                  have p24291_3 := h24291c.2.2.2
                  linarith only [h23945, hlam, p24291_0]
                · have p24291_0 := h24291c.1
                  have p24291_1 := h24291c.2.1
                  have p24291_2 := h24291c.2.2.1
                  have p24291_3 := h24291c.2.2.2
                  linarith only [hlam, p24291_0]
                · have p24291_0 := h24291c.1
                  have p24291_1 := h24291c.2.1
                  have p24291_2 := h24291c.2.2.1
                  have p24291_3 := h24291c.2.2.2
                  linarith only [h0, h22010, hc12, hc24, hlam, hphi, p24291_1]
                · have p24291_0 := h24291c.1
                  have p24291_1 := h24291c.2.1
                  have p24291_2 := h24291c.2.2.1
                  have p24291_3 := h24291c.2.2.2
                  rcases p24291_3 (m.d 0 2) (by simp) with h24334 | h24334
                  · linarith only [h24334, hlam, p24291_0]
                  · rcases p24291_3 (m.d 1 2) (by simp) with h24336 | h24336
                    · linarith only [h23344, h24336, hlam]
                    · rcases p24291_3 (m.d 2 3) (by simp) with h24338 | h24338
                      · rcases p24291_3 (m.d 2 4) (by simp) with h24339 | h24339
                        · rcases p24291_3 (m.d 2 5) (by simp) with h24340 | h24340
                          · rcases h4bigk with h24341c | h24341c | h24341c | h24341c | h24341c | h24341c | h24341c | h24341c | h24341c | h24341c | h24341c | h24341c | h24341c | h24341c | h24341c | h24341c | h24341c | h24341c | h24341c | h24341c | h24341c | h24341c | h24341c | h24341c | h24341c
                            · have p24341_0 := h24341c.1
                              have p24341_1 := h24341c.2.1
                              have p24341_2 := h24341c.2.2.1
                              have p24341_3 := h24341c.2.2.2
                              linarith only [hlam, p24341_0]
                            · have p24341_0 := h24341c.1
                              have p24341_1 := h24341c.2.1
                              have p24341_2 := h24341c.2.2.1
                              have p24341_3 := h24341c.2.2.2
                              rcases p24341_3 (m.d 0 4) (by simp) with h24343 | h24343
                              · rcases p24341_3 (m.d 1 4) (by simp) with h24344 | h24344
                                · linarith only [h2, h24344, hlam]
                                · rcases p24341_3 (m.d 2 4) (by simp) with h24346 | h24346
                                  · rcases p24341_3 (m.d 3 4) (by simp) with h24347 | h24347
                                    · linarith only [h23337, h24347, hlam]
                                    · rcases p24341_3 (m.d 4 5) (by simp) with h24349 | h24349
                                      · linarith only [h23339, h24349, hlam]
                                      · linarith only [h23348, h24349, hlam]
                                  · linarith only [h23342, h24346, hlam]
                              · linarith only [h2, h24343, hlam]
                            · have p24341_0 := h24341c.1
                              have p24341_1 := h24341c.2.1
                              have p24341_2 := h24341c.2.2.1
                              have p24341_3 := h24341c.2.2.2
                              linarith only [h19744, hlam, p24341_1]
                            · have p24341_0 := h24341c.1
                              have p24341_1 := h24341c.2.1
                              have p24341_2 := h24341c.2.2.1
                              have p24341_3 := h24341c.2.2.2
                              rcases p24341_3 (m.d 0 4) (by simp) with h24355 | h24355
                              · rcases p24341_3 (m.d 1 4) (by simp) with h24356 | h24356
                                · linarith only [h2, h24356, hlam]
                                · linarith only [h23346, h24356, hlam]
                              · linarith only [h23337, h24355, hlam]
                            · have p24341_0 := h24341c.1
                              have p24341_1 := h24341c.2.1
                              have p24341_2 := h24341c.2.2.1
                              have p24341_3 := h24341c.2.2.2
                              linarith only [h19744, h23342, h23348, h23945, hc12, hc23, hlam, hphi, p24341_1]
                            · have p24341_0 := h24341c.1
                              have p24341_1 := h24341c.2.1
                              have p24341_2 := h24341c.2.2.1
                              have p24341_3 := h24341c.2.2.2
                              linarith only [h2, hlam, p24341_0]
                            · have p24341_0 := h24341c.1
                              have p24341_1 := h24341c.2.1
                              have p24341_2 := h24341c.2.2.1
                              have p24341_3 := h24341c.2.2.2
                              linarith only [hlam, p24341_0]
                            · have p24341_0 := h24341c.1
                              have p24341_1 := h24341c.2.1
                              have p24341_2 := h24341c.2.2.1
                              have p24341_3 := h24341c.2.2.2
                              linarith only [h23342, hlam, p24341_1]
                            · have p24341_0 := h24341c.1
                              have p24341_1 := h24341c.2.1
                              have p24341_2 := h24341c.2.2.1
                              have p24341_3 := h24341c.2.2.2
                              linarith only [h23348, hc34, hc45, hlam, hphi, p24341_1]
                            · have p24341_0 := h24341c.1
                              have p24341_1 := h24341c.2.1
                              have p24341_2 := h24341c.2.2.1
                              have p24341_3 := h24341c.2.2.2
                              linarith only [h23348, hlam, p24341_0]
                            · have p24341_0 := h24341c.1
                              have p24341_1 := h24341c.2.1
                              have p24341_2 := h24341c.2.2.1
                              have p24341_3 := h24341c.2.2.2
                              linarith only [h23339, h23348, h23945, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p24341_1]
                            · have p24341_0 := h24341c.1
                              have p24341_1 := h24341c.2.1
                              have p24341_2 := h24341c.2.2.1
                              have p24341_3 := h24341c.2.2.2
                              rcases p24341_3 (m.d 0 4) (by simp) with h24367 | h24367
                              · linarith only [h19744, h24367, hlam]
                              · linarith only [h2, h24367, hlam]
                            · have p24341_0 := h24341c.1
                              have p24341_1 := h24341c.2.1
                              have p24341_2 := h24341c.2.2.1
                              have p24341_3 := h24341c.2.2.2
                              linarith only [hlam, p24341_0]
                            · have p24341_0 := h24341c.1
                              have p24341_1 := h24341c.2.1
                              have p24341_2 := h24341c.2.2.1
                              have p24341_3 := h24341c.2.2.2
                              rcases p24341_3 (m.d 0 4) (by simp) with h24371 | h24371
                              · linarith only [h19744, h24371, hlam]
                              · linarith only [h23337, h24371, hlam]
                            · have p24341_0 := h24341c.1
                              have p24341_1 := h24341c.2.1
                              have p24341_2 := h24341c.2.2.1
                              have p24341_3 := h24341c.2.2.2
                              linarith only [h23342, h23348, hc12, hc24, hlam, hphi, p24341_1]
                            · have p24341_0 := h24341c.1
                              have p24341_1 := h24341c.2.1
                              have p24341_2 := h24341c.2.2.1
                              have p24341_3 := h24341c.2.2.2
                              linarith only [h23337, hlam, p24341_0]
                            · have p24341_0 := h24341c.1
                              have p24341_1 := h24341c.2.1
                              have p24341_2 := h24341c.2.2.1
                              have p24341_3 := h24341c.2.2.2
                              linarith only [h23346, hlam, p24341_0]
                            · have p24341_0 := h24341c.1
                              have p24341_1 := h24341c.2.1
                              have p24341_2 := h24341c.2.2.1
                              have p24341_3 := h24341c.2.2.2
                              linarith only [h23945, hlam, p24341_0]
                            · have p24341_0 := h24341c.1
                              have p24341_1 := h24341c.2.1
                              have p24341_2 := h24341c.2.2.1
                              have p24341_3 := h24341c.2.2.2
                              linarith only [hlam, p24341_0]
                            · have p24341_0 := h24341c.1
                              have p24341_1 := h24341c.2.1
                              have p24341_2 := h24341c.2.2.1
                              have p24341_3 := h24341c.2.2.2
                              linarith only [h23948, hlam, p24341_0]
                            · have p24341_0 := h24341c.1
                              have p24341_1 := h24341c.2.1
                              have p24341_2 := h24341c.2.2.1
                              have p24341_3 := h24341c.2.2.2
                              linarith only [h23339, hlam, p24341_0]
                            · have p24341_0 := h24341c.1
                              have p24341_1 := h24341c.2.1
                              have p24341_2 := h24341c.2.2.1
                              have p24341_3 := h24341c.2.2.2
                              linarith only [h23337, h23339, h23342, h4, hc12, hc23, hlam, hphi, p24341_1]
                            · have p24341_0 := h24341c.1
                              have p24341_1 := h24341c.2.1
                              have p24341_2 := h24341c.2.2.1
                              have p24341_3 := h24341c.2.2.2
                              linarith only [h23947, hlam, p24341_0]
                            · have p24341_0 := h24341c.1
                              have p24341_1 := h24341c.2.1
                              have p24341_2 := h24341c.2.2.1
                              have p24341_3 := h24341c.2.2.2
                              rcases p24341_3 (m.d 0 4) (by simp) with h24383 | h24383
                              · rcases p24341_3 (m.d 1 4) (by simp) with h24384 | h24384
                                · linarith only [h23348, h24384, hlam]
                                · linarith only [h23346, h24384, hlam]
                              · linarith only [h23337, h24383, hlam]
                            · have p24341_0 := h24341c.1
                              have p24341_1 := h24341c.2.1
                              have p24341_2 := h24341c.2.2.1
                              have p24341_3 := h24341c.2.2.2
                              linarith only [hlam, p24341_0]
                          · linarith only [h24340, hlam, p24291_0]
                        · linarith only [h19744, h24339, hlam]
                      · linarith only [h24338, h4, hlam]
                · have p24291_0 := h24291c.1
                  have p24291_1 := h24291c.2.1
                  have p24291_2 := h24291c.2.2.1
                  have p24291_3 := h24291c.2.2.2
                  rcases p24291_3 (m.d 0 2) (by simp) with h24392 | h24392
                  · linarith only [h22010, h24392, hlam]
                  · linarith only [h0, h24392, hlam]
                · have p24291_0 := h24291c.1
                  have p24291_1 := h24291c.2.1
                  have p24291_2 := h24291c.2.2.1
                  have p24291_3 := h24291c.2.2.2
                  linarith only [h23946, hlam, p24291_0]
                · have p24291_0 := h24291c.1
                  have p24291_1 := h24291c.2.1
                  have p24291_2 := h24291c.2.2.1
                  have p24291_3 := h24291c.2.2.2
                  linarith only [h23947, hlam, p24291_1]
                · have p24291_0 := h24291c.1
                  have p24291_1 := h24291c.2.1
                  have p24291_2 := h24291c.2.2.1
                  have p24291_3 := h24291c.2.2.2
                  linarith only [hlam, p24291_0]
    · linarith only [h23959, hlam, p23950_0]
  · have p23950_0 := h23950c.1
    have p23950_1 := h23950c.2.1
    have p23950_2 := h23950c.2.2.1
    have p23950_3 := h23950c.2.2.2
    rcases p23950_3 (m.d 0 1) (by simp) with h24399 | h24399
    · rcases p23950_3 (m.d 1 2) (by simp) with h24400 | h24400
      · linarith only [h0, h24400, hlam]
      · rcases p23950_3 (m.d 1 3) (by simp) with h24402 | h24402
        · linarith only [h1, h24402, hlam]
        · linarith only [h23346, h24402, hlam]
    · linarith only [h24399, hlam, p23950_0]
  · have p23950_0 := h23950c.1
    have p23950_1 := h23950c.2.1
    have p23950_2 := h23950c.2.2.1
    have p23950_3 := h23950c.2.2.2
    rcases p23950_3 (m.d 0 1) (by simp) with h24406 | h24406
    · rcases p23950_3 (m.d 1 2) (by simp) with h24407 | h24407
      · linarith only [h0, h24407, hlam]
      · rcases p23950_3 (m.d 1 3) (by simp) with h24409 | h24409
        · linarith only [h1, h24409, hlam]
        · linarith only [h23347, h24409, hlam]
    · linarith only [h24406, hlam, p23950_0]
  · have p23950_0 := h23950c.1
    have p23950_1 := h23950c.2.1
    have p23950_2 := h23950c.2.2.1
    have p23950_3 := h23950c.2.2.2
    linarith only [h0, hlam, p23950_0]
  · have p23950_0 := h23950c.1
    have p23950_1 := h23950c.2.1
    have p23950_2 := h23950c.2.2.1
    have p23950_3 := h23950c.2.2.2
    linarith only [hlam, p23950_0]
  · have p23950_0 := h23950c.1
    have p23950_1 := h23950c.2.1
    have p23950_2 := h23950c.2.2.1
    have p23950_3 := h23950c.2.2.2
    linarith only [h23340, hlam, p23950_1]
  · have p23950_0 := h23950c.1
    have p23950_1 := h23950c.2.1
    have p23950_2 := h23950c.2.2.1
    have p23950_3 := h23950c.2.2.2
    linarith only [h23342, hlam, p23950_1]
  · have p23950_0 := h23950c.1
    have p23950_1 := h23950c.2.1
    have p23950_2 := h23950c.2.2.1
    have p23950_3 := h23950c.2.2.2
    linarith only [h23344, hlam, p23950_1]
  · have p23950_0 := h23950c.1
    have p23950_1 := h23950c.2.1
    have p23950_2 := h23950c.2.2.1
    have p23950_3 := h23950c.2.2.2
    linarith only [h1, hlam, p23950_0]
  · have p23950_0 := h23950c.1
    have p23950_1 := h23950c.2.1
    have p23950_2 := h23950c.2.2.1
    have p23950_3 := h23950c.2.2.2
    rcases p23950_3 (m.d 0 1) (by simp) with h24419 | h24419
    · rcases p23950_3 (m.d 1 2) (by simp) with h24420 | h24420
      · linarith only [h23340, h24420, hlam]
      · rcases p23950_3 (m.d 1 3) (by simp) with h24422 | h24422
        · rcases p23950_3 (m.d 1 4) (by simp) with h24423 | h24423
          · linarith only [h23346, h24423, hlam]
          · linarith only [h23342, h24423, hlam]
        · linarith only [h23340, h24422, hlam]
    · linarith only [h0, h24419, hlam]
  · have p23950_0 := h23950c.1
    have p23950_1 := h23950c.2.1
    have p23950_2 := h23950c.2.2.1
    have p23950_3 := h23950c.2.2.2
    linarith only [hlam, p23950_0]
  · have p23950_0 := h23950c.1
    have p23950_1 := h23950c.2.1
    have p23950_2 := h23950c.2.2.1
    have p23950_3 := h23950c.2.2.2
    rcases p23950_3 (m.d 0 1) (by simp) with h24429 | h24429
    · rcases p23950_3 (m.d 1 2) (by simp) with h24430 | h24430
      · linarith only [h23340, h24430, hlam]
      · rcases p23950_3 (m.d 1 3) (by simp) with h24432 | h24432
        · rcases p23950_3 (m.d 1 4) (by simp) with h24433 | h24433
          · linarith only [h23346, h24433, hlam]
          · rcases p23950_3 (m.d 1 5) (by simp) with h24435 | h24435
            · linarith only [h23347, h24435, hlam]
            · linarith only [h23348, h24435, hlam]
        · linarith only [h23346, h24432, hlam]
    · linarith only [h2, h24429, hlam]
  · have p23950_0 := h23950c.1
    have p23950_1 := h23950c.2.1
    have p23950_2 := h23950c.2.2.1
    have p23950_3 := h23950c.2.2.2
    rcases p23950_3 (m.d 0 1) (by simp) with h24440 | h24440
    · rcases p23950_3 (m.d 1 2) (by simp) with h24441 | h24441
      · linarith only [h23340, h24441, hlam]
      · rcases p23950_3 (m.d 1 3) (by simp) with h24443 | h24443
        · rcases p23950_3 (m.d 1 4) (by simp) with h24444 | h24444
          · linarith only [h23346, h24444, hlam]
          · rcases p23950_3 (m.d 1 5) (by simp) with h24446 | h24446
            · linarith only [h23347, h24446, hlam]
            · rcases h1emax with h24448 | h24448 | h24448 | h24448 | h24448
              · linarith only [h1, h23342, h23348, h24448, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p23950_1]
              · rcases h2bigk with h24450c | h24450c | h24450c | h24450c | h24450c | h24450c | h24450c | h24450c | h24450c | h24450c | h24450c | h24450c | h24450c | h24450c | h24450c | h24450c | h24450c | h24450c | h24450c | h24450c | h24450c | h24450c | h24450c | h24450c | h24450c
                · have p24450_0 := h24450c.1
                  have p24450_1 := h24450c.2.1
                  have p24450_2 := h24450c.2.2.1
                  have p24450_3 := h24450c.2.2.2
                  linarith only [hlam, p24450_0]
                · have p24450_0 := h24450c.1
                  have p24450_1 := h24450c.2.1
                  have p24450_2 := h24450c.2.2.1
                  have p24450_3 := h24450c.2.2.2
                  linarith only [h4, hc12, hc23, hlam, hphi, p24450_1]
                · have p24450_0 := h24450c.1
                  have p24450_1 := h24450c.2.1
                  have p24450_2 := h24450c.2.2.1
                  have p24450_3 := h24450c.2.2.2
                  linarith only [h4, hlam, p24450_0]
                · have p24450_0 := h24450c.1
                  have p24450_1 := h24450c.2.1
                  have p24450_2 := h24450c.2.2.1
                  have p24450_3 := h24450c.2.2.2
                  linarith only [h19744, hlam, p24450_0]
                · have p24450_0 := h24450c.1
                  have p24450_1 := h24450c.2.1
                  have p24450_2 := h24450c.2.2.1
                  have p24450_3 := h24450c.2.2.2
                  linarith only [h22010, hlam, p24450_0]
                · have p24450_0 := h24450c.1
                  have p24450_1 := h24450c.2.1
                  have p24450_2 := h24450c.2.2.1
                  have p24450_3 := h24450c.2.2.2
                  linarith only [h0, hlam, p24450_1]
                · have p24450_0 := h24450c.1
                  have p24450_1 := h24450c.2.1
                  have p24450_2 := h24450c.2.2.1
                  have p24450_3 := h24450c.2.2.2
                  linarith only [hlam, p24450_0]
                · have p24450_0 := h24450c.1
                  have p24450_1 := h24450c.2.1
                  have p24450_2 := h24450c.2.2.1
                  have p24450_3 := h24450c.2.2.2
                  linarith only [h23340, hlam, p24450_0]
                · have p24450_0 := h24450c.1
                  have p24450_1 := h24450c.2.1
                  have p24450_2 := h24450c.2.2.1
                  have p24450_3 := h24450c.2.2.2
                  linarith only [h23342, hlam, p24450_0]
                · have p24450_0 := h24450c.1
                  have p24450_1 := h24450c.2.1
                  have p24450_2 := h24450c.2.2.1
                  have p24450_3 := h24450c.2.2.2
                  linarith only [h23344, hlam, p24450_0]
                · have p24450_0 := h24450c.1
                  have p24450_1 := h24450c.2.1
                  have p24450_2 := h24450c.2.2.1
                  have p24450_3 := h24450c.2.2.2
                  rcases p24450_3 (m.d 0 2) (by simp) with h24461 | h24461
                  · linarith only [h24461, hlam, p24450_0]
                  · rcases p24450_3 (m.d 1 2) (by simp) with h24463 | h24463
                    · linarith only [h23340, h24463, hlam]
                    · rcases p24450_3 (m.d 2 3) (by simp) with h24465 | h24465
                      · rcases p24450_3 (m.d 2 4) (by simp) with h24466 | h24466
                        · linarith only [h23945, h24466, hlam]
                        · linarith only [h19744, h24466, hlam]
                      · linarith only [h24465, hlam, p24450_0]
                · have p24450_0 := h24450c.1
                  have p24450_1 := h24450c.2.1
                  have p24450_2 := h24450c.2.2.1
                  have p24450_3 := h24450c.2.2.2
                  rcases p24450_3 (m.d 0 2) (by simp) with h24470 | h24470
                  · linarith only [h24470, h4, hlam]
                  · linarith only [h0, h24470, hlam]
                · have p24450_0 := h24450c.1
                  have p24450_1 := h24450c.2.1
                  have p24450_2 := h24450c.2.2.1
                  have p24450_3 := h24450c.2.2.2
                  linarith only [hlam, p24450_0]
                · have p24450_0 := h24450c.1
                  have p24450_1 := h24450c.2.1
                  have p24450_2 := h24450c.2.2.1
                  have p24450_3 := h24450c.2.2.2
                  linarith only [h19744, hc02, hc23, hlam, hphi, p24450_1]
                · have p24450_0 := h24450c.1
                  have p24450_1 := h24450c.2.1
                  have p24450_2 := h24450c.2.2.1
                  have p24450_3 := h24450c.2.2.2
                  linarith only [h0, h22010, hc12, hc23, hlam, hphi, p24450_1]
                · have p24450_0 := h24450c.1
                  have p24450_1 := h24450c.2.1
                  have p24450_2 := h24450c.2.2.1
                  have p24450_3 := h24450c.2.2.2
                  rcases p24450_3 (m.d 0 2) (by simp) with h24476 | h24476
                  · linarith only [h24476, hlam, p24450_0]
                  · rcases p24450_3 (m.d 1 2) (by simp) with h24478 | h24478
                    · linarith only [h23342, h24478, hlam]
                    · rcases p24450_3 (m.d 2 3) (by simp) with h24480 | h24480
                      · rcases p24450_3 (m.d 2 4) (by simp) with h24481 | h24481
                        · rcases p24450_3 (m.d 2 5) (by simp) with h24482 | h24482
                          · linarith only [h23947, h24482, hlam]
                          · linarith only [h22010, h24482, hlam]
                        · linarith only [h24481, hlam, p24450_0]
                      · linarith only [h24480, h4, hlam]
                · have p24450_0 := h24450c.1
                  have p24450_1 := h24450c.2.1
                  have p24450_2 := h24450c.2.2.1
                  have p24450_3 := h24450c.2.2.2
                  rcases p24450_3 (m.d 0 2) (by simp) with h24487 | h24487
                  · linarith only [h19744, h24487, hlam]
                  · linarith only [h0, h24487, hlam]
                · have p24450_0 := h24450c.1
                  have p24450_1 := h24450c.2.1
                  have p24450_2 := h24450c.2.2.1
                  have p24450_3 := h24450c.2.2.2
                  linarith only [h23945, hlam, p24450_0]
                · have p24450_0 := h24450c.1
                  have p24450_1 := h24450c.2.1
                  have p24450_2 := h24450c.2.2.1
                  have p24450_3 := h24450c.2.2.2
                  linarith only [hlam, p24450_0]
                · have p24450_0 := h24450c.1
                  have p24450_1 := h24450c.2.1
                  have p24450_2 := h24450c.2.2.1
                  have p24450_3 := h24450c.2.2.2
                  linarith only [h0, h22010, hc12, hc24, hlam, hphi, p24450_1]
                · have p24450_0 := h24450c.1
                  have p24450_1 := h24450c.2.1
                  have p24450_2 := h24450c.2.2.1
                  have p24450_3 := h24450c.2.2.2
                  rcases p24450_3 (m.d 0 2) (by simp) with h24493 | h24493
                  · linarith only [h24493, hlam, p24450_0]
                  · rcases p24450_3 (m.d 1 2) (by simp) with h24495 | h24495
                    · linarith only [h23344, h24495, hlam]
                    · rcases p24450_3 (m.d 2 3) (by simp) with h24497 | h24497
                      · rcases p24450_3 (m.d 2 4) (by simp) with h24498 | h24498
                        · rcases p24450_3 (m.d 2 5) (by simp) with h24499 | h24499
                          · rcases h4bigk with h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c | h24500c
                            · have p24500_0 := h24500c.1
                              have p24500_1 := h24500c.2.1
                              have p24500_2 := h24500c.2.2.1
                              have p24500_3 := h24500c.2.2.2
                              linarith only [hlam, p24500_0]
                            · have p24500_0 := h24500c.1
                              have p24500_1 := h24500c.2.1
                              have p24500_2 := h24500c.2.2.1
                              have p24500_3 := h24500c.2.2.2
                              rcases p24500_3 (m.d 0 4) (by simp) with h24502 | h24502
                              · rcases p24500_3 (m.d 1 4) (by simp) with h24503 | h24503
                                · linarith only [h2, h24503, hlam]
                                · rcases p24500_3 (m.d 2 4) (by simp) with h24505 | h24505
                                  · rcases p24500_3 (m.d 3 4) (by simp) with h24506 | h24506
                                    · linarith only [h23337, h24506, hlam]
                                    · rcases p24500_3 (m.d 4 5) (by simp) with h24508 | h24508
                                      · linarith only [h23339, h24508, hlam]
                                      · linarith only [h23348, h24508, hlam]
                                  · linarith only [h23342, h24505, hlam]
                              · linarith only [h2, h24502, hlam]
                            · have p24500_0 := h24500c.1
                              have p24500_1 := h24500c.2.1
                              have p24500_2 := h24500c.2.2.1
                              have p24500_3 := h24500c.2.2.2
                              linarith only [h19744, hlam, p24500_1]
                            · have p24500_0 := h24500c.1
                              have p24500_1 := h24500c.2.1
                              have p24500_2 := h24500c.2.2.1
                              have p24500_3 := h24500c.2.2.2
                              rcases p24500_3 (m.d 0 4) (by simp) with h24514 | h24514
                              · rcases p24500_3 (m.d 1 4) (by simp) with h24515 | h24515
                                · linarith only [h2, h24515, hlam]
                                · linarith only [h23346, h24515, hlam]
                              · linarith only [h23337, h24514, hlam]
                            · have p24500_0 := h24500c.1
                              have p24500_1 := h24500c.2.1
                              have p24500_2 := h24500c.2.2.1
                              have p24500_3 := h24500c.2.2.2
                              linarith only [h23337, h23342, h23348, h4, hc12, hc23, hlam, hphi, p24500_1]
                            · have p24500_0 := h24500c.1
                              have p24500_1 := h24500c.2.1
                              have p24500_2 := h24500c.2.2.1
                              have p24500_3 := h24500c.2.2.2
                              linarith only [h2, hlam, p24500_0]
                            · have p24500_0 := h24500c.1
                              have p24500_1 := h24500c.2.1
                              have p24500_2 := h24500c.2.2.1
                              have p24500_3 := h24500c.2.2.2
                              linarith only [hlam, p24500_0]
                            · have p24500_0 := h24500c.1
                              have p24500_1 := h24500c.2.1
                              have p24500_2 := h24500c.2.2.1
                              have p24500_3 := h24500c.2.2.2
                              linarith only [h23342, hlam, p24500_1]
                            · have p24500_0 := h24500c.1
                              have p24500_1 := h24500c.2.1
                              have p24500_2 := h24500c.2.2.1
                              have p24500_3 := h24500c.2.2.2
                              linarith only [h23348, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23950_1, p24500_1]
                            · have p24500_0 := h24500c.1
                              have p24500_1 := h24500c.2.1
                              have p24500_2 := h24500c.2.2.1
                              have p24500_3 := h24500c.2.2.2
                              linarith only [h23348, hlam, p24500_0]
                            · have p24500_0 := h24500c.1
                              have p24500_1 := h24500c.2.1
                              have p24500_2 := h24500c.2.2.1
                              have p24500_3 := h24500c.2.2.2
                              linarith only [h23339, h23348, h23945, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p24500_1]
                            · have p24500_0 := h24500c.1
                              have p24500_1 := h24500c.2.1
                              have p24500_2 := h24500c.2.2.1
                              have p24500_3 := h24500c.2.2.2
                              rcases p24500_3 (m.d 0 4) (by simp) with h24526 | h24526
                              · linarith only [h19744, h24526, hlam]
                              · linarith only [h2, h24526, hlam]
                            · have p24500_0 := h24500c.1
                              have p24500_1 := h24500c.2.1
                              have p24500_2 := h24500c.2.2.1
                              have p24500_3 := h24500c.2.2.2
                              linarith only [hlam, p24500_0]
                            · have p24500_0 := h24500c.1
                              have p24500_1 := h24500c.2.1
                              have p24500_2 := h24500c.2.2.1
                              have p24500_3 := h24500c.2.2.2
                              rcases p24500_3 (m.d 0 4) (by simp) with h24530 | h24530
                              · linarith only [h19744, h24530, hlam]
                              · linarith only [h23337, h24530, hlam]
                            · have p24500_0 := h24500c.1
                              have p24500_1 := h24500c.2.1
                              have p24500_2 := h24500c.2.2.1
                              have p24500_3 := h24500c.2.2.2
                              linarith only [h23342, h23348, hc12, hc24, hlam, hphi, p24500_1]
                            · have p24500_0 := h24500c.1
                              have p24500_1 := h24500c.2.1
                              have p24500_2 := h24500c.2.2.1
                              have p24500_3 := h24500c.2.2.2
                              linarith only [h23337, hlam, p24500_0]
                            · have p24500_0 := h24500c.1
                              have p24500_1 := h24500c.2.1
                              have p24500_2 := h24500c.2.2.1
                              have p24500_3 := h24500c.2.2.2
                              linarith only [h23346, hlam, p24500_0]
                            · have p24500_0 := h24500c.1
                              have p24500_1 := h24500c.2.1
                              have p24500_2 := h24500c.2.2.1
                              have p24500_3 := h24500c.2.2.2
                              linarith only [h23945, hlam, p24500_0]
                            · have p24500_0 := h24500c.1
                              have p24500_1 := h24500c.2.1
                              have p24500_2 := h24500c.2.2.1
                              have p24500_3 := h24500c.2.2.2
                              linarith only [hlam, p24500_0]
                            · have p24500_0 := h24500c.1
                              have p24500_1 := h24500c.2.1
                              have p24500_2 := h24500c.2.2.1
                              have p24500_3 := h24500c.2.2.2
                              linarith only [h23948, hlam, p24500_0]
                            · have p24500_0 := h24500c.1
                              have p24500_1 := h24500c.2.1
                              have p24500_2 := h24500c.2.2.1
                              have p24500_3 := h24500c.2.2.2
                              linarith only [h23339, hlam, p24500_0]
                            · have p24500_0 := h24500c.1
                              have p24500_1 := h24500c.2.1
                              have p24500_2 := h24500c.2.2.1
                              have p24500_3 := h24500c.2.2.2
                              linarith only [h19744, h23339, h23342, hc12, hc24, hlam, hphi, p24500_1]
                            · have p24500_0 := h24500c.1
                              have p24500_1 := h24500c.2.1
                              have p24500_2 := h24500c.2.2.1
                              have p24500_3 := h24500c.2.2.2
                              linarith only [h23947, hlam, p24500_0]
                            · have p24500_0 := h24500c.1
                              have p24500_1 := h24500c.2.1
                              have p24500_2 := h24500c.2.2.1
                              have p24500_3 := h24500c.2.2.2
                              rcases p24500_3 (m.d 0 4) (by simp) with h24542 | h24542
                              · rcases p24500_3 (m.d 1 4) (by simp) with h24543 | h24543
                                · linarith only [h23348, h24543, hlam]
                                · linarith only [h23346, h24543, hlam]
                              · linarith only [h23337, h24542, hlam]
                            · have p24500_0 := h24500c.1
                              have p24500_1 := h24500c.2.1
                              have p24500_2 := h24500c.2.2.1
                              have p24500_3 := h24500c.2.2.2
                              linarith only [hlam, p24500_0]
                          · linarith only [h24499, hlam, p24450_0]
                        · linarith only [h19744, h24498, hlam]
                      · linarith only [h24497, h4, hlam]
                · have p24450_0 := h24450c.1
                  have p24450_1 := h24450c.2.1
                  have p24450_2 := h24450c.2.2.1
                  have p24450_3 := h24450c.2.2.2
                  rcases p24450_3 (m.d 0 2) (by simp) with h24551 | h24551
                  · linarith only [h22010, h24551, hlam]
                  · linarith only [h0, h24551, hlam]
                · have p24450_0 := h24450c.1
                  have p24450_1 := h24450c.2.1
                  have p24450_2 := h24450c.2.2.1
                  have p24450_3 := h24450c.2.2.2
                  linarith only [h23946, hlam, p24450_0]
                · have p24450_0 := h24450c.1
                  have p24450_1 := h24450c.2.1
                  have p24450_2 := h24450c.2.2.1
                  have p24450_3 := h24450c.2.2.2
                  linarith only [h23947, hlam, p24450_1]
                · have p24450_0 := h24450c.1
                  have p24450_1 := h24450c.2.1
                  have p24450_2 := h24450c.2.2.1
                  have p24450_3 := h24450c.2.2.2
                  linarith only [hlam, p24450_0]
              · linarith only [h23342, h23348, h24448, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p23950_1]
              · rcases h2bigk with h24558c | h24558c | h24558c | h24558c | h24558c | h24558c | h24558c | h24558c | h24558c | h24558c | h24558c | h24558c | h24558c | h24558c | h24558c | h24558c | h24558c | h24558c | h24558c | h24558c | h24558c | h24558c | h24558c | h24558c | h24558c
                · have p24558_0 := h24558c.1
                  have p24558_1 := h24558c.2.1
                  have p24558_2 := h24558c.2.2.1
                  have p24558_3 := h24558c.2.2.2
                  linarith only [hlam, p24558_0]
                · have p24558_0 := h24558c.1
                  have p24558_1 := h24558c.2.1
                  have p24558_2 := h24558c.2.2.1
                  have p24558_3 := h24558c.2.2.2
                  linarith only [h4, hc12, hc23, hlam, hphi, p24558_1]
                · have p24558_0 := h24558c.1
                  have p24558_1 := h24558c.2.1
                  have p24558_2 := h24558c.2.2.1
                  have p24558_3 := h24558c.2.2.2
                  linarith only [h4, hlam, p24558_0]
                · have p24558_0 := h24558c.1
                  have p24558_1 := h24558c.2.1
                  have p24558_2 := h24558c.2.2.1
                  have p24558_3 := h24558c.2.2.2
                  linarith only [h19744, hlam, p24558_0]
                · have p24558_0 := h24558c.1
                  have p24558_1 := h24558c.2.1
                  have p24558_2 := h24558c.2.2.1
                  have p24558_3 := h24558c.2.2.2
                  linarith only [h22010, hlam, p24558_0]
                · have p24558_0 := h24558c.1
                  have p24558_1 := h24558c.2.1
                  have p24558_2 := h24558c.2.2.1
                  have p24558_3 := h24558c.2.2.2
                  linarith only [h0, hlam, p24558_1]
                · have p24558_0 := h24558c.1
                  have p24558_1 := h24558c.2.1
                  have p24558_2 := h24558c.2.2.1
                  have p24558_3 := h24558c.2.2.2
                  linarith only [hlam, p24558_0]
                · have p24558_0 := h24558c.1
                  have p24558_1 := h24558c.2.1
                  have p24558_2 := h24558c.2.2.1
                  have p24558_3 := h24558c.2.2.2
                  linarith only [h23340, hlam, p24558_0]
                · have p24558_0 := h24558c.1
                  have p24558_1 := h24558c.2.1
                  have p24558_2 := h24558c.2.2.1
                  have p24558_3 := h24558c.2.2.2
                  linarith only [h23342, hlam, p24558_0]
                · have p24558_0 := h24558c.1
                  have p24558_1 := h24558c.2.1
                  have p24558_2 := h24558c.2.2.1
                  have p24558_3 := h24558c.2.2.2
                  linarith only [h23344, hlam, p24558_0]
                · have p24558_0 := h24558c.1
                  have p24558_1 := h24558c.2.1
                  have p24558_2 := h24558c.2.2.1
                  have p24558_3 := h24558c.2.2.2
                  rcases p24558_3 (m.d 0 2) (by simp) with h24569 | h24569
                  · linarith only [h24569, hlam, p24558_0]
                  · rcases p24558_3 (m.d 1 2) (by simp) with h24571 | h24571
                    · linarith only [h23340, h24571, hlam]
                    · rcases p24558_3 (m.d 2 3) (by simp) with h24573 | h24573
                      · rcases p24558_3 (m.d 2 4) (by simp) with h24574 | h24574
                        · linarith only [h23945, h24574, hlam]
                        · linarith only [h19744, h24574, hlam]
                      · linarith only [h24573, hlam, p24558_0]
                · have p24558_0 := h24558c.1
                  have p24558_1 := h24558c.2.1
                  have p24558_2 := h24558c.2.2.1
                  have p24558_3 := h24558c.2.2.2
                  rcases p24558_3 (m.d 0 2) (by simp) with h24578 | h24578
                  · linarith only [h24578, h4, hlam]
                  · linarith only [h0, h24578, hlam]
                · have p24558_0 := h24558c.1
                  have p24558_1 := h24558c.2.1
                  have p24558_2 := h24558c.2.2.1
                  have p24558_3 := h24558c.2.2.2
                  linarith only [hlam, p24558_0]
                · have p24558_0 := h24558c.1
                  have p24558_1 := h24558c.2.1
                  have p24558_2 := h24558c.2.2.1
                  have p24558_3 := h24558c.2.2.2
                  linarith only [h19744, hc02, hc23, hlam, hphi, p24558_1]
                · have p24558_0 := h24558c.1
                  have p24558_1 := h24558c.2.1
                  have p24558_2 := h24558c.2.2.1
                  have p24558_3 := h24558c.2.2.2
                  linarith only [h0, h22010, hc12, hc23, hlam, hphi, p24558_1]
                · have p24558_0 := h24558c.1
                  have p24558_1 := h24558c.2.1
                  have p24558_2 := h24558c.2.2.1
                  have p24558_3 := h24558c.2.2.2
                  rcases p24558_3 (m.d 0 2) (by simp) with h24584 | h24584
                  · linarith only [h24584, hlam, p24558_0]
                  · rcases p24558_3 (m.d 1 2) (by simp) with h24586 | h24586
                    · linarith only [h23342, h24586, hlam]
                    · rcases p24558_3 (m.d 2 3) (by simp) with h24588 | h24588
                      · rcases p24558_3 (m.d 2 4) (by simp) with h24589 | h24589
                        · rcases p24558_3 (m.d 2 5) (by simp) with h24590 | h24590
                          · linarith only [h23947, h24590, hlam]
                          · linarith only [h22010, h24590, hlam]
                        · linarith only [h24589, hlam, p24558_0]
                      · linarith only [h24588, h4, hlam]
                · have p24558_0 := h24558c.1
                  have p24558_1 := h24558c.2.1
                  have p24558_2 := h24558c.2.2.1
                  have p24558_3 := h24558c.2.2.2
                  rcases p24558_3 (m.d 0 2) (by simp) with h24595 | h24595
                  · linarith only [h19744, h24595, hlam]
                  · linarith only [h0, h24595, hlam]
                · have p24558_0 := h24558c.1
                  have p24558_1 := h24558c.2.1
                  have p24558_2 := h24558c.2.2.1
                  have p24558_3 := h24558c.2.2.2
                  linarith only [h23945, hlam, p24558_0]
                · have p24558_0 := h24558c.1
                  have p24558_1 := h24558c.2.1
                  have p24558_2 := h24558c.2.2.1
                  have p24558_3 := h24558c.2.2.2
                  linarith only [hlam, p24558_0]
                · have p24558_0 := h24558c.1
                  have p24558_1 := h24558c.2.1
                  have p24558_2 := h24558c.2.2.1
                  have p24558_3 := h24558c.2.2.2
                  linarith only [h0, h22010, hc12, hc24, hlam, hphi, p24558_1]
                · have p24558_0 := h24558c.1
                  have p24558_1 := h24558c.2.1
                  have p24558_2 := h24558c.2.2.1
                  have p24558_3 := h24558c.2.2.2
                  rcases p24558_3 (m.d 0 2) (by simp) with h24601 | h24601
                  · linarith only [h24601, hlam, p24558_0]
                  · rcases p24558_3 (m.d 1 2) (by simp) with h24603 | h24603
                    · linarith only [h23344, h24603, hlam]
                    · rcases p24558_3 (m.d 2 3) (by simp) with h24605 | h24605
                      · rcases p24558_3 (m.d 2 4) (by simp) with h24606 | h24606
                        · rcases p24558_3 (m.d 2 5) (by simp) with h24607 | h24607
                          · rcases h4bigk with h24608c | h24608c | h24608c | h24608c | h24608c | h24608c | h24608c | h24608c | h24608c | h24608c | h24608c | h24608c | h24608c | h24608c | h24608c | h24608c | h24608c | h24608c | h24608c | h24608c | h24608c | h24608c | h24608c | h24608c | h24608c
                            · have p24608_0 := h24608c.1
                              have p24608_1 := h24608c.2.1
                              have p24608_2 := h24608c.2.2.1
                              have p24608_3 := h24608c.2.2.2
                              linarith only [hlam, p24608_0]
                            · have p24608_0 := h24608c.1
                              have p24608_1 := h24608c.2.1
                              have p24608_2 := h24608c.2.2.1
                              have p24608_3 := h24608c.2.2.2
                              rcases p24608_3 (m.d 0 4) (by simp) with h24610 | h24610
                              · rcases p24608_3 (m.d 1 4) (by simp) with h24611 | h24611
                                · linarith only [h2, h24611, hlam]
                                · rcases p24608_3 (m.d 2 4) (by simp) with h24613 | h24613
                                  · rcases p24608_3 (m.d 3 4) (by simp) with h24614 | h24614
                                    · linarith only [h23337, h24614, hlam]
                                    · rcases p24608_3 (m.d 4 5) (by simp) with h24616 | h24616
                                      · linarith only [h23339, h24616, hlam]
                                      · linarith only [h23348, h24616, hlam]
                                  · linarith only [h23342, h24613, hlam]
                              · linarith only [h2, h24610, hlam]
                            · have p24608_0 := h24608c.1
                              have p24608_1 := h24608c.2.1
                              have p24608_2 := h24608c.2.2.1
                              have p24608_3 := h24608c.2.2.2
                              linarith only [h19744, hlam, p24608_1]
                            · have p24608_0 := h24608c.1
                              have p24608_1 := h24608c.2.1
                              have p24608_2 := h24608c.2.2.1
                              have p24608_3 := h24608c.2.2.2
                              rcases p24608_3 (m.d 0 4) (by simp) with h24622 | h24622
                              · rcases p24608_3 (m.d 1 4) (by simp) with h24623 | h24623
                                · linarith only [h2, h24623, hlam]
                                · linarith only [h23346, h24623, hlam]
                              · linarith only [h23337, h24622, hlam]
                            · have p24608_0 := h24608c.1
                              have p24608_1 := h24608c.2.1
                              have p24608_2 := h24608c.2.2.1
                              have p24608_3 := h24608c.2.2.2
                              linarith only [h23337, h23342, h23348, h4, hc12, hc23, hlam, hphi, p24608_1]
                            · have p24608_0 := h24608c.1
                              have p24608_1 := h24608c.2.1
                              have p24608_2 := h24608c.2.2.1
                              have p24608_3 := h24608c.2.2.2
                              linarith only [h2, hlam, p24608_0]
                            · have p24608_0 := h24608c.1
                              have p24608_1 := h24608c.2.1
                              have p24608_2 := h24608c.2.2.1
                              have p24608_3 := h24608c.2.2.2
                              linarith only [hlam, p24608_0]
                            · have p24608_0 := h24608c.1
                              have p24608_1 := h24608c.2.1
                              have p24608_2 := h24608c.2.2.1
                              have p24608_3 := h24608c.2.2.2
                              linarith only [h23342, hlam, p24608_1]
                            · have p24608_0 := h24608c.1
                              have p24608_1 := h24608c.2.1
                              have p24608_2 := h24608c.2.2.1
                              have p24608_3 := h24608c.2.2.2
                              linarith only [h1, h23348, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23950_1, p24608_1]
                            · have p24608_0 := h24608c.1
                              have p24608_1 := h24608c.2.1
                              have p24608_2 := h24608c.2.2.1
                              have p24608_3 := h24608c.2.2.2
                              linarith only [h23348, hlam, p24608_0]
                            · have p24608_0 := h24608c.1
                              have p24608_1 := h24608c.2.1
                              have p24608_2 := h24608c.2.2.1
                              have p24608_3 := h24608c.2.2.2
                              linarith only [h23339, h23348, h23945, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p24608_1]
                            · have p24608_0 := h24608c.1
                              have p24608_1 := h24608c.2.1
                              have p24608_2 := h24608c.2.2.1
                              have p24608_3 := h24608c.2.2.2
                              rcases p24608_3 (m.d 0 4) (by simp) with h24634 | h24634
                              · linarith only [h19744, h24634, hlam]
                              · linarith only [h2, h24634, hlam]
                            · have p24608_0 := h24608c.1
                              have p24608_1 := h24608c.2.1
                              have p24608_2 := h24608c.2.2.1
                              have p24608_3 := h24608c.2.2.2
                              linarith only [hlam, p24608_0]
                            · have p24608_0 := h24608c.1
                              have p24608_1 := h24608c.2.1
                              have p24608_2 := h24608c.2.2.1
                              have p24608_3 := h24608c.2.2.2
                              rcases p24608_3 (m.d 0 4) (by simp) with h24638 | h24638
                              · linarith only [h19744, h24638, hlam]
                              · linarith only [h23337, h24638, hlam]
                            · have p24608_0 := h24608c.1
                              have p24608_1 := h24608c.2.1
                              have p24608_2 := h24608c.2.2.1
                              have p24608_3 := h24608c.2.2.2
                              linarith only [h23342, h23348, hc12, hc24, hlam, hphi, p24608_1]
                            · have p24608_0 := h24608c.1
                              have p24608_1 := h24608c.2.1
                              have p24608_2 := h24608c.2.2.1
                              have p24608_3 := h24608c.2.2.2
                              linarith only [h23337, hlam, p24608_0]
                            · have p24608_0 := h24608c.1
                              have p24608_1 := h24608c.2.1
                              have p24608_2 := h24608c.2.2.1
                              have p24608_3 := h24608c.2.2.2
                              linarith only [h23346, hlam, p24608_0]
                            · have p24608_0 := h24608c.1
                              have p24608_1 := h24608c.2.1
                              have p24608_2 := h24608c.2.2.1
                              have p24608_3 := h24608c.2.2.2
                              linarith only [h23945, hlam, p24608_0]
                            · have p24608_0 := h24608c.1
                              have p24608_1 := h24608c.2.1
                              have p24608_2 := h24608c.2.2.1
                              have p24608_3 := h24608c.2.2.2
                              linarith only [hlam, p24608_0]
                            · have p24608_0 := h24608c.1
                              have p24608_1 := h24608c.2.1
                              have p24608_2 := h24608c.2.2.1
                              have p24608_3 := h24608c.2.2.2
                              linarith only [h23948, hlam, p24608_0]
                            · have p24608_0 := h24608c.1
                              have p24608_1 := h24608c.2.1
                              have p24608_2 := h24608c.2.2.1
                              have p24608_3 := h24608c.2.2.2
                              linarith only [h23339, hlam, p24608_0]
                            · have p24608_0 := h24608c.1
                              have p24608_1 := h24608c.2.1
                              have p24608_2 := h24608c.2.2.1
                              have p24608_3 := h24608c.2.2.2
                              linarith only [h19744, h23339, h23342, hc12, hc24, hlam, hphi, p24608_1]
                            · have p24608_0 := h24608c.1
                              have p24608_1 := h24608c.2.1
                              have p24608_2 := h24608c.2.2.1
                              have p24608_3 := h24608c.2.2.2
                              linarith only [h23947, hlam, p24608_0]
                            · have p24608_0 := h24608c.1
                              have p24608_1 := h24608c.2.1
                              have p24608_2 := h24608c.2.2.1
                              have p24608_3 := h24608c.2.2.2
                              rcases p24608_3 (m.d 0 4) (by simp) with h24650 | h24650
                              · rcases p24608_3 (m.d 1 4) (by simp) with h24651 | h24651
                                · linarith only [h23348, h24651, hlam]
                                · linarith only [h23346, h24651, hlam]
                              · linarith only [h23337, h24650, hlam]
                            · have p24608_0 := h24608c.1
                              have p24608_1 := h24608c.2.1
                              have p24608_2 := h24608c.2.2.1
                              have p24608_3 := h24608c.2.2.2
                              linarith only [hlam, p24608_0]
                          · linarith only [h24607, hlam, p24558_0]
                        · linarith only [h19744, h24606, hlam]
                      · linarith only [h24605, h4, hlam]
                · have p24558_0 := h24558c.1
                  have p24558_1 := h24558c.2.1
                  have p24558_2 := h24558c.2.2.1
                  have p24558_3 := h24558c.2.2.2
                  rcases p24558_3 (m.d 0 2) (by simp) with h24659 | h24659
                  · linarith only [h22010, h24659, hlam]
                  · linarith only [h0, h24659, hlam]
                · have p24558_0 := h24558c.1
                  have p24558_1 := h24558c.2.1
                  have p24558_2 := h24558c.2.2.1
                  have p24558_3 := h24558c.2.2.2
                  linarith only [h23946, hlam, p24558_0]
                · have p24558_0 := h24558c.1
                  have p24558_1 := h24558c.2.1
                  have p24558_2 := h24558c.2.2.1
                  have p24558_3 := h24558c.2.2.2
                  linarith only [h23947, hlam, p24558_1]
                · have p24558_0 := h24558c.1
                  have p24558_1 := h24558c.2.1
                  have p24558_2 := h24558c.2.2.1
                  have p24558_3 := h24558c.2.2.2
                  linarith only [hlam, p24558_0]
              · rcases h2bigk with h24665c | h24665c | h24665c | h24665c | h24665c | h24665c | h24665c | h24665c | h24665c | h24665c | h24665c | h24665c | h24665c | h24665c | h24665c | h24665c | h24665c | h24665c | h24665c | h24665c | h24665c | h24665c | h24665c | h24665c | h24665c
                · have p24665_0 := h24665c.1
                  have p24665_1 := h24665c.2.1
                  have p24665_2 := h24665c.2.2.1
                  have p24665_3 := h24665c.2.2.2
                  linarith only [hlam, p24665_0]
                · have p24665_0 := h24665c.1
                  have p24665_1 := h24665c.2.1
                  have p24665_2 := h24665c.2.2.1
                  have p24665_3 := h24665c.2.2.2
                  linarith only [h4, hc12, hc23, hlam, hphi, p24665_1]
                · have p24665_0 := h24665c.1
                  have p24665_1 := h24665c.2.1
                  have p24665_2 := h24665c.2.2.1
                  have p24665_3 := h24665c.2.2.2
                  linarith only [h4, hlam, p24665_0]
                · have p24665_0 := h24665c.1
                  have p24665_1 := h24665c.2.1
                  have p24665_2 := h24665c.2.2.1
                  have p24665_3 := h24665c.2.2.2
                  linarith only [h19744, hlam, p24665_0]
                · have p24665_0 := h24665c.1
                  have p24665_1 := h24665c.2.1
                  have p24665_2 := h24665c.2.2.1
                  have p24665_3 := h24665c.2.2.2
                  linarith only [h22010, hlam, p24665_0]
                · have p24665_0 := h24665c.1
                  have p24665_1 := h24665c.2.1
                  have p24665_2 := h24665c.2.2.1
                  have p24665_3 := h24665c.2.2.2
                  linarith only [h0, hlam, p24665_1]
                · have p24665_0 := h24665c.1
                  have p24665_1 := h24665c.2.1
                  have p24665_2 := h24665c.2.2.1
                  have p24665_3 := h24665c.2.2.2
                  linarith only [hlam, p24665_0]
                · have p24665_0 := h24665c.1
                  have p24665_1 := h24665c.2.1
                  have p24665_2 := h24665c.2.2.1
                  have p24665_3 := h24665c.2.2.2
                  linarith only [h23340, hlam, p24665_0]
                · have p24665_0 := h24665c.1
                  have p24665_1 := h24665c.2.1
                  have p24665_2 := h24665c.2.2.1
                  have p24665_3 := h24665c.2.2.2
                  linarith only [h23342, hlam, p24665_0]
                · have p24665_0 := h24665c.1
                  have p24665_1 := h24665c.2.1
                  have p24665_2 := h24665c.2.2.1
                  have p24665_3 := h24665c.2.2.2
                  linarith only [h23344, hlam, p24665_0]
                · have p24665_0 := h24665c.1
                  have p24665_1 := h24665c.2.1
                  have p24665_2 := h24665c.2.2.1
                  have p24665_3 := h24665c.2.2.2
                  rcases p24665_3 (m.d 0 2) (by simp) with h24676 | h24676
                  · linarith only [h24676, hlam, p24665_0]
                  · rcases p24665_3 (m.d 1 2) (by simp) with h24678 | h24678
                    · linarith only [h23340, h24678, hlam]
                    · rcases p24665_3 (m.d 2 3) (by simp) with h24680 | h24680
                      · rcases p24665_3 (m.d 2 4) (by simp) with h24681 | h24681
                        · linarith only [h23945, h24681, hlam]
                        · linarith only [h19744, h24681, hlam]
                      · linarith only [h24680, hlam, p24665_0]
                · have p24665_0 := h24665c.1
                  have p24665_1 := h24665c.2.1
                  have p24665_2 := h24665c.2.2.1
                  have p24665_3 := h24665c.2.2.2
                  rcases p24665_3 (m.d 0 2) (by simp) with h24685 | h24685
                  · linarith only [h24685, h4, hlam]
                  · linarith only [h0, h24685, hlam]
                · have p24665_0 := h24665c.1
                  have p24665_1 := h24665c.2.1
                  have p24665_2 := h24665c.2.2.1
                  have p24665_3 := h24665c.2.2.2
                  linarith only [hlam, p24665_0]
                · have p24665_0 := h24665c.1
                  have p24665_1 := h24665c.2.1
                  have p24665_2 := h24665c.2.2.1
                  have p24665_3 := h24665c.2.2.2
                  linarith only [h19744, hc02, hc23, hlam, hphi, p24665_1]
                · have p24665_0 := h24665c.1
                  have p24665_1 := h24665c.2.1
                  have p24665_2 := h24665c.2.2.1
                  have p24665_3 := h24665c.2.2.2
                  linarith only [h0, h22010, hc12, hc23, hlam, hphi, p24665_1]
                · have p24665_0 := h24665c.1
                  have p24665_1 := h24665c.2.1
                  have p24665_2 := h24665c.2.2.1
                  have p24665_3 := h24665c.2.2.2
                  rcases p24665_3 (m.d 0 2) (by simp) with h24691 | h24691
                  · linarith only [h24691, hlam, p24665_0]
                  · rcases p24665_3 (m.d 1 2) (by simp) with h24693 | h24693
                    · linarith only [h23342, h24693, hlam]
                    · rcases p24665_3 (m.d 2 3) (by simp) with h24695 | h24695
                      · rcases p24665_3 (m.d 2 4) (by simp) with h24696 | h24696
                        · rcases p24665_3 (m.d 2 5) (by simp) with h24697 | h24697
                          · linarith only [h23947, h24697, hlam]
                          · linarith only [h22010, h24697, hlam]
                        · linarith only [h24696, hlam, p24665_0]
                      · linarith only [h24695, h4, hlam]
                · have p24665_0 := h24665c.1
                  have p24665_1 := h24665c.2.1
                  have p24665_2 := h24665c.2.2.1
                  have p24665_3 := h24665c.2.2.2
                  rcases p24665_3 (m.d 0 2) (by simp) with h24702 | h24702
                  · linarith only [h19744, h24702, hlam]
                  · linarith only [h0, h24702, hlam]
                · have p24665_0 := h24665c.1
                  have p24665_1 := h24665c.2.1
                  have p24665_2 := h24665c.2.2.1
                  have p24665_3 := h24665c.2.2.2
                  linarith only [h23945, hlam, p24665_0]
                · have p24665_0 := h24665c.1
                  have p24665_1 := h24665c.2.1
                  have p24665_2 := h24665c.2.2.1
                  have p24665_3 := h24665c.2.2.2
                  linarith only [hlam, p24665_0]
                · have p24665_0 := h24665c.1
                  have p24665_1 := h24665c.2.1
                  have p24665_2 := h24665c.2.2.1
                  have p24665_3 := h24665c.2.2.2
                  linarith only [h0, h22010, hc12, hc24, hlam, hphi, p24665_1]
                · have p24665_0 := h24665c.1
                  have p24665_1 := h24665c.2.1
                  have p24665_2 := h24665c.2.2.1
                  have p24665_3 := h24665c.2.2.2
                  rcases p24665_3 (m.d 0 2) (by simp) with h24708 | h24708
                  · linarith only [h24708, hlam, p24665_0]
                  · rcases p24665_3 (m.d 1 2) (by simp) with h24710 | h24710
                    · linarith only [h23344, h24710, hlam]
                    · rcases p24665_3 (m.d 2 3) (by simp) with h24712 | h24712
                      · rcases p24665_3 (m.d 2 4) (by simp) with h24713 | h24713
                        · rcases p24665_3 (m.d 2 5) (by simp) with h24714 | h24714
                          · rcases h4bigk with h24715c | h24715c | h24715c | h24715c | h24715c | h24715c | h24715c | h24715c | h24715c | h24715c | h24715c | h24715c | h24715c | h24715c | h24715c | h24715c | h24715c | h24715c | h24715c | h24715c | h24715c | h24715c | h24715c | h24715c | h24715c
                            · have p24715_0 := h24715c.1
                              have p24715_1 := h24715c.2.1
                              have p24715_2 := h24715c.2.2.1
                              have p24715_3 := h24715c.2.2.2
                              linarith only [hlam, p24715_0]
                            · have p24715_0 := h24715c.1
                              have p24715_1 := h24715c.2.1
                              have p24715_2 := h24715c.2.2.1
                              have p24715_3 := h24715c.2.2.2
                              rcases p24715_3 (m.d 0 4) (by simp) with h24717 | h24717
                              · rcases p24715_3 (m.d 1 4) (by simp) with h24718 | h24718
                                · linarith only [h2, h24718, hlam]
                                · rcases p24715_3 (m.d 2 4) (by simp) with h24720 | h24720
                                  · rcases p24715_3 (m.d 3 4) (by simp) with h24721 | h24721
                                    · linarith only [h23337, h24721, hlam]
                                    · rcases p24715_3 (m.d 4 5) (by simp) with h24723 | h24723
                                      · linarith only [h23339, h24723, hlam]
                                      · linarith only [h23348, h24723, hlam]
                                  · linarith only [h23342, h24720, hlam]
                              · linarith only [h2, h24717, hlam]
                            · have p24715_0 := h24715c.1
                              have p24715_1 := h24715c.2.1
                              have p24715_2 := h24715c.2.2.1
                              have p24715_3 := h24715c.2.2.2
                              linarith only [h19744, hlam, p24715_1]
                            · have p24715_0 := h24715c.1
                              have p24715_1 := h24715c.2.1
                              have p24715_2 := h24715c.2.2.1
                              have p24715_3 := h24715c.2.2.2
                              rcases p24715_3 (m.d 0 4) (by simp) with h24729 | h24729
                              · rcases p24715_3 (m.d 1 4) (by simp) with h24730 | h24730
                                · linarith only [h2, h24730, hlam]
                                · linarith only [h23346, h24730, hlam]
                              · linarith only [h23337, h24729, hlam]
                            · have p24715_0 := h24715c.1
                              have p24715_1 := h24715c.2.1
                              have p24715_2 := h24715c.2.2.1
                              have p24715_3 := h24715c.2.2.2
                              linarith only [h19744, h23342, h23348, h23945, hc12, hc23, hlam, hphi, p24715_1]
                            · have p24715_0 := h24715c.1
                              have p24715_1 := h24715c.2.1
                              have p24715_2 := h24715c.2.2.1
                              have p24715_3 := h24715c.2.2.2
                              linarith only [h2, hlam, p24715_0]
                            · have p24715_0 := h24715c.1
                              have p24715_1 := h24715c.2.1
                              have p24715_2 := h24715c.2.2.1
                              have p24715_3 := h24715c.2.2.2
                              linarith only [hlam, p24715_0]
                            · have p24715_0 := h24715c.1
                              have p24715_1 := h24715c.2.1
                              have p24715_2 := h24715c.2.2.1
                              have p24715_3 := h24715c.2.2.2
                              linarith only [h23342, hlam, p24715_1]
                            · have p24715_0 := h24715c.1
                              have p24715_1 := h24715c.2.1
                              have p24715_2 := h24715c.2.2.1
                              have p24715_3 := h24715c.2.2.2
                              linarith only [h1, h23348, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p23950_1, p24715_1]
                            · have p24715_0 := h24715c.1
                              have p24715_1 := h24715c.2.1
                              have p24715_2 := h24715c.2.2.1
                              have p24715_3 := h24715c.2.2.2
                              linarith only [h23348, hlam, p24715_0]
                            · have p24715_0 := h24715c.1
                              have p24715_1 := h24715c.2.1
                              have p24715_2 := h24715c.2.2.1
                              have p24715_3 := h24715c.2.2.2
                              linarith only [h23339, h23342, h23348, h23945, hc12, hc23, hlam, hphi, p24715_1]
                            · have p24715_0 := h24715c.1
                              have p24715_1 := h24715c.2.1
                              have p24715_2 := h24715c.2.2.1
                              have p24715_3 := h24715c.2.2.2
                              rcases p24715_3 (m.d 0 4) (by simp) with h24741 | h24741
                              · linarith only [h19744, h24741, hlam]
                              · linarith only [h2, h24741, hlam]
                            · have p24715_0 := h24715c.1
                              have p24715_1 := h24715c.2.1
                              have p24715_2 := h24715c.2.2.1
                              have p24715_3 := h24715c.2.2.2
                              linarith only [hlam, p24715_0]
                            · have p24715_0 := h24715c.1
                              have p24715_1 := h24715c.2.1
                              have p24715_2 := h24715c.2.2.1
                              have p24715_3 := h24715c.2.2.2
                              rcases p24715_3 (m.d 0 4) (by simp) with h24745 | h24745
                              · linarith only [h19744, h24745, hlam]
                              · linarith only [h23337, h24745, hlam]
                            · have p24715_0 := h24715c.1
                              have p24715_1 := h24715c.2.1
                              have p24715_2 := h24715c.2.2.1
                              have p24715_3 := h24715c.2.2.2
                              linarith only [h23342, h23348, hc12, hc24, hlam, hphi, p24715_1]
                            · have p24715_0 := h24715c.1
                              have p24715_1 := h24715c.2.1
                              have p24715_2 := h24715c.2.2.1
                              have p24715_3 := h24715c.2.2.2
                              linarith only [h23337, hlam, p24715_0]
                            · have p24715_0 := h24715c.1
                              have p24715_1 := h24715c.2.1
                              have p24715_2 := h24715c.2.2.1
                              have p24715_3 := h24715c.2.2.2
                              linarith only [h23346, hlam, p24715_0]
                            · have p24715_0 := h24715c.1
                              have p24715_1 := h24715c.2.1
                              have p24715_2 := h24715c.2.2.1
                              have p24715_3 := h24715c.2.2.2
                              linarith only [h23945, hlam, p24715_0]
                            · have p24715_0 := h24715c.1
                              have p24715_1 := h24715c.2.1
                              have p24715_2 := h24715c.2.2.1
                              have p24715_3 := h24715c.2.2.2
                              linarith only [hlam, p24715_0]
                            · have p24715_0 := h24715c.1
                              have p24715_1 := h24715c.2.1
                              have p24715_2 := h24715c.2.2.1
                              have p24715_3 := h24715c.2.2.2
                              linarith only [h23948, hlam, p24715_0]
                            · have p24715_0 := h24715c.1
                              have p24715_1 := h24715c.2.1
                              have p24715_2 := h24715c.2.2.1
                              have p24715_3 := h24715c.2.2.2
                              linarith only [h23339, hlam, p24715_0]
                            · have p24715_0 := h24715c.1
                              have p24715_1 := h24715c.2.1
                              have p24715_2 := h24715c.2.2.1
                              have p24715_3 := h24715c.2.2.2
                              linarith only [h19744, h23339, h23342, hc12, hc24, hlam, hphi, p24715_1]
                            · have p24715_0 := h24715c.1
                              have p24715_1 := h24715c.2.1
                              have p24715_2 := h24715c.2.2.1
                              have p24715_3 := h24715c.2.2.2
                              linarith only [h23947, hlam, p24715_0]
                            · have p24715_0 := h24715c.1
                              have p24715_1 := h24715c.2.1
                              have p24715_2 := h24715c.2.2.1
                              have p24715_3 := h24715c.2.2.2
                              rcases p24715_3 (m.d 0 4) (by simp) with h24757 | h24757
                              · rcases p24715_3 (m.d 1 4) (by simp) with h24758 | h24758
                                · linarith only [h23348, h24758, hlam]
                                · linarith only [h23346, h24758, hlam]
                              · linarith only [h23337, h24757, hlam]
                            · have p24715_0 := h24715c.1
                              have p24715_1 := h24715c.2.1
                              have p24715_2 := h24715c.2.2.1
                              have p24715_3 := h24715c.2.2.2
                              linarith only [hlam, p24715_0]
                          · linarith only [h24714, hlam, p24665_0]
                        · linarith only [h19744, h24713, hlam]
                      · linarith only [h24712, h4, hlam]
                · have p24665_0 := h24665c.1
                  have p24665_1 := h24665c.2.1
                  have p24665_2 := h24665c.2.2.1
                  have p24665_3 := h24665c.2.2.2
                  rcases p24665_3 (m.d 0 2) (by simp) with h24766 | h24766
                  · linarith only [h22010, h24766, hlam]
                  · linarith only [h0, h24766, hlam]
                · have p24665_0 := h24665c.1
                  have p24665_1 := h24665c.2.1
                  have p24665_2 := h24665c.2.2.1
                  have p24665_3 := h24665c.2.2.2
                  linarith only [h23946, hlam, p24665_0]
                · have p24665_0 := h24665c.1
                  have p24665_1 := h24665c.2.1
                  have p24665_2 := h24665c.2.2.1
                  have p24665_3 := h24665c.2.2.2
                  linarith only [h23947, hlam, p24665_1]
                · have p24665_0 := h24665c.1
                  have p24665_1 := h24665c.2.1
                  have p24665_2 := h24665c.2.2.1
                  have p24665_3 := h24665c.2.2.2
                  linarith only [hlam, p24665_0]
        · linarith only [h23347, h24443, hlam]
    · linarith only [h24440, h3, hlam]
  · have p23950_0 := h23950c.1
    have p23950_1 := h23950c.2.1
    have p23950_2 := h23950c.2.2.1
    have p23950_3 := h23950c.2.2.2
    linarith only [h2, hlam, p23950_0]
  · have p23950_0 := h23950c.1
    have p23950_1 := h23950c.2.1
    have p23950_2 := h23950c.2.2.1
    have p23950_3 := h23950c.2.2.2
    linarith only [h23337, h23339, h23348, h4, hc12, hc23, hlam, hphi, p23950_1]
  · have p23950_0 := h23950c.1
    have p23950_1 := h23950c.2.1
    have p23950_2 := h23950c.2.2.1
    have p23950_3 := h23950c.2.2.2
    linarith only [h23346, hlam, p23950_1]
  · have p23950_0 := h23950c.1
    have p23950_1 := h23950c.2.1
    have p23950_2 := h23950c.2.2.1
    have p23950_3 := h23950c.2.2.2
    linarith only [hlam, p23950_0]
  · have p23950_0 := h23950c.1
    have p23950_1 := h23950c.2.1
    have p23950_2 := h23950c.2.2.1
    have p23950_3 := h23950c.2.2.2
    linarith only [h23348, hlam, p23950_1]
  · have p23950_0 := h23950c.1
    have p23950_1 := h23950c.2.1
    have p23950_2 := h23950c.2.2.1
    have p23950_3 := h23950c.2.2.2
    linarith only [h3, hlam, p23950_0]
  · have p23950_0 := h23950c.1
    have p23950_1 := h23950c.2.1
    have p23950_2 := h23950c.2.2.1
    have p23950_3 := h23950c.2.2.2
    linarith only [h23337, h23339, h23348, h4, hc12, hc23, hlam, hphi, p23950_1]
  · have p23950_0 := h23950c.1
    have p23950_1 := h23950c.2.1
    have p23950_2 := h23950c.2.2.1
    have p23950_3 := h23950c.2.2.2
    linarith only [h23347, hlam, p23950_0]
  · have p23950_0 := h23950c.1
    have p23950_1 := h23950c.2.1
    have p23950_2 := h23950c.2.2.1
    have p23950_3 := h23950c.2.2.2
    linarith only [h23337, h23339, h23342, h23348, h4, hc12, hc23, hlam, hphi, p23950_1]
  · have p23950_0 := h23950c.1
    have p23950_1 := h23950c.2.1
    have p23950_2 := h23950c.2.2.1
    have p23950_3 := h23950c.2.2.2
    linarith only [hlam, p23950_0]

end R2N4
