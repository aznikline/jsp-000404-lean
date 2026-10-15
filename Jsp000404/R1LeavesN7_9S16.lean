import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_9S15

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8270000 in
set_option maxHeartbeats 8270000 in
theorem r1l7_13_24_L_I_H_I_s11_x0_x0_x0_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7360 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8811 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg10295 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11548 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h11549 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h11550 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h11551 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h7360 := hg7360
  have h8811 := hg8811
  have h10295 := hg10295
  rcases m.htr 0 4 5 (by decide) (by decide) with h12952 | h12952
  · linarith only [h11550, h11551, h12952, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h12954 | h12954
    · rcases m.htr 1 2 4 (by decide) (by decide) with h12955 | h12955
      · rcases m.htr 1 3 4 (by decide) (by decide) with h12956 | h12956
        · rcases m.htr 1 3 5 (by decide) (by decide) with h12957 | h12957
          · rcases m.htr 1 4 5 (by decide) (by decide) with h12958 | h12958
            · rcases m.htr 2 3 4 (by decide) (by decide) with h12959 | h12959
              · rcases m.htr 2 3 5 (by decide) (by decide) with h12960 | h12960
                · linarith only [h11548, h11551, h12960, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h12962 | h12962
                  · linarith only [h0, h11549, h12952, h12962, h8811, hc01, hc12, hlam, hphi]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h12964 | h12964
                    · linarith only [h11548, h11551, h12952, h12957, h12959, h12964, h8811, hc01, hc13, hlam, hphi]
                    · rcases h3bigk with h12966c | h12966c | h12966c | h12966c | h12966c | h12966c | h12966c | h12966c | h12966c | h12966c | h12966c | h12966c | h12966c | h12966c | h12966c | h12966c | h12966c | h12966c | h12966c | h12966c | h12966c | h12966c | h12966c | h12966c | h12966c
                      · have p12966_0 := h12966c.1
                        have p12966_1 := h12966c.2.1
                        have p12966_2 := h12966c.2.2.1
                        have p12966_3 := h12966c.2.2.2
                        linarith only [hlam, p12966_0]
                      · have p12966_0 := h12966c.1
                        have p12966_1 := h12966c.2.1
                        have p12966_2 := h12966c.2.2.1
                        have p12966_3 := h12966c.2.2.2
                        linarith only [h7360, hlam, p12966_1]
                      · have p12966_0 := h12966c.1
                        have p12966_1 := h12966c.2.1
                        have p12966_2 := h12966c.2.2.1
                        have p12966_3 := h12966c.2.2.2
                        linarith only [h11551, h12954, h12956, h12958, h12959, h12964, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12966_1]
                      · have p12966_0 := h12966c.1
                        have p12966_1 := h12966c.2.1
                        have p12966_2 := h12966c.2.2.1
                        have p12966_3 := h12966c.2.2.2
                        linarith only [h11551, h12954, h12956, h12958, h12964, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12966_1]
                      · have p12966_0 := h12966c.1
                        have p12966_1 := h12966c.2.1
                        have p12966_2 := h12966c.2.2.1
                        have p12966_3 := h12966c.2.2.2
                        linarith only [h11551, hlam, p12966_0]
                      · have p12966_0 := h12966c.1
                        have p12966_1 := h12966c.2.1
                        have p12966_2 := h12966c.2.2.1
                        have p12966_3 := h12966c.2.2.2
                        rcases p12966_3 (m.d 0 3) (by simp) with h12972 | h12972
                        · linarith only [h12972, h7360, hlam]
                        · rcases p12966_3 (m.d 1 3) (by simp) with h12974 | h12974
                          · rcases p12966_3 (m.d 2 3) (by simp) with h12975 | h12975
                            · linarith only [h12954, h12975, hlam]
                            · rcases p12966_3 (m.d 3 4) (by simp) with h12977 | h12977
                              · linarith only [h12956, h12977, hlam]
                              · rcases p12966_3 (m.d 3 5) (by simp) with h12979 | h12979
                                · linarith only [h12957, h12979, hlam]
                                · linarith only [h11551, h12979, hlam]
                          · linarith only [h12974, h7360, hlam]
                      · have p12966_0 := h12966c.1
                        have p12966_1 := h12966c.2.1
                        have p12966_2 := h12966c.2.2.1
                        have p12966_3 := h12966c.2.2.2
                        linarith only [hlam, p12966_0]
                      · have p12966_0 := h12966c.1
                        have p12966_1 := h12966c.2.1
                        have p12966_2 := h12966c.2.2.1
                        have p12966_3 := h12966c.2.2.2
                        rcases p12966_3 (m.d 0 3) (by simp) with h12984 | h12984
                        · linarith only [h12984, h7360, hlam]
                        · linarith only [h11548, h12984, hlam]
                      · have p12966_0 := h12966c.1
                        have p12966_1 := h12966c.2.1
                        have p12966_2 := h12966c.2.2.1
                        have p12966_3 := h12966c.2.2.2
                        linarith only [h11548, h11551, h12956, h12958, h12959, h12964, hlam, p12966_2]
                      · have p12966_0 := h12966c.1
                        have p12966_1 := h12966c.2.1
                        have p12966_2 := h12966c.2.2.1
                        have p12966_3 := h12966c.2.2.2
                        linarith only [h11548, h11551, h12954, h12959, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12966_1]
                      · have p12966_0 := h12966c.1
                        have p12966_1 := h12966c.2.1
                        have p12966_2 := h12966c.2.2.1
                        have p12966_3 := h12966c.2.2.2
                        linarith only [h11548, hlam, p12966_0]
                      · have p12966_0 := h12966c.1
                        have p12966_1 := h12966c.2.1
                        have p12966_2 := h12966c.2.2.1
                        have p12966_3 := h12966c.2.2.2
                        linarith only [h12954, hlam, p12966_0]
                      · have p12966_0 := h12966c.1
                        have p12966_1 := h12966c.2.1
                        have p12966_2 := h12966c.2.2.1
                        have p12966_3 := h12966c.2.2.2
                        linarith only [hlam, p12966_0]
                      · have p12966_0 := h12966c.1
                        have p12966_1 := h12966c.2.1
                        have p12966_2 := h12966c.2.2.1
                        have p12966_3 := h12966c.2.2.2
                        linarith only [h11548, h11551, h12954, h12957, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12966_1]
                      · have p12966_0 := h12966c.1
                        have p12966_1 := h12966c.2.1
                        have p12966_2 := h12966c.2.2.1
                        have p12966_3 := h12966c.2.2.2
                        linarith only [h12960, hlam, p12966_0]
                      · have p12966_0 := h12966c.1
                        have p12966_1 := h12966c.2.1
                        have p12966_2 := h12966c.2.2.1
                        have p12966_3 := h12966c.2.2.2
                        linarith only [h11550, hlam, p12966_0]
                      · have p12966_0 := h12966c.1
                        have p12966_1 := h12966c.2.1
                        have p12966_2 := h12966c.2.2.1
                        have p12966_3 := h12966c.2.2.2
                        linarith only [h12956, hlam, p12966_0]
                      · have p12966_0 := h12966c.1
                        have p12966_1 := h12966c.2.1
                        have p12966_2 := h12966c.2.2.1
                        have p12966_3 := h12966c.2.2.2
                        linarith only [h12959, hlam, p12966_0]
                      · have p12966_0 := h12966c.1
                        have p12966_1 := h12966c.2.1
                        have p12966_2 := h12966c.2.2.1
                        have p12966_3 := h12966c.2.2.2
                        linarith only [hlam, p12966_0]
                      · have p12966_0 := h12966c.1
                        have p12966_1 := h12966c.2.1
                        have p12966_2 := h12966c.2.2.1
                        have p12966_3 := h12966c.2.2.2
                        linarith only [h12964, hlam, p12966_1]
                      · have p12966_0 := h12966c.1
                        have p12966_1 := h12966c.2.1
                        have p12966_2 := h12966c.2.2.1
                        have p12966_3 := h12966c.2.2.2
                        linarith only [h12954, h12957, h7360, hc01, hc12, hlam, hphi, p12966_1]
                      · have p12966_0 := h12966c.1
                        have p12966_1 := h12966c.2.1
                        have p12966_2 := h12966c.2.2.1
                        have p12966_3 := h12966c.2.2.2
                        linarith only [h12957, hlam, p12966_0]
                      · have p12966_0 := h12966c.1
                        have p12966_1 := h12966c.2.1
                        have p12966_2 := h12966c.2.2.1
                        have p12966_3 := h12966c.2.2.2
                        linarith only [h12954, h12957, h12959, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p12966_1]
                      · have p12966_0 := h12966c.1
                        have p12966_1 := h12966c.2.1
                        have p12966_2 := h12966c.2.2.1
                        have p12966_3 := h12966c.2.2.2
                        rcases p12966_3 (m.d 0 3) (by simp) with h13002 | h13002
                        · linarith only [h11551, h13002, hlam]
                        · linarith only [h11550, h13002, hlam]
                      · have p12966_0 := h12966c.1
                        have p12966_1 := h12966c.2.1
                        have p12966_2 := h12966c.2.2.1
                        have p12966_3 := h12966c.2.2.2
                        linarith only [hlam, p12966_0]
              · linarith only [h11550, h11551, h12959, hc23, hc35, hlam, hphi]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h13007 | h13007
              · rcases m.htr 2 3 5 (by decide) (by decide) with h13008 | h13008
                · linarith only [h11548, h11551, h13008, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h13010 | h13010
                  · linarith only [h12958, h13010, h8811, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h13012 | h13012
                    · linarith only [h11548, h11551, h12954, h12957, h12958, h13007, h13012, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases h3bigk with h13014c | h13014c | h13014c | h13014c | h13014c | h13014c | h13014c | h13014c | h13014c | h13014c | h13014c | h13014c | h13014c | h13014c | h13014c | h13014c | h13014c | h13014c | h13014c | h13014c | h13014c | h13014c | h13014c | h13014c | h13014c
                      · have p13014_0 := h13014c.1
                        have p13014_1 := h13014c.2.1
                        have p13014_2 := h13014c.2.2.1
                        have p13014_3 := h13014c.2.2.2
                        linarith only [hlam, p13014_0]
                      · have p13014_0 := h13014c.1
                        have p13014_1 := h13014c.2.1
                        have p13014_2 := h13014c.2.2.1
                        have p13014_3 := h13014c.2.2.2
                        linarith only [h7360, hlam, p13014_1]
                      · have p13014_0 := h13014c.1
                        have p13014_1 := h13014c.2.1
                        have p13014_2 := h13014c.2.2.1
                        have p13014_3 := h13014c.2.2.2
                        linarith only [h11551, h12954, h12957, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13014_1]
                      · have p13014_0 := h13014c.1
                        have p13014_1 := h13014c.2.1
                        have p13014_2 := h13014c.2.2.1
                        have p13014_3 := h13014c.2.2.2
                        linarith only [h11551, h12954, h12957, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13014_1]
                      · have p13014_0 := h13014c.1
                        have p13014_1 := h13014c.2.1
                        have p13014_2 := h13014c.2.2.1
                        have p13014_3 := h13014c.2.2.2
                        linarith only [h11551, hlam, p13014_0]
                      · have p13014_0 := h13014c.1
                        have p13014_1 := h13014c.2.1
                        have p13014_2 := h13014c.2.2.1
                        have p13014_3 := h13014c.2.2.2
                        rcases p13014_3 (m.d 0 3) (by simp) with h13020 | h13020
                        · linarith only [h13020, h7360, hlam]
                        · rcases p13014_3 (m.d 1 3) (by simp) with h13022 | h13022
                          · rcases p13014_3 (m.d 2 3) (by simp) with h13023 | h13023
                            · linarith only [h12954, h13023, hlam]
                            · rcases p13014_3 (m.d 3 4) (by simp) with h13025 | h13025
                              · linarith only [h12956, h13025, hlam]
                              · rcases p13014_3 (m.d 3 5) (by simp) with h13027 | h13027
                                · linarith only [h12957, h13027, hlam]
                                · linarith only [h11551, h13027, hlam]
                          · linarith only [h13022, h7360, hlam]
                      · have p13014_0 := h13014c.1
                        have p13014_1 := h13014c.2.1
                        have p13014_2 := h13014c.2.2.1
                        have p13014_3 := h13014c.2.2.2
                        linarith only [hlam, p13014_0]
                      · have p13014_0 := h13014c.1
                        have p13014_1 := h13014c.2.1
                        have p13014_2 := h13014c.2.2.1
                        have p13014_3 := h13014c.2.2.2
                        rcases p13014_3 (m.d 0 3) (by simp) with h13032 | h13032
                        · linarith only [h13032, h7360, hlam]
                        · linarith only [h11548, h13032, hlam]
                      · have p13014_0 := h13014c.1
                        have p13014_1 := h13014c.2.1
                        have p13014_2 := h13014c.2.2.1
                        have p13014_3 := h13014c.2.2.2
                        linarith only [h11548, h11551, h12957, h13007, hlam, p13014_2]
                      · have p13014_0 := h13014c.1
                        have p13014_1 := h13014c.2.1
                        have p13014_2 := h13014c.2.2.1
                        have p13014_3 := h13014c.2.2.2
                        linarith only [h11551, h12954, h7360, hc01, hc12, hlam, hphi, p13014_1]
                      · have p13014_0 := h13014c.1
                        have p13014_1 := h13014c.2.1
                        have p13014_2 := h13014c.2.2.1
                        have p13014_3 := h13014c.2.2.2
                        linarith only [h11548, hlam, p13014_0]
                      · have p13014_0 := h13014c.1
                        have p13014_1 := h13014c.2.1
                        have p13014_2 := h13014c.2.2.1
                        have p13014_3 := h13014c.2.2.2
                        linarith only [h12954, hlam, p13014_0]
                      · have p13014_0 := h13014c.1
                        have p13014_1 := h13014c.2.1
                        have p13014_2 := h13014c.2.2.1
                        have p13014_3 := h13014c.2.2.2
                        linarith only [hlam, p13014_0]
                      · have p13014_0 := h13014c.1
                        have p13014_1 := h13014c.2.1
                        have p13014_2 := h13014c.2.2.1
                        have p13014_3 := h13014c.2.2.2
                        linarith only [h11548, h11551, h12954, h12957, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13014_1]
                      · have p13014_0 := h13014c.1
                        have p13014_1 := h13014c.2.1
                        have p13014_2 := h13014c.2.2.1
                        have p13014_3 := h13014c.2.2.2
                        linarith only [h13008, hlam, p13014_0]
                      · have p13014_0 := h13014c.1
                        have p13014_1 := h13014c.2.1
                        have p13014_2 := h13014c.2.2.1
                        have p13014_3 := h13014c.2.2.2
                        linarith only [h11550, hlam, p13014_0]
                      · have p13014_0 := h13014c.1
                        have p13014_1 := h13014c.2.1
                        have p13014_2 := h13014c.2.2.1
                        have p13014_3 := h13014c.2.2.2
                        linarith only [h12956, hlam, p13014_0]
                      · have p13014_0 := h13014c.1
                        have p13014_1 := h13014c.2.1
                        have p13014_2 := h13014c.2.2.1
                        have p13014_3 := h13014c.2.2.2
                        linarith only [h13007, hlam, p13014_0]
                      · have p13014_0 := h13014c.1
                        have p13014_1 := h13014c.2.1
                        have p13014_2 := h13014c.2.2.1
                        have p13014_3 := h13014c.2.2.2
                        linarith only [hlam, p13014_0]
                      · have p13014_0 := h13014c.1
                        have p13014_1 := h13014c.2.1
                        have p13014_2 := h13014c.2.2.1
                        have p13014_3 := h13014c.2.2.2
                        linarith only [h13012, hlam, p13014_1]
                      · have p13014_0 := h13014c.1
                        have p13014_1 := h13014c.2.1
                        have p13014_2 := h13014c.2.2.1
                        have p13014_3 := h13014c.2.2.2
                        linarith only [h12954, h12957, h7360, hc01, hc12, hlam, hphi, p13014_1]
                      · have p13014_0 := h13014c.1
                        have p13014_1 := h13014c.2.1
                        have p13014_2 := h13014c.2.2.1
                        have p13014_3 := h13014c.2.2.2
                        linarith only [h12957, hlam, p13014_0]
                      · have p13014_0 := h13014c.1
                        have p13014_1 := h13014c.2.1
                        have p13014_2 := h13014c.2.2.1
                        have p13014_3 := h13014c.2.2.2
                        linarith only [h12954, h12957, h13007, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13014_1]
                      · have p13014_0 := h13014c.1
                        have p13014_1 := h13014c.2.1
                        have p13014_2 := h13014c.2.2.1
                        have p13014_3 := h13014c.2.2.2
                        rcases p13014_3 (m.d 0 3) (by simp) with h13050 | h13050
                        · linarith only [h11551, h13050, hlam]
                        · linarith only [h11550, h13050, hlam]
                      · have p13014_0 := h13014c.1
                        have p13014_1 := h13014c.2.1
                        have p13014_2 := h13014c.2.2.1
                        have p13014_3 := h13014c.2.2.2
                        linarith only [hlam, p13014_0]
              · linarith only [h11550, h11551, h12954, h12957, h13007, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h13055 | h13055
            · linarith only [h12952, h12956, h12957, h13055, h8811, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h13057 | h13057
              · rcases m.htr 2 3 5 (by decide) (by decide) with h13058 | h13058
                · linarith only [h12957, h13058, h7360, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h13060 | h13060
                  · linarith only [h13055, h13060, h8811, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h13062 | h13062
                    · linarith only [h13055, h13062, h8811, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases h3bigk with h13064c | h13064c | h13064c | h13064c | h13064c | h13064c | h13064c | h13064c | h13064c | h13064c | h13064c | h13064c | h13064c | h13064c | h13064c | h13064c | h13064c | h13064c | h13064c | h13064c | h13064c | h13064c | h13064c | h13064c | h13064c
                      · have p13064_0 := h13064c.1
                        have p13064_1 := h13064c.2.1
                        have p13064_2 := h13064c.2.2.1
                        have p13064_3 := h13064c.2.2.2
                        linarith only [hlam, p13064_0]
                      · have p13064_0 := h13064c.1
                        have p13064_1 := h13064c.2.1
                        have p13064_2 := h13064c.2.2.1
                        have p13064_3 := h13064c.2.2.2
                        linarith only [h7360, hlam, p13064_1]
                      · have p13064_0 := h13064c.1
                        have p13064_1 := h13064c.2.1
                        have p13064_2 := h13064c.2.2.1
                        have p13064_3 := h13064c.2.2.2
                        linarith only [h12957, h13062, h7360, hc23, hc45, hlam, hphi, ht34, p13064_1]
                      · have p13064_0 := h13064c.1
                        have p13064_1 := h13064c.2.1
                        have p13064_2 := h13064c.2.2.1
                        have p13064_3 := h13064c.2.2.2
                        linarith only [h12957, h13062, h7360, hc34, hc45, hlam, hphi, p13064_1]
                      · have p13064_0 := h13064c.1
                        have p13064_1 := h13064c.2.1
                        have p13064_2 := h13064c.2.2.1
                        have p13064_3 := h13064c.2.2.2
                        linarith only [h11551, hlam, p13064_0]
                      · have p13064_0 := h13064c.1
                        have p13064_1 := h13064c.2.1
                        have p13064_2 := h13064c.2.2.1
                        have p13064_3 := h13064c.2.2.2
                        linarith only [h12957, h13062, hc03, hc45, hlam, hphi, ht34, p13064_1]
                      · have p13064_0 := h13064c.1
                        have p13064_1 := h13064c.2.1
                        have p13064_2 := h13064c.2.2.1
                        have p13064_3 := h13064c.2.2.2
                        linarith only [hlam, p13064_0]
                      · have p13064_0 := h13064c.1
                        have p13064_1 := h13064c.2.1
                        have p13064_2 := h13064c.2.2.1
                        have p13064_3 := h13064c.2.2.2
                        linarith only [h12957, h13057, h13062, hc34, hc45, hlam, hphi, p13064_1]
                      · have p13064_0 := h13064c.1
                        have p13064_1 := h13064c.2.1
                        have p13064_2 := h13064c.2.2.1
                        have p13064_3 := h13064c.2.2.2
                        linarith only [h12957, h13062, hc34, hc45, hlam, hphi, p13064_1]
                      · have p13064_0 := h13064c.1
                        have p13064_1 := h13064c.2.1
                        have p13064_2 := h13064c.2.2.1
                        have p13064_3 := h13064c.2.2.2
                        linarith only [h12957, hlam, p13064_0]
                      · have p13064_0 := h13064c.1
                        have p13064_1 := h13064c.2.1
                        have p13064_2 := h13064c.2.2.1
                        have p13064_3 := h13064c.2.2.2
                        linarith only [h11548, hlam, p13064_0]
                      · have p13064_0 := h13064c.1
                        have p13064_1 := h13064c.2.1
                        have p13064_2 := h13064c.2.2.1
                        have p13064_3 := h13064c.2.2.2
                        linarith only [h12954, hlam, p13064_0]
                      · have p13064_0 := h13064c.1
                        have p13064_1 := h13064c.2.1
                        have p13064_2 := h13064c.2.2.1
                        have p13064_3 := h13064c.2.2.2
                        linarith only [hlam, p13064_0]
                      · have p13064_0 := h13064c.1
                        have p13064_1 := h13064c.2.1
                        have p13064_2 := h13064c.2.2.1
                        have p13064_3 := h13064c.2.2.2
                        linarith only [h11548, h12957, h13062, h7360, hc34, hc45, hlam, hphi, p13064_1]
                      · have p13064_0 := h13064c.1
                        have p13064_1 := h13064c.2.1
                        have p13064_2 := h13064c.2.2.1
                        have p13064_3 := h13064c.2.2.2
                        linarith only [h13058, hlam, p13064_0]
                      · have p13064_0 := h13064c.1
                        have p13064_1 := h13064c.2.1
                        have p13064_2 := h13064c.2.2.1
                        have p13064_3 := h13064c.2.2.2
                        linarith only [h11550, hlam, p13064_0]
                      · have p13064_0 := h13064c.1
                        have p13064_1 := h13064c.2.1
                        have p13064_2 := h13064c.2.2.1
                        have p13064_3 := h13064c.2.2.2
                        linarith only [h12956, hlam, p13064_0]
                      · have p13064_0 := h13064c.1
                        have p13064_1 := h13064c.2.1
                        have p13064_2 := h13064c.2.2.1
                        have p13064_3 := h13064c.2.2.2
                        linarith only [h13057, hlam, p13064_0]
                      · have p13064_0 := h13064c.1
                        have p13064_1 := h13064c.2.1
                        have p13064_2 := h13064c.2.2.1
                        have p13064_3 := h13064c.2.2.2
                        linarith only [hlam, p13064_0]
                      · have p13064_0 := h13064c.1
                        have p13064_1 := h13064c.2.1
                        have p13064_2 := h13064c.2.2.1
                        have p13064_3 := h13064c.2.2.2
                        linarith only [h13062, hlam, p13064_1]
                      · have p13064_0 := h13064c.1
                        have p13064_1 := h13064c.2.1
                        have p13064_2 := h13064c.2.2.1
                        have p13064_3 := h13064c.2.2.2
                        linarith only [h11550, h13062, hc34, hc45, hlam, hphi, p13064_1]
                      · have p13064_0 := h13064c.1
                        have p13064_1 := h13064c.2.1
                        have p13064_2 := h13064c.2.2.1
                        have p13064_3 := h13064c.2.2.2
                        linarith only [h13062, h7360, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p13064_1]
                      · have p13064_0 := h13064c.1
                        have p13064_1 := h13064c.2.1
                        have p13064_2 := h13064c.2.2.1
                        have p13064_3 := h13064c.2.2.2
                        linarith only [h13057, h13062, hc34, hc45, hlam, hphi, p13064_1]
                      · have p13064_0 := h13064c.1
                        have p13064_1 := h13064c.2.1
                        have p13064_2 := h13064c.2.2.1
                        have p13064_3 := h13064c.2.2.2
                        rcases p13064_3 (m.d 0 3) (by simp) with h13088 | h13088
                        · linarith only [h11551, h13088, hlam]
                        · linarith only [h11550, h13088, hlam]
                      · have p13064_0 := h13064c.1
                        have p13064_1 := h13064c.2.1
                        have p13064_2 := h13064c.2.2.1
                        have p13064_3 := h13064c.2.2.2
                        linarith only [hlam, p13064_0]
              · linarith only [h11550, h11551, h13057, hc23, hc35, hlam, hphi]
        · linarith only [h11550, h11551, h12956, hc13, hc35, hlam, hphi]
      · linarith only [h0, h11549, h12952, h12955, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
    · linarith only [h0, h11548, h12954, hlam]

set_option maxHeartbeats 8270000 in
set_option maxHeartbeats 8270000 in
theorem r1l7_13_24_L_I_H_I_s11_x0_x0_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7360 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8811 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg10295 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11548 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h11549 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h11550 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h7360 := hg7360
  have h8811 := hg8811
  have h10295 := hg10295
  rcases m.htr 0 3 5 (by decide) (by decide) with h11551 | h11551
  · exact r1l7_13_24_L_I_H_I_s11_x0_x0_x0_x0 m hb3 hb4 hg0 hg7360 hg8811 hg10295 h11548 h11549 h11550 h11551
  · exact r1l7_13_24_L_I_H_I_s11_x0_x0_x0_x1 m hb3 hb4 hg0 hg7360 hg8811 hg10295 h11548 h11549 h11550 h11551

set_option maxHeartbeats 8270000 in
set_option maxHeartbeats 8270000 in
theorem r1l7_13_24_L_I_H_I_s11_x0_x0_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7360 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8811 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg10295 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11548 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h11549 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h11550 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h7360 := hg7360
  have h8811 := hg8811
  have h10295 := hg10295
  rcases m.htr 0 3 5 (by decide) (by decide) with h13096 | h13096
  · rcases m.htr 0 4 5 (by decide) (by decide) with h13097 | h13097
    · rcases m.htr 1 2 3 (by decide) (by decide) with h13098 | h13098
      · rcases m.htr 1 2 4 (by decide) (by decide) with h13099 | h13099
        · rcases m.htr 1 3 4 (by decide) (by decide) with h13100 | h13100
          · rcases m.htr 1 3 5 (by decide) (by decide) with h13101 | h13101
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13102 | h13102
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13103 | h13103
                · linarith only [h11548, h11550, h13103, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13105 | h13105
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13106 | h13106
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13107 | h13107
                      · rcases h3bigk with h13108c | h13108c | h13108c | h13108c | h13108c | h13108c | h13108c | h13108c | h13108c | h13108c | h13108c | h13108c | h13108c | h13108c | h13108c | h13108c | h13108c | h13108c | h13108c | h13108c | h13108c | h13108c | h13108c | h13108c | h13108c
                        · have p13108_0 := h13108c.1
                          have p13108_1 := h13108c.2.1
                          have p13108_2 := h13108c.2.2.1
                          have p13108_3 := h13108c.2.2.2
                          linarith only [hlam, p13108_0]
                        · have p13108_0 := h13108c.1
                          have p13108_1 := h13108c.2.1
                          have p13108_2 := h13108c.2.2.1
                          have p13108_3 := h13108c.2.2.2
                          linarith only [h7360, hlam, p13108_1]
                        · have p13108_0 := h13108c.1
                          have p13108_1 := h13108c.2.1
                          have p13108_2 := h13108c.2.2.1
                          have p13108_3 := h13108c.2.2.2
                          linarith only [h11550, h13098, h13100, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13108_1]
                        · have p13108_0 := h13108c.1
                          have p13108_1 := h13108c.2.1
                          have p13108_2 := h13108c.2.2.1
                          have p13108_3 := h13108c.2.2.2
                          linarith only [h11550, hlam, p13108_0]
                        · have p13108_0 := h13108c.1
                          have p13108_1 := h13108c.2.1
                          have p13108_2 := h13108c.2.2.1
                          have p13108_3 := h13108c.2.2.2
                          linarith only [h11550, h13098, h13100, h13107, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p13108_1]
                        · have p13108_0 := h13108c.1
                          have p13108_1 := h13108c.2.1
                          have p13108_2 := h13108c.2.2.1
                          have p13108_3 := h13108c.2.2.2
                          rcases p13108_3 (m.d 0 3) (by simp) with h13114 | h13114
                          · linarith only [h13114, h7360, hlam]
                          · rcases p13108_3 (m.d 1 3) (by simp) with h13116 | h13116
                            · rcases p13108_3 (m.d 2 3) (by simp) with h13117 | h13117
                              · linarith only [h13098, h13117, hlam]
                              · rcases p13108_3 (m.d 3 4) (by simp) with h13119 | h13119
                                · linarith only [h13100, h13119, hlam]
                                · linarith only [h11550, h13119, hlam]
                            · linarith only [h13116, h7360, hlam]
                        · have p13108_0 := h13108c.1
                          have p13108_1 := h13108c.2.1
                          have p13108_2 := h13108c.2.2.1
                          have p13108_3 := h13108c.2.2.2
                          linarith only [hlam, p13108_0]
                        · have p13108_0 := h13108c.1
                          have p13108_1 := h13108c.2.1
                          have p13108_2 := h13108c.2.2.1
                          have p13108_3 := h13108c.2.2.2
                          rcases p13108_3 (m.d 0 3) (by simp) with h13124 | h13124
                          · linarith only [h13124, h7360, hlam]
                          · linarith only [h11548, h13124, hlam]
                        · have p13108_0 := h13108c.1
                          have p13108_1 := h13108c.2.1
                          have p13108_2 := h13108c.2.2.1
                          have p13108_3 := h13108c.2.2.2
                          linarith only [h11550, h13098, h7360, hc01, hc12, hlam, hphi, p13108_1]
                        · have p13108_0 := h13108c.1
                          have p13108_1 := h13108c.2.1
                          have p13108_2 := h13108c.2.2.1
                          have p13108_3 := h13108c.2.2.2
                          linarith only [h11548, h11550, h13100, h13105, hlam, p13108_2]
                        · have p13108_0 := h13108c.1
                          have p13108_1 := h13108c.2.1
                          have p13108_2 := h13108c.2.2.1
                          have p13108_3 := h13108c.2.2.2
                          linarith only [h11548, hlam, p13108_0]
                        · have p13108_0 := h13108c.1
                          have p13108_1 := h13108c.2.1
                          have p13108_2 := h13108c.2.2.1
                          have p13108_3 := h13108c.2.2.2
                          linarith only [h13098, hlam, p13108_0]
                        · have p13108_0 := h13108c.1
                          have p13108_1 := h13108c.2.1
                          have p13108_2 := h13108c.2.2.1
                          have p13108_3 := h13108c.2.2.2
                          linarith only [hlam, p13108_0]
                        · have p13108_0 := h13108c.1
                          have p13108_1 := h13108c.2.1
                          have p13108_2 := h13108c.2.2.1
                          have p13108_3 := h13108c.2.2.2
                          linarith only [h13103, hlam, p13108_0]
                        · have p13108_0 := h13108c.1
                          have p13108_1 := h13108c.2.1
                          have p13108_2 := h13108c.2.2.1
                          have p13108_3 := h13108c.2.2.2
                          linarith only [h11548, h11550, h13100, h13107, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p13108_1]
                        · have p13108_0 := h13108c.1
                          have p13108_1 := h13108c.2.1
                          have p13108_2 := h13108c.2.2.1
                          have p13108_3 := h13108c.2.2.2
                          linarith only [h13100, h7360, hc01, hc13, hlam, hphi, p13108_1]
                        · have p13108_0 := h13108c.1
                          have p13108_1 := h13108c.2.1
                          have p13108_2 := h13108c.2.2.1
                          have p13108_3 := h13108c.2.2.2
                          linarith only [h13100, hlam, p13108_0]
                        · have p13108_0 := h13108c.1
                          have p13108_1 := h13108c.2.1
                          have p13108_2 := h13108c.2.2.1
                          have p13108_3 := h13108c.2.2.2
                          linarith only [h13098, h13100, h13105, h13107, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p13108_1]
                        · have p13108_0 := h13108c.1
                          have p13108_1 := h13108c.2.1
                          have p13108_2 := h13108c.2.2.1
                          have p13108_3 := h13108c.2.2.2
                          linarith only [hlam, p13108_0]
                        · have p13108_0 := h13108c.1
                          have p13108_1 := h13108c.2.1
                          have p13108_2 := h13108c.2.2.1
                          have p13108_3 := h13108c.2.2.2
                          rcases p13108_3 (m.d 0 3) (by simp) with h13138 | h13138
                          · linarith only [h11550, h13138, hlam]
                          · linarith only [h13096, h13138, hlam]
                        · have p13108_0 := h13108c.1
                          have p13108_1 := h13108c.2.1
                          have p13108_2 := h13108c.2.2.1
                          have p13108_3 := h13108c.2.2.2
                          linarith only [h13096, hlam, p13108_0]
                        · have p13108_0 := h13108c.1
                          have p13108_1 := h13108c.2.1
                          have p13108_2 := h13108c.2.2.1
                          have p13108_3 := h13108c.2.2.2
                          linarith only [h13101, hlam, p13108_0]
                        · have p13108_0 := h13108c.1
                          have p13108_1 := h13108c.2.1
                          have p13108_2 := h13108c.2.2.1
                          have p13108_3 := h13108c.2.2.2
                          linarith only [h13105, hlam, p13108_0]
                        · have p13108_0 := h13108c.1
                          have p13108_1 := h13108c.2.1
                          have p13108_2 := h13108c.2.2.1
                          have p13108_3 := h13108c.2.2.2
                          linarith only [h13107, hlam, p13108_0]
                        · have p13108_0 := h13108c.1
                          have p13108_1 := h13108c.2.1
                          have p13108_2 := h13108c.2.2.1
                          have p13108_3 := h13108c.2.2.2
                          linarith only [hlam, p13108_0]
                      · linarith only [h11550, h13097, h13107, hlam]
                    · linarith only [h11550, h13096, h13097, h13098, h13100, h13103, h13105, h13106, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h11550, h13096, h13098, h13100, h13105, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h11550, h13096, h13097, h13098, h13100, h13102, h8811, hc01, hc12, hlam, hphi]
            · linarith only [h11550, h13096, h13100, h13101, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h13151 | h13151
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13152 | h13152
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13153 | h13153
                · linarith only [h13100, h13153, h7360, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13155 | h13155
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13156 | h13156
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13157 | h13157
                      · rcases h3bigk with h13158c | h13158c | h13158c | h13158c | h13158c | h13158c | h13158c | h13158c | h13158c | h13158c | h13158c | h13158c | h13158c | h13158c | h13158c | h13158c | h13158c | h13158c | h13158c | h13158c | h13158c | h13158c | h13158c | h13158c | h13158c
                        · have p13158_0 := h13158c.1
                          have p13158_1 := h13158c.2.1
                          have p13158_2 := h13158c.2.2.1
                          have p13158_3 := h13158c.2.2.2
                          linarith only [hlam, p13158_0]
                        · have p13158_0 := h13158c.1
                          have p13158_1 := h13158c.2.1
                          have p13158_2 := h13158c.2.2.1
                          have p13158_3 := h13158c.2.2.2
                          linarith only [h7360, hlam, p13158_1]
                        · have p13158_0 := h13158c.1
                          have p13158_1 := h13158c.2.1
                          have p13158_2 := h13158c.2.2.1
                          have p13158_3 := h13158c.2.2.2
                          linarith only [h13100, h13155, h13157, h7360, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13158_1]
                        · have p13158_0 := h13158c.1
                          have p13158_1 := h13158c.2.1
                          have p13158_2 := h13158c.2.2.1
                          have p13158_3 := h13158c.2.2.2
                          linarith only [h11550, hlam, p13158_0]
                        · have p13158_0 := h13158c.1
                          have p13158_1 := h13158c.2.1
                          have p13158_2 := h13158c.2.2.1
                          have p13158_3 := h13158c.2.2.2
                          rcases p13158_3 (m.d 0 3) (by simp) with h13163 | h13163
                          · rcases p13158_3 (m.d 1 3) (by simp) with h13164 | h13164
                            · rcases p13158_3 (m.d 2 3) (by simp) with h13165 | h13165
                              · linarith only [h11548, h13165, hlam]
                              · linarith only [h13155, h13165, hlam]
                            · linarith only [h13151, h13164, hlam]
                          · linarith only [h13163, hlam, p13158_0]
                        · have p13158_0 := h13158c.1
                          have p13158_1 := h13158c.2.1
                          have p13158_2 := h13158c.2.2.1
                          have p13158_3 := h13158c.2.2.2
                          linarith only [h13100, hc03, hc34, hlam, hphi, p13158_1]
                        · have p13158_0 := h13158c.1
                          have p13158_1 := h13158c.2.1
                          have p13158_2 := h13158c.2.2.1
                          have p13158_3 := h13158c.2.2.2
                          linarith only [hlam, p13158_0]
                        · have p13158_0 := h13158c.1
                          have p13158_1 := h13158c.2.1
                          have p13158_2 := h13158c.2.2.1
                          have p13158_3 := h13158c.2.2.2
                          linarith only [h13100, h13155, h13157, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13158_1]
                        · have p13158_0 := h13158c.1
                          have p13158_1 := h13158c.2.1
                          have p13158_2 := h13158c.2.2.1
                          have p13158_3 := h13158c.2.2.2
                          linarith only [h13100, hlam, p13158_0]
                        · have p13158_0 := h13158c.1
                          have p13158_1 := h13158c.2.1
                          have p13158_2 := h13158c.2.2.1
                          have p13158_3 := h13158c.2.2.2
                          rcases p13158_3 (m.d 0 3) (by simp) with h13174 | h13174
                          · linarith only [h13174, h7360, hlam]
                          · linarith only [h13096, h13174, hlam]
                        · have p13158_0 := h13158c.1
                          have p13158_1 := h13158c.2.1
                          have p13158_2 := h13158c.2.2.1
                          have p13158_3 := h13158c.2.2.2
                          linarith only [h11548, hlam, p13158_0]
                        · have p13158_0 := h13158c.1
                          have p13158_1 := h13158c.2.1
                          have p13158_2 := h13158c.2.2.1
                          have p13158_3 := h13158c.2.2.2
                          linarith only [h13098, hlam, p13158_0]
                        · have p13158_0 := h13158c.1
                          have p13158_1 := h13158c.2.1
                          have p13158_2 := h13158c.2.2.1
                          have p13158_3 := h13158c.2.2.2
                          linarith only [hlam, p13158_0]
                        · have p13158_0 := h13158c.1
                          have p13158_1 := h13158c.2.1
                          have p13158_2 := h13158c.2.2.1
                          have p13158_3 := h13158c.2.2.2
                          linarith only [h13153, hlam, p13158_0]
                        · have p13158_0 := h13158c.1
                          have p13158_1 := h13158c.2.1
                          have p13158_2 := h13158c.2.2.1
                          have p13158_3 := h13158c.2.2.2
                          rcases p13158_3 (m.d 0 3) (by simp) with h13181 | h13181
                          · rcases p13158_3 (m.d 1 3) (by simp) with h13182 | h13182
                            · rcases p13158_3 (m.d 2 3) (by simp) with h13183 | h13183
                              · rcases p13158_3 (m.d 3 4) (by simp) with h13184 | h13184
                                · rcases p13158_3 (m.d 3 5) (by simp) with h13185 | h13185
                                  · linarith only [h13185, hlam, p13158_0]
                                  · rcases h4bigk with h13187c | h13187c | h13187c | h13187c | h13187c | h13187c | h13187c | h13187c | h13187c | h13187c | h13187c | h13187c | h13187c | h13187c | h13187c | h13187c | h13187c | h13187c | h13187c | h13187c | h13187c | h13187c | h13187c | h13187c | h13187c
                                    · have p13187_0 := h13187c.1
                                      have p13187_1 := h13187c.2.1
                                      have p13187_2 := h13187c.2.2.1
                                      have p13187_3 := h13187c.2.2.2
                                      linarith only [hlam, p13187_0]
                                    · have p13187_0 := h13187c.1
                                      have p13187_1 := h13187c.2.1
                                      have p13187_2 := h13187c.2.2.1
                                      have p13187_3 := h13187c.2.2.2
                                      linarith only [h8811, hlam, p13187_0]
                                    · have p13187_0 := h13187c.1
                                      have p13187_1 := h13187c.2.1
                                      have p13187_2 := h13187c.2.2.1
                                      have p13187_3 := h13187c.2.2.2
                                      linarith only [h13100, h13153, h13157, h8811, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13158_1, p13187_1]
                                    · have p13187_0 := h13187c.1
                                      have p13187_1 := h13187c.2.1
                                      have p13187_2 := h13187c.2.2.1
                                      have p13187_3 := h13187c.2.2.2
                                      linarith only [h11550, hlam, p13187_0]
                                    · have p13187_0 := h13187c.1
                                      have p13187_1 := h13187c.2.1
                                      have p13187_2 := h13187c.2.2.1
                                      have p13187_3 := h13187c.2.2.2
                                      rcases p13187_3 (m.d 0 4) (by simp) with h13192 | h13192
                                      · rcases p13187_3 (m.d 1 4) (by simp) with h13193 | h13193
                                        · rcases p13187_3 (m.d 2 4) (by simp) with h13194 | h13194
                                          · linarith only [h11549, h13194, hlam]
                                          · linarith only [h13156, h13194, hlam]
                                        · linarith only [h13152, h13193, hlam]
                                      · linarith only [h13192, hlam, p13187_0]
                                    · have p13187_0 := h13187c.1
                                      have p13187_1 := h13187c.2.1
                                      have p13187_2 := h13187c.2.2.1
                                      have p13187_3 := h13187c.2.2.2
                                      linarith only [h13100, h8811, hc01, hc34, hlam, hphi, ht12, ht23, p13187_1]
                                    · have p13187_0 := h13187c.1
                                      have p13187_1 := h13187c.2.1
                                      have p13187_2 := h13187c.2.2.1
                                      have p13187_3 := h13187c.2.2.2
                                      linarith only [hlam, p13187_0]
                                    · have p13187_0 := h13187c.1
                                      have p13187_1 := h13187c.2.1
                                      have p13187_2 := h13187c.2.2.1
                                      have p13187_3 := h13187c.2.2.2
                                      linarith only [h13100, h13153, h13157, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13158_1, p13187_1]
                                    · have p13187_0 := h13187c.1
                                      have p13187_1 := h13187c.2.1
                                      have p13187_2 := h13187c.2.2.1
                                      have p13187_3 := h13187c.2.2.2
                                      linarith only [h13100, hlam, p13187_1]
                                    · have p13187_0 := h13187c.1
                                      have p13187_1 := h13187c.2.1
                                      have p13187_2 := h13187c.2.2.1
                                      have p13187_3 := h13187c.2.2.2
                                      rcases p13187_3 (m.d 0 4) (by simp) with h13203 | h13203
                                      · linarith only [h13203, h8811, hlam]
                                      · linarith only [h13097, h13203, hlam]
                                    · have p13187_0 := h13187c.1
                                      have p13187_1 := h13187c.2.1
                                      have p13187_2 := h13187c.2.2.1
                                      have p13187_3 := h13187c.2.2.2
                                      linarith only [h11549, hlam, p13187_1]
                                    · have p13187_0 := h13187c.1
                                      have p13187_1 := h13187c.2.1
                                      have p13187_2 := h13187c.2.2.1
                                      have p13187_3 := h13187c.2.2.2
                                      linarith only [h13099, hlam, p13187_1]
                                    · have p13187_0 := h13187c.1
                                      have p13187_1 := h13187c.2.1
                                      have p13187_2 := h13187c.2.2.1
                                      have p13187_3 := h13187c.2.2.2
                                      linarith only [hlam, p13187_0]
                                    · have p13187_0 := h13187c.1
                                      have p13187_1 := h13187c.2.1
                                      have p13187_2 := h13187c.2.2.1
                                      have p13187_3 := h13187c.2.2.2
                                      linarith only [h13153, hlam, p13187_1]
                                    · have p13187_0 := h13187c.1
                                      have p13187_1 := h13187c.2.1
                                      have p13187_2 := h13187c.2.2.1
                                      have p13187_3 := h13187c.2.2.2
                                      linarith only [h0, h11549, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p13187_1]
                                    · have p13187_0 := h13187c.1
                                      have p13187_1 := h13187c.2.1
                                      have p13187_2 := h13187c.2.2.1
                                      have p13187_3 := h13187c.2.2.2
                                      linarith only [h8811, hc01, hc34, hlam, hphi, ht12, ht23, p13187_1]
                                    · have p13187_0 := h13187c.1
                                      have p13187_1 := h13187c.2.1
                                      have p13187_2 := h13187c.2.2.1
                                      have p13187_3 := h13187c.2.2.2
                                      linarith only [h8811, hc01, hc34, hlam, hphi, ht12, ht23, p13187_1]
                                    · have p13187_0 := h13187c.1
                                      have p13187_1 := h13187c.2.1
                                      have p13187_2 := h13187c.2.2.1
                                      have p13187_3 := h13187c.2.2.2
                                      linarith only [h13153, h13157, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p13158_1, p13187_1]
                                    · have p13187_0 := h13187c.1
                                      have p13187_1 := h13187c.2.1
                                      have p13187_2 := h13187c.2.2.1
                                      have p13187_3 := h13187c.2.2.2
                                      linarith only [hlam, p13187_0]
                                    · have p13187_0 := h13187c.1
                                      have p13187_1 := h13187c.2.1
                                      have p13187_2 := h13187c.2.2.1
                                      have p13187_3 := h13187c.2.2.2
                                      rcases p13187_3 (m.d 0 4) (by simp) with h13215 | h13215
                                      · linarith only [h11550, h13215, hlam]
                                      · linarith only [h13097, h13215, hlam]
                                    · have p13187_0 := h13187c.1
                                      have p13187_1 := h13187c.2.1
                                      have p13187_2 := h13187c.2.2.1
                                      have p13187_3 := h13187c.2.2.2
                                      linarith only [h13097, hlam, p13187_0]
                                    · have p13187_0 := h13187c.1
                                      have p13187_1 := h13187c.2.1
                                      have p13187_2 := h13187c.2.2.1
                                      have p13187_3 := h13187c.2.2.2
                                      linarith only [h13152, hlam, p13187_0]
                                    · have p13187_0 := h13187c.1
                                      have p13187_1 := h13187c.2.1
                                      have p13187_2 := h13187c.2.2.1
                                      have p13187_3 := h13187c.2.2.2
                                      linarith only [h13156, hlam, p13187_0]
                                    · have p13187_0 := h13187c.1
                                      have p13187_1 := h13187c.2.1
                                      have p13187_2 := h13187c.2.2.1
                                      have p13187_3 := h13187c.2.2.2
                                      linarith only [h13157, hlam, p13187_0]
                                    · have p13187_0 := h13187c.1
                                      have p13187_1 := h13187c.2.1
                                      have p13187_2 := h13187c.2.2.1
                                      have p13187_3 := h13187c.2.2.2
                                      linarith only [hlam, p13187_0]
                                · linarith only [h13157, h13184, hlam]
                              · linarith only [h13183, hlam, p13158_0]
                            · linarith only [h13151, h13182, hlam]
                          · linarith only [h13096, h13181, hlam]
                        · have p13158_0 := h13158c.1
                          have p13158_1 := h13158c.2.1
                          have p13158_2 := h13158c.2.2.1
                          have p13158_3 := h13158c.2.2.2
                          rcases p13158_3 (m.d 0 3) (by simp) with h13227 | h13227
                          · linarith only [h13227, hlam, p13158_0]
                          · rcases p13158_3 (m.d 1 3) (by simp) with h13229 | h13229
                            · linarith only [h13100, h13229, hlam]
                            · linarith only [h13229, h7360, hlam]
                        · have p13158_0 := h13158c.1
                          have p13158_1 := h13158c.2.1
                          have p13158_2 := h13158c.2.2.1
                          have p13158_3 := h13158c.2.2.2
                          linarith only [h10295, h13151, hc01, hc34, hlam, hphi, ht12, ht23, p13158_1]
                        · have p13158_0 := h13158c.1
                          have p13158_1 := h13158c.2.1
                          have p13158_2 := h13158c.2.2.1
                          have p13158_3 := h13158c.2.2.2
                          rcases p13158_3 (m.d 0 3) (by simp) with h13233 | h13233
                          · linarith only [h11550, h13233, hlam]
                          · linarith only [h11548, h13233, hlam]
                        · have p13158_0 := h13158c.1
                          have p13158_1 := h13158c.2.1
                          have p13158_2 := h13158c.2.2.1
                          have p13158_3 := h13158c.2.2.2
                          linarith only [hlam, p13158_0]
                        · have p13158_0 := h13158c.1
                          have p13158_1 := h13158c.2.1
                          have p13158_2 := h13158c.2.2.1
                          have p13158_3 := h13158c.2.2.2
                          rcases p13158_3 (m.d 0 3) (by simp) with h13237 | h13237
                          · linarith only [h11550, h13237, hlam]
                          · linarith only [h13096, h13237, hlam]
                        · have p13158_0 := h13158c.1
                          have p13158_1 := h13158c.2.1
                          have p13158_2 := h13158c.2.2.1
                          have p13158_3 := h13158c.2.2.2
                          linarith only [h13096, hlam, p13158_0]
                        · have p13158_0 := h13158c.1
                          have p13158_1 := h13158c.2.1
                          have p13158_2 := h13158c.2.2.1
                          have p13158_3 := h13158c.2.2.2
                          linarith only [h13151, hlam, p13158_0]
                        · have p13158_0 := h13158c.1
                          have p13158_1 := h13158c.2.1
                          have p13158_2 := h13158c.2.2.1
                          have p13158_3 := h13158c.2.2.2
                          linarith only [h13155, hlam, p13158_0]
                        · have p13158_0 := h13158c.1
                          have p13158_1 := h13158c.2.1
                          have p13158_2 := h13158c.2.2.1
                          have p13158_3 := h13158c.2.2.2
                          linarith only [h13157, hlam, p13158_0]
                        · have p13158_0 := h13158c.1
                          have p13158_1 := h13158c.2.1
                          have p13158_2 := h13158c.2.2.1
                          have p13158_3 := h13158c.2.2.2
                          linarith only [hlam, p13158_0]
                      · linarith only [h0, h11548, h11549, h11550, h13097, h13155, h13157, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h13153, h13155, h13156, hlam]
                  · linarith only [h11550, h13096, h13155, hc23, hc34, hlam, hphi]
              · linarith only [h13096, h13097, h13100, h13152, h7360, h8811, hc01, hc34, hlam, hphi, ht12, ht23]
            · linarith only [h13096, h13151, h7360, hlam]
        · linarith only [h0, h11549, h13099, hlam]
      · linarith only [h0, h11548, h13098, hlam]
    · linarith only [h11550, h13096, h13097, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h13253 | h13253
    · rcases m.htr 1 2 3 (by decide) (by decide) with h13254 | h13254
      · rcases m.htr 1 2 4 (by decide) (by decide) with h13255 | h13255
        · rcases m.htr 1 3 4 (by decide) (by decide) with h13256 | h13256
          · rcases m.htr 1 3 5 (by decide) (by decide) with h13257 | h13257
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13258 | h13258
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13259 | h13259
                · linarith only [h11548, h11550, h13259, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13261 | h13261
                  · linarith only [h11548, h13096, h13261, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13263 | h13263
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13264 | h13264
                      · rcases h3bigk with h13265c | h13265c | h13265c | h13265c | h13265c | h13265c | h13265c | h13265c | h13265c | h13265c | h13265c | h13265c | h13265c | h13265c | h13265c | h13265c | h13265c | h13265c | h13265c | h13265c | h13265c | h13265c | h13265c | h13265c | h13265c
                        · have p13265_0 := h13265c.1
                          have p13265_1 := h13265c.2.1
                          have p13265_2 := h13265c.2.2.1
                          have p13265_3 := h13265c.2.2.2
                          linarith only [hlam, p13265_0]
                        · have p13265_0 := h13265c.1
                          have p13265_1 := h13265c.2.1
                          have p13265_2 := h13265c.2.2.1
                          have p13265_3 := h13265c.2.2.2
                          linarith only [h7360, hlam, p13265_1]
                        · have p13265_0 := h13265c.1
                          have p13265_1 := h13265c.2.1
                          have p13265_2 := h13265c.2.2.1
                          have p13265_3 := h13265c.2.2.2
                          linarith only [h13096, h13264, hc23, hc34, hlam, hphi, p13265_1]
                        · have p13265_0 := h13265c.1
                          have p13265_1 := h13265c.2.1
                          have p13265_2 := h13265c.2.2.1
                          have p13265_3 := h13265c.2.2.2
                          linarith only [h11550, hlam, p13265_0]
                        · have p13265_0 := h13265c.1
                          have p13265_1 := h13265c.2.1
                          have p13265_2 := h13265c.2.2.1
                          have p13265_3 := h13265c.2.2.2
                          linarith only [h13096, hlam, p13265_0]
                        · have p13265_0 := h13265c.1
                          have p13265_1 := h13265c.2.1
                          have p13265_2 := h13265c.2.2.1
                          have p13265_3 := h13265c.2.2.2
                          rcases p13265_3 (m.d 0 3) (by simp) with h13271 | h13271
                          · linarith only [h13271, h7360, hlam]
                          · rcases p13265_3 (m.d 1 3) (by simp) with h13273 | h13273
                            · rcases p13265_3 (m.d 2 3) (by simp) with h13274 | h13274
                              · linarith only [h13254, h13274, hlam]
                              · rcases p13265_3 (m.d 3 4) (by simp) with h13276 | h13276
                                · linarith only [h13256, h13276, hlam]
                                · linarith only [h11550, h13276, hlam]
                            · linarith only [h13273, h7360, hlam]
                        · have p13265_0 := h13265c.1
                          have p13265_1 := h13265c.2.1
                          have p13265_2 := h13265c.2.2.1
                          have p13265_3 := h13265c.2.2.2
                          linarith only [hlam, p13265_0]
                        · have p13265_0 := h13265c.1
                          have p13265_1 := h13265c.2.1
                          have p13265_2 := h13265c.2.2.1
                          have p13265_3 := h13265c.2.2.2
                          rcases p13265_3 (m.d 0 3) (by simp) with h13281 | h13281
                          · linarith only [h13281, h7360, hlam]
                          · linarith only [h11548, h13281, hlam]
                        · have p13265_0 := h13265c.1
                          have p13265_1 := h13265c.2.1
                          have p13265_2 := h13265c.2.2.1
                          have p13265_3 := h13265c.2.2.2
                          linarith only [h13096, h13254, h13264, h7360, hc01, hc12, hlam, hphi, p13265_1]
                        · have p13265_0 := h13265c.1
                          have p13265_1 := h13265c.2.1
                          have p13265_2 := h13265c.2.2.1
                          have p13265_3 := h13265c.2.2.2
                          linarith only [h13096, h13254, h7360, hc01, hc12, hlam, hphi, p13265_1]
                        · have p13265_0 := h13265c.1
                          have p13265_1 := h13265c.2.1
                          have p13265_2 := h13265c.2.2.1
                          have p13265_3 := h13265c.2.2.2
                          linarith only [h11548, hlam, p13265_0]
                        · have p13265_0 := h13265c.1
                          have p13265_1 := h13265c.2.1
                          have p13265_2 := h13265c.2.2.1
                          have p13265_3 := h13265c.2.2.2
                          linarith only [h13254, hlam, p13265_0]
                        · have p13265_0 := h13265c.1
                          have p13265_1 := h13265c.2.1
                          have p13265_2 := h13265c.2.2.1
                          have p13265_3 := h13265c.2.2.2
                          linarith only [hlam, p13265_0]
                        · have p13265_0 := h13265c.1
                          have p13265_1 := h13265c.2.1
                          have p13265_2 := h13265c.2.2.1
                          have p13265_3 := h13265c.2.2.2
                          linarith only [h13259, hlam, p13265_0]
                        · have p13265_0 := h13265c.1
                          have p13265_1 := h13265c.2.1
                          have p13265_2 := h13265c.2.2.1
                          have p13265_3 := h13265c.2.2.2
                          linarith only [h13261, hlam, p13265_0]
                        · have p13265_0 := h13265c.1
                          have p13265_1 := h13265c.2.1
                          have p13265_2 := h13265c.2.2.1
                          have p13265_3 := h13265c.2.2.2
                          linarith only [h13254, h13256, h7360, hc01, hc12, hlam, hphi, p13265_1]
                        · have p13265_0 := h13265c.1
                          have p13265_1 := h13265c.2.1
                          have p13265_2 := h13265c.2.2.1
                          have p13265_3 := h13265c.2.2.2
                          linarith only [h13256, hlam, p13265_0]
                        · have p13265_0 := h13265c.1
                          have p13265_1 := h13265c.2.1
                          have p13265_2 := h13265c.2.2.1
                          have p13265_3 := h13265c.2.2.2
                          rcases p13265_3 (m.d 0 3) (by simp) with h13293 | h13293
                          · linarith only [h11550, h13293, hlam]
                          · linarith only [h11548, h13293, hlam]
                        · have p13265_0 := h13265c.1
                          have p13265_1 := h13265c.2.1
                          have p13265_2 := h13265c.2.2.1
                          have p13265_3 := h13265c.2.2.2
                          linarith only [hlam, p13265_0]
                        · have p13265_0 := h13265c.1
                          have p13265_1 := h13265c.2.1
                          have p13265_2 := h13265c.2.2.1
                          have p13265_3 := h13265c.2.2.2
                          linarith only [h13096, h13254, h13256, h7360, hc01, hc12, hlam, hphi, p13265_1]
                        · have p13265_0 := h13265c.1
                          have p13265_1 := h13265c.2.1
                          have p13265_2 := h13265c.2.2.1
                          have p13265_3 := h13265c.2.2.2
                          linarith only [h13254, h13257, h7360, hc01, hc12, hlam, hphi, p13265_1]
                        · have p13265_0 := h13265c.1
                          have p13265_1 := h13265c.2.1
                          have p13265_2 := h13265c.2.2.1
                          have p13265_3 := h13265c.2.2.2
                          linarith only [h13257, hlam, p13265_0]
                        · have p13265_0 := h13265c.1
                          have p13265_1 := h13265c.2.1
                          have p13265_2 := h13265c.2.2.1
                          have p13265_3 := h13265c.2.2.2
                          rcases p13265_3 (m.d 0 3) (by simp) with h13300 | h13300
                          · linarith only [h13096, h13300, hlam]
                          · linarith only [h11548, h13300, hlam]
                        · have p13265_0 := h13265c.1
                          have p13265_1 := h13265c.2.1
                          have p13265_2 := h13265c.2.2.1
                          have p13265_3 := h13265c.2.2.2
                          linarith only [h13264, hlam, p13265_0]
                        · have p13265_0 := h13265c.1
                          have p13265_1 := h13265c.2.1
                          have p13265_2 := h13265c.2.2.1
                          have p13265_3 := h13265c.2.2.2
                          linarith only [hlam, p13265_0]
                      · linarith only [h11550, h13253, h13264, h7360, h8811, hc01, hc14, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13306 | h13306
                      · rcases h3bigk with h13307c | h13307c | h13307c | h13307c | h13307c | h13307c | h13307c | h13307c | h13307c | h13307c | h13307c | h13307c | h13307c | h13307c | h13307c | h13307c | h13307c | h13307c | h13307c | h13307c | h13307c | h13307c | h13307c | h13307c | h13307c
                        · have p13307_0 := h13307c.1
                          have p13307_1 := h13307c.2.1
                          have p13307_2 := h13307c.2.2.1
                          have p13307_3 := h13307c.2.2.2
                          linarith only [hlam, p13307_0]
                        · have p13307_0 := h13307c.1
                          have p13307_1 := h13307c.2.1
                          have p13307_2 := h13307c.2.2.1
                          have p13307_3 := h13307c.2.2.2
                          linarith only [h7360, hlam, p13307_1]
                        · have p13307_0 := h13307c.1
                          have p13307_1 := h13307c.2.1
                          have p13307_2 := h13307c.2.2.1
                          have p13307_3 := h13307c.2.2.2
                          linarith only [h11550, h13254, h13256, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13307_1]
                        · have p13307_0 := h13307c.1
                          have p13307_1 := h13307c.2.1
                          have p13307_2 := h13307c.2.2.1
                          have p13307_3 := h13307c.2.2.2
                          linarith only [h11550, hlam, p13307_0]
                        · have p13307_0 := h13307c.1
                          have p13307_1 := h13307c.2.1
                          have p13307_2 := h13307c.2.2.1
                          have p13307_3 := h13307c.2.2.2
                          linarith only [h13096, hlam, p13307_0]
                        · have p13307_0 := h13307c.1
                          have p13307_1 := h13307c.2.1
                          have p13307_2 := h13307c.2.2.1
                          have p13307_3 := h13307c.2.2.2
                          rcases p13307_3 (m.d 0 3) (by simp) with h13313 | h13313
                          · linarith only [h13313, h7360, hlam]
                          · rcases p13307_3 (m.d 1 3) (by simp) with h13315 | h13315
                            · rcases p13307_3 (m.d 2 3) (by simp) with h13316 | h13316
                              · linarith only [h13254, h13316, hlam]
                              · rcases p13307_3 (m.d 3 4) (by simp) with h13318 | h13318
                                · linarith only [h13256, h13318, hlam]
                                · linarith only [h11550, h13318, hlam]
                            · linarith only [h13315, h7360, hlam]
                        · have p13307_0 := h13307c.1
                          have p13307_1 := h13307c.2.1
                          have p13307_2 := h13307c.2.2.1
                          have p13307_3 := h13307c.2.2.2
                          linarith only [hlam, p13307_0]
                        · have p13307_0 := h13307c.1
                          have p13307_1 := h13307c.2.1
                          have p13307_2 := h13307c.2.2.1
                          have p13307_3 := h13307c.2.2.2
                          linarith only [h11550, h13253, h13256, h13259, h13263, hlam, p13307_2]
                        · have p13307_0 := h13307c.1
                          have p13307_1 := h13307c.2.1
                          have p13307_2 := h13307c.2.2.1
                          have p13307_3 := h13307c.2.2.2
                          linarith only [h11550, h13254, h7360, hc01, hc12, hlam, hphi, p13307_1]
                        · have p13307_0 := h13307c.1
                          have p13307_1 := h13307c.2.1
                          have p13307_2 := h13307c.2.2.1
                          have p13307_3 := h13307c.2.2.2
                          linarith only [h13096, h13254, h7360, hc01, hc12, hlam, hphi, p13307_1]
                        · have p13307_0 := h13307c.1
                          have p13307_1 := h13307c.2.1
                          have p13307_2 := h13307c.2.2.1
                          have p13307_3 := h13307c.2.2.2
                          linarith only [h11548, hlam, p13307_0]
                        · have p13307_0 := h13307c.1
                          have p13307_1 := h13307c.2.1
                          have p13307_2 := h13307c.2.2.1
                          have p13307_3 := h13307c.2.2.2
                          linarith only [h13254, hlam, p13307_0]
                        · have p13307_0 := h13307c.1
                          have p13307_1 := h13307c.2.1
                          have p13307_2 := h13307c.2.2.1
                          have p13307_3 := h13307c.2.2.2
                          linarith only [hlam, p13307_0]
                        · have p13307_0 := h13307c.1
                          have p13307_1 := h13307c.2.1
                          have p13307_2 := h13307c.2.2.1
                          have p13307_3 := h13307c.2.2.2
                          linarith only [h13259, hlam, p13307_0]
                        · have p13307_0 := h13307c.1
                          have p13307_1 := h13307c.2.1
                          have p13307_2 := h13307c.2.2.1
                          have p13307_3 := h13307c.2.2.2
                          linarith only [h13261, hlam, p13307_0]
                        · have p13307_0 := h13307c.1
                          have p13307_1 := h13307c.2.1
                          have p13307_2 := h13307c.2.2.1
                          have p13307_3 := h13307c.2.2.2
                          linarith only [h13254, h13256, h7360, hc01, hc12, hlam, hphi, p13307_1]
                        · have p13307_0 := h13307c.1
                          have p13307_1 := h13307c.2.1
                          have p13307_2 := h13307c.2.2.1
                          have p13307_3 := h13307c.2.2.2
                          linarith only [h13256, hlam, p13307_0]
                        · have p13307_0 := h13307c.1
                          have p13307_1 := h13307c.2.1
                          have p13307_2 := h13307c.2.2.1
                          have p13307_3 := h13307c.2.2.2
                          rcases p13307_3 (m.d 0 3) (by simp) with h13333 | h13333
                          · linarith only [h11550, h13333, hlam]
                          · linarith only [h11548, h13333, hlam]
                        · have p13307_0 := h13307c.1
                          have p13307_1 := h13307c.2.1
                          have p13307_2 := h13307c.2.2.1
                          have p13307_3 := h13307c.2.2.2
                          linarith only [hlam, p13307_0]
                        · have p13307_0 := h13307c.1
                          have p13307_1 := h13307c.2.1
                          have p13307_2 := h13307c.2.2.1
                          have p13307_3 := h13307c.2.2.2
                          linarith only [h13096, h13254, h13256, h7360, hc01, hc12, hlam, hphi, p13307_1]
                        · have p13307_0 := h13307c.1
                          have p13307_1 := h13307c.2.1
                          have p13307_2 := h13307c.2.2.1
                          have p13307_3 := h13307c.2.2.2
                          linarith only [h13254, h13257, h7360, hc01, hc12, hlam, hphi, p13307_1]
                        · have p13307_0 := h13307c.1
                          have p13307_1 := h13307c.2.1
                          have p13307_2 := h13307c.2.2.1
                          have p13307_3 := h13307c.2.2.2
                          linarith only [h13257, hlam, p13307_0]
                        · have p13307_0 := h13307c.1
                          have p13307_1 := h13307c.2.1
                          have p13307_2 := h13307c.2.2.1
                          have p13307_3 := h13307c.2.2.2
                          rcases p13307_3 (m.d 0 3) (by simp) with h13340 | h13340
                          · linarith only [h13096, h13340, hlam]
                          · linarith only [h11548, h13340, hlam]
                        · have p13307_0 := h13307c.1
                          have p13307_1 := h13307c.2.1
                          have p13307_2 := h13307c.2.2.1
                          have p13307_3 := h13307c.2.2.2
                          linarith only [h13306, hlam, p13307_0]
                        · have p13307_0 := h13307c.1
                          have p13307_1 := h13307c.2.1
                          have p13307_2 := h13307c.2.2.1
                          have p13307_3 := h13307c.2.2.2
                          linarith only [hlam, p13307_0]
                      · linarith only [h11550, h13253, h13306, hlam]
              · linarith only [h11550, h13253, h13254, h13256, h13258, h8811, hc01, hc12, hlam, hphi]
            · linarith only [h11550, h13256, h13257, h7360, hc01, hc35, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h13348 | h13348
            · linarith only [h13096, h13256, h13348, h7360, hc01, hc34, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13350 | h13350
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13351 | h13351
                · linarith only [h13256, h13351, h7360, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13353 | h13353
                  · linarith only [h13348, h13353, h7360, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13355 | h13355
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13356 | h13356
                      · rcases h3bigk with h13357c | h13357c | h13357c | h13357c | h13357c | h13357c | h13357c | h13357c | h13357c | h13357c | h13357c | h13357c | h13357c | h13357c | h13357c | h13357c | h13357c | h13357c | h13357c | h13357c | h13357c | h13357c | h13357c | h13357c | h13357c
                        · have p13357_0 := h13357c.1
                          have p13357_1 := h13357c.2.1
                          have p13357_2 := h13357c.2.2.1
                          have p13357_3 := h13357c.2.2.2
                          linarith only [hlam, p13357_0]
                        · have p13357_0 := h13357c.1
                          have p13357_1 := h13357c.2.1
                          have p13357_2 := h13357c.2.2.1
                          have p13357_3 := h13357c.2.2.2
                          linarith only [h7360, hlam, p13357_1]
                        · have p13357_0 := h13357c.1
                          have p13357_1 := h13357c.2.1
                          have p13357_2 := h13357c.2.2.1
                          have p13357_3 := h13357c.2.2.2
                          linarith only [h13348, h13356, h7360, hc23, hc34, hlam, hphi, p13357_1]
                        · have p13357_0 := h13357c.1
                          have p13357_1 := h13357c.2.1
                          have p13357_2 := h13357c.2.2.1
                          have p13357_3 := h13357c.2.2.2
                          linarith only [h11550, hlam, p13357_0]
                        · have p13357_0 := h13357c.1
                          have p13357_1 := h13357c.2.1
                          have p13357_2 := h13357c.2.2.1
                          have p13357_3 := h13357c.2.2.2
                          linarith only [h13096, hlam, p13357_0]
                        · have p13357_0 := h13357c.1
                          have p13357_1 := h13357c.2.1
                          have p13357_2 := h13357c.2.2.1
                          have p13357_3 := h13357c.2.2.2
                          linarith only [h13348, h13356, hc03, hc34, hlam, hphi, p13357_1]
                        · have p13357_0 := h13357c.1
                          have p13357_1 := h13357c.2.1
                          have p13357_2 := h13357c.2.2.1
                          have p13357_3 := h13357c.2.2.2
                          linarith only [hlam, p13357_0]
                        · have p13357_0 := h13357c.1
                          have p13357_1 := h13357c.2.1
                          have p13357_2 := h13357c.2.2.1
                          have p13357_3 := h13357c.2.2.2
                          linarith only [h13348, h13356, hc23, hc34, hlam, hphi, p13357_1]
                        · have p13357_0 := h13357c.1
                          have p13357_1 := h13357c.2.1
                          have p13357_2 := h13357c.2.2.1
                          have p13357_3 := h13357c.2.2.2
                          linarith only [h13256, hlam, p13357_0]
                        · have p13357_0 := h13357c.1
                          have p13357_1 := h13357c.2.1
                          have p13357_2 := h13357c.2.2.1
                          have p13357_3 := h13357c.2.2.2
                          linarith only [h13348, hlam, p13357_0]
                        · have p13357_0 := h13357c.1
                          have p13357_1 := h13357c.2.1
                          have p13357_2 := h13357c.2.2.1
                          have p13357_3 := h13357c.2.2.2
                          linarith only [h11548, hlam, p13357_0]
                        · have p13357_0 := h13357c.1
                          have p13357_1 := h13357c.2.1
                          have p13357_2 := h13357c.2.2.1
                          have p13357_3 := h13357c.2.2.2
                          linarith only [h13254, hlam, p13357_0]
                        · have p13357_0 := h13357c.1
                          have p13357_1 := h13357c.2.1
                          have p13357_2 := h13357c.2.2.1
                          have p13357_3 := h13357c.2.2.2
                          linarith only [hlam, p13357_0]
                        · have p13357_0 := h13357c.1
                          have p13357_1 := h13357c.2.1
                          have p13357_2 := h13357c.2.2.1
                          have p13357_3 := h13357c.2.2.2
                          linarith only [h13351, hlam, p13357_0]
                        · have p13357_0 := h13357c.1
                          have p13357_1 := h13357c.2.1
                          have p13357_2 := h13357c.2.2.1
                          have p13357_3 := h13357c.2.2.2
                          linarith only [h13353, hlam, p13357_0]
                        · have p13357_0 := h13357c.1
                          have p13357_1 := h13357c.2.1
                          have p13357_2 := h13357c.2.2.1
                          have p13357_3 := h13357c.2.2.2
                          rcases p13357_3 (m.d 0 3) (by simp) with h13373 | h13373
                          · linarith only [h13373, hlam, p13357_0]
                          · rcases p13357_3 (m.d 1 3) (by simp) with h13375 | h13375
                            · linarith only [h13256, h13375, hlam]
                            · linarith only [h13375, h7360, hlam]
                        · have p13357_0 := h13357c.1
                          have p13357_1 := h13357c.2.1
                          have p13357_2 := h13357c.2.2.1
                          have p13357_3 := h13357c.2.2.2
                          linarith only [h7360, hc01, hc34, hlam, hphi, ht12, ht23, p13357_1]
                        · have p13357_0 := h13357c.1
                          have p13357_1 := h13357c.2.1
                          have p13357_2 := h13357c.2.2.1
                          have p13357_3 := h13357c.2.2.2
                          rcases p13357_3 (m.d 0 3) (by simp) with h13379 | h13379
                          · linarith only [h11550, h13379, hlam]
                          · linarith only [h11548, h13379, hlam]
                        · have p13357_0 := h13357c.1
                          have p13357_1 := h13357c.2.1
                          have p13357_2 := h13357c.2.2.1
                          have p13357_3 := h13357c.2.2.2
                          linarith only [hlam, p13357_0]
                        · have p13357_0 := h13357c.1
                          have p13357_1 := h13357c.2.1
                          have p13357_2 := h13357c.2.2.1
                          have p13357_3 := h13357c.2.2.2
                          linarith only [h13096, h7360, hc01, hc34, hlam, hphi, ht12, ht23, p13357_1]
                        · have p13357_0 := h13357c.1
                          have p13357_1 := h13357c.2.1
                          have p13357_2 := h13357c.2.2.1
                          have p13357_3 := h13357c.2.2.2
                          rcases p13357_3 (m.d 0 3) (by simp) with h13384 | h13384
                          · linarith only [h13384, hlam, p13357_0]
                          · rcases p13357_3 (m.d 1 3) (by simp) with h13386 | h13386
                            · linarith only [h13348, h13386, hlam]
                            · linarith only [h13386, h7360, hlam]
                        · have p13357_0 := h13357c.1
                          have p13357_1 := h13357c.2.1
                          have p13357_2 := h13357c.2.2.1
                          have p13357_3 := h13357c.2.2.2
                          linarith only [h7360, hc01, hc35, hlam, hphi, ht12, ht23, p13357_1]
                        · have p13357_0 := h13357c.1
                          have p13357_1 := h13357c.2.1
                          have p13357_2 := h13357c.2.2.1
                          have p13357_3 := h13357c.2.2.2
                          rcases p13357_3 (m.d 0 3) (by simp) with h13390 | h13390
                          · linarith only [h13096, h13390, hlam]
                          · linarith only [h11548, h13390, hlam]
                        · have p13357_0 := h13357c.1
                          have p13357_1 := h13357c.2.1
                          have p13357_2 := h13357c.2.2.1
                          have p13357_3 := h13357c.2.2.2
                          linarith only [h13356, hlam, p13357_0]
                        · have p13357_0 := h13357c.1
                          have p13357_1 := h13357c.2.1
                          have p13357_2 := h13357c.2.2.1
                          have p13357_3 := h13357c.2.2.2
                          linarith only [hlam, p13357_0]
                      · linarith only [h0, h11549, h13256, h13355, h13356, h8811, hc01, hc12, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13396 | h13396
                      · rcases h3bigk with h13397c | h13397c | h13397c | h13397c | h13397c | h13397c | h13397c | h13397c | h13397c | h13397c | h13397c | h13397c | h13397c | h13397c | h13397c | h13397c | h13397c | h13397c | h13397c | h13397c | h13397c | h13397c | h13397c | h13397c | h13397c
                        · have p13397_0 := h13397c.1
                          have p13397_1 := h13397c.2.1
                          have p13397_2 := h13397c.2.2.1
                          have p13397_3 := h13397c.2.2.2
                          linarith only [hlam, p13397_0]
                        · have p13397_0 := h13397c.1
                          have p13397_1 := h13397c.2.1
                          have p13397_2 := h13397c.2.2.1
                          have p13397_3 := h13397c.2.2.2
                          linarith only [h7360, hlam, p13397_1]
                        · have p13397_0 := h13397c.1
                          have p13397_1 := h13397c.2.1
                          have p13397_2 := h13397c.2.2.1
                          have p13397_3 := h13397c.2.2.2
                          linarith only [h13348, h13396, h7360, hc23, hc34, hlam, hphi, p13397_1]
                        · have p13397_0 := h13397c.1
                          have p13397_1 := h13397c.2.1
                          have p13397_2 := h13397c.2.2.1
                          have p13397_3 := h13397c.2.2.2
                          linarith only [h11550, hlam, p13397_0]
                        · have p13397_0 := h13397c.1
                          have p13397_1 := h13397c.2.1
                          have p13397_2 := h13397c.2.2.1
                          have p13397_3 := h13397c.2.2.2
                          linarith only [h13096, hlam, p13397_0]
                        · have p13397_0 := h13397c.1
                          have p13397_1 := h13397c.2.1
                          have p13397_2 := h13397c.2.2.1
                          have p13397_3 := h13397c.2.2.2
                          linarith only [h13348, h13396, hc03, hc34, hlam, hphi, p13397_1]
                        · have p13397_0 := h13397c.1
                          have p13397_1 := h13397c.2.1
                          have p13397_2 := h13397c.2.2.1
                          have p13397_3 := h13397c.2.2.2
                          linarith only [hlam, p13397_0]
                        · have p13397_0 := h13397c.1
                          have p13397_1 := h13397c.2.1
                          have p13397_2 := h13397c.2.2.1
                          have p13397_3 := h13397c.2.2.2
                          linarith only [h13348, h13396, hc23, hc34, hlam, hphi, p13397_1]
                        · have p13397_0 := h13397c.1
                          have p13397_1 := h13397c.2.1
                          have p13397_2 := h13397c.2.2.1
                          have p13397_3 := h13397c.2.2.2
                          linarith only [h13256, hlam, p13397_0]
                        · have p13397_0 := h13397c.1
                          have p13397_1 := h13397c.2.1
                          have p13397_2 := h13397c.2.2.1
                          have p13397_3 := h13397c.2.2.2
                          linarith only [h13348, hlam, p13397_0]
                        · have p13397_0 := h13397c.1
                          have p13397_1 := h13397c.2.1
                          have p13397_2 := h13397c.2.2.1
                          have p13397_3 := h13397c.2.2.2
                          linarith only [h11548, hlam, p13397_0]
                        · have p13397_0 := h13397c.1
                          have p13397_1 := h13397c.2.1
                          have p13397_2 := h13397c.2.2.1
                          have p13397_3 := h13397c.2.2.2
                          linarith only [h13254, hlam, p13397_0]
                        · have p13397_0 := h13397c.1
                          have p13397_1 := h13397c.2.1
                          have p13397_2 := h13397c.2.2.1
                          have p13397_3 := h13397c.2.2.2
                          linarith only [hlam, p13397_0]
                        · have p13397_0 := h13397c.1
                          have p13397_1 := h13397c.2.1
                          have p13397_2 := h13397c.2.2.1
                          have p13397_3 := h13397c.2.2.2
                          linarith only [h13351, hlam, p13397_0]
                        · have p13397_0 := h13397c.1
                          have p13397_1 := h13397c.2.1
                          have p13397_2 := h13397c.2.2.1
                          have p13397_3 := h13397c.2.2.2
                          linarith only [h13353, hlam, p13397_0]
                        · have p13397_0 := h13397c.1
                          have p13397_1 := h13397c.2.1
                          have p13397_2 := h13397c.2.2.1
                          have p13397_3 := h13397c.2.2.2
                          rcases p13397_3 (m.d 0 3) (by simp) with h13413 | h13413
                          · linarith only [h13413, hlam, p13397_0]
                          · rcases p13397_3 (m.d 1 3) (by simp) with h13415 | h13415
                            · linarith only [h13256, h13415, hlam]
                            · linarith only [h13415, h7360, hlam]
                        · have p13397_0 := h13397c.1
                          have p13397_1 := h13397c.2.1
                          have p13397_2 := h13397c.2.2.1
                          have p13397_3 := h13397c.2.2.2
                          linarith only [h7360, hc01, hc34, hlam, hphi, ht12, ht23, p13397_1]
                        · have p13397_0 := h13397c.1
                          have p13397_1 := h13397c.2.1
                          have p13397_2 := h13397c.2.2.1
                          have p13397_3 := h13397c.2.2.2
                          rcases p13397_3 (m.d 0 3) (by simp) with h13419 | h13419
                          · linarith only [h11550, h13419, hlam]
                          · linarith only [h11548, h13419, hlam]
                        · have p13397_0 := h13397c.1
                          have p13397_1 := h13397c.2.1
                          have p13397_2 := h13397c.2.2.1
                          have p13397_3 := h13397c.2.2.2
                          linarith only [hlam, p13397_0]
                        · have p13397_0 := h13397c.1
                          have p13397_1 := h13397c.2.1
                          have p13397_2 := h13397c.2.2.1
                          have p13397_3 := h13397c.2.2.2
                          linarith only [h13096, h7360, hc01, hc34, hlam, hphi, ht12, ht23, p13397_1]
                        · have p13397_0 := h13397c.1
                          have p13397_1 := h13397c.2.1
                          have p13397_2 := h13397c.2.2.1
                          have p13397_3 := h13397c.2.2.2
                          rcases p13397_3 (m.d 0 3) (by simp) with h13424 | h13424
                          · linarith only [h13424, hlam, p13397_0]
                          · rcases p13397_3 (m.d 1 3) (by simp) with h13426 | h13426
                            · linarith only [h13348, h13426, hlam]
                            · linarith only [h13426, h7360, hlam]
                        · have p13397_0 := h13397c.1
                          have p13397_1 := h13397c.2.1
                          have p13397_2 := h13397c.2.2.1
                          have p13397_3 := h13397c.2.2.2
                          linarith only [h7360, hc01, hc35, hlam, hphi, ht12, ht23, p13397_1]
                        · have p13397_0 := h13397c.1
                          have p13397_1 := h13397c.2.1
                          have p13397_2 := h13397c.2.2.1
                          have p13397_3 := h13397c.2.2.2
                          rcases p13397_3 (m.d 0 3) (by simp) with h13430 | h13430
                          · linarith only [h13096, h13430, hlam]
                          · linarith only [h11548, h13430, hlam]
                        · have p13397_0 := h13397c.1
                          have p13397_1 := h13397c.2.1
                          have p13397_2 := h13397c.2.2.1
                          have p13397_3 := h13397c.2.2.2
                          linarith only [h13396, hlam, p13397_0]
                        · have p13397_0 := h13397c.1
                          have p13397_1 := h13397c.2.1
                          have p13397_2 := h13397c.2.2.1
                          have p13397_3 := h13397c.2.2.2
                          linarith only [hlam, p13397_0]
                      · linarith only [h11550, h13253, h13396, h7360, h8811, hc01, hc14, hlam, hphi]
              · linarith only [h13253, h13350, h8811, hlam]
        · linarith only [h0, h11549, h13255, hlam]
      · linarith only [h0, h11548, h13254, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h13439 | h13439
      · rcases m.htr 1 2 4 (by decide) (by decide) with h13440 | h13440
        · rcases m.htr 1 3 4 (by decide) (by decide) with h13441 | h13441
          · rcases m.htr 1 3 5 (by decide) (by decide) with h13442 | h13442
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13443 | h13443
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13444 | h13444
                · linarith only [h0, h11548, h11550, h13444, h7360, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13446 | h13446
                  · linarith only [h11548, h13096, h13446, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13448 | h13448
                    · linarith only [h11549, h13253, h13448, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13450 | h13450
                      · linarith only [h13253, h13439, h13441, h13450, h8811, hc01, hc12, hlam, hphi]
                      · linarith only [h11550, h13439, h13441, h13443, h13450, h7360, hc01, hc12, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13453 | h13453
                · linarith only [h11548, h11550, h13453, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13455 | h13455
                  · linarith only [h11548, h13096, h13455, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13457 | h13457
                    · linarith only [h13443, h13457, h8811, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13459 | h13459
                      · linarith only [h13441, h13443, h13459, hlam]
                      · rcases h3bigk with h13461c | h13461c | h13461c | h13461c | h13461c | h13461c | h13461c | h13461c | h13461c | h13461c | h13461c | h13461c | h13461c | h13461c | h13461c | h13461c | h13461c | h13461c | h13461c | h13461c | h13461c | h13461c | h13461c | h13461c | h13461c
                        · have p13461_0 := h13461c.1
                          have p13461_1 := h13461c.2.1
                          have p13461_2 := h13461c.2.2.1
                          have p13461_3 := h13461c.2.2.2
                          linarith only [hlam, p13461_0]
                        · have p13461_0 := h13461c.1
                          have p13461_1 := h13461c.2.1
                          have p13461_2 := h13461c.2.2.1
                          have p13461_3 := h13461c.2.2.2
                          linarith only [h7360, hlam, p13461_1]
                        · have p13461_0 := h13461c.1
                          have p13461_1 := h13461c.2.1
                          have p13461_2 := h13461c.2.2.1
                          have p13461_3 := h13461c.2.2.2
                          linarith only [h11550, hc23, hc34, hlam, hphi, p13461_1]
                        · have p13461_0 := h13461c.1
                          have p13461_1 := h13461c.2.1
                          have p13461_2 := h13461c.2.2.1
                          have p13461_3 := h13461c.2.2.2
                          linarith only [h11550, hlam, p13461_0]
                        · have p13461_0 := h13461c.1
                          have p13461_1 := h13461c.2.1
                          have p13461_2 := h13461c.2.2.1
                          have p13461_3 := h13461c.2.2.2
                          linarith only [h13096, hlam, p13461_0]
                        · have p13461_0 := h13461c.1
                          have p13461_1 := h13461c.2.1
                          have p13461_2 := h13461c.2.2.1
                          have p13461_3 := h13461c.2.2.2
                          rcases p13461_3 (m.d 0 3) (by simp) with h13467 | h13467
                          · linarith only [h13467, h7360, hlam]
                          · rcases p13461_3 (m.d 1 3) (by simp) with h13469 | h13469
                            · rcases p13461_3 (m.d 2 3) (by simp) with h13470 | h13470
                              · linarith only [h13439, h13470, hlam]
                              · rcases p13461_3 (m.d 3 4) (by simp) with h13472 | h13472
                                · linarith only [h13441, h13472, hlam]
                                · linarith only [h11550, h13472, hlam]
                            · linarith only [h13469, h7360, hlam]
                        · have p13461_0 := h13461c.1
                          have p13461_1 := h13461c.2.1
                          have p13461_2 := h13461c.2.2.1
                          have p13461_3 := h13461c.2.2.2
                          linarith only [hlam, p13461_0]
                        · have p13461_0 := h13461c.1
                          have p13461_1 := h13461c.2.1
                          have p13461_2 := h13461c.2.2.1
                          have p13461_3 := h13461c.2.2.2
                          rcases p13461_3 (m.d 0 3) (by simp) with h13477 | h13477
                          · linarith only [h13477, h7360, hlam]
                          · linarith only [h11548, h13477, hlam]
                        · have p13461_0 := h13461c.1
                          have p13461_1 := h13461c.2.1
                          have p13461_2 := h13461c.2.2.1
                          have p13461_3 := h13461c.2.2.2
                          linarith only [h11550, h13439, h7360, hc01, hc12, hlam, hphi, p13461_1]
                        · have p13461_0 := h13461c.1
                          have p13461_1 := h13461c.2.1
                          have p13461_2 := h13461c.2.2.1
                          have p13461_3 := h13461c.2.2.2
                          linarith only [h13096, h13439, h7360, hc01, hc12, hlam, hphi, p13461_1]
                        · have p13461_0 := h13461c.1
                          have p13461_1 := h13461c.2.1
                          have p13461_2 := h13461c.2.2.1
                          have p13461_3 := h13461c.2.2.2
                          linarith only [h11548, hlam, p13461_0]
                        · have p13461_0 := h13461c.1
                          have p13461_1 := h13461c.2.1
                          have p13461_2 := h13461c.2.2.1
                          have p13461_3 := h13461c.2.2.2
                          linarith only [h13439, hlam, p13461_0]
                        · have p13461_0 := h13461c.1
                          have p13461_1 := h13461c.2.1
                          have p13461_2 := h13461c.2.2.1
                          have p13461_3 := h13461c.2.2.2
                          linarith only [hlam, p13461_0]
                        · have p13461_0 := h13461c.1
                          have p13461_1 := h13461c.2.1
                          have p13461_2 := h13461c.2.2.1
                          have p13461_3 := h13461c.2.2.2
                          linarith only [h13453, hlam, p13461_0]
                        · have p13461_0 := h13461c.1
                          have p13461_1 := h13461c.2.1
                          have p13461_2 := h13461c.2.2.1
                          have p13461_3 := h13461c.2.2.2
                          linarith only [h13455, hlam, p13461_0]
                        · have p13461_0 := h13461c.1
                          have p13461_1 := h13461c.2.1
                          have p13461_2 := h13461c.2.2.1
                          have p13461_3 := h13461c.2.2.2
                          linarith only [h13439, h13441, h7360, hc01, hc12, hlam, hphi, p13461_1]
                        · have p13461_0 := h13461c.1
                          have p13461_1 := h13461c.2.1
                          have p13461_2 := h13461c.2.2.1
                          have p13461_3 := h13461c.2.2.2
                          linarith only [h13441, hlam, p13461_0]
                        · have p13461_0 := h13461c.1
                          have p13461_1 := h13461c.2.1
                          have p13461_2 := h13461c.2.2.1
                          have p13461_3 := h13461c.2.2.2
                          linarith only [h13441, h13443, hc23, hc45, hlam, hphi, ht34, p13461_1]
                        · have p13461_0 := h13461c.1
                          have p13461_1 := h13461c.2.1
                          have p13461_2 := h13461c.2.2.1
                          have p13461_3 := h13461c.2.2.2
                          linarith only [hlam, p13461_0]
                        · have p13461_0 := h13461c.1
                          have p13461_1 := h13461c.2.1
                          have p13461_2 := h13461c.2.2.1
                          have p13461_3 := h13461c.2.2.2
                          linarith only [h13459, hlam, p13461_1]
                        · have p13461_0 := h13461c.1
                          have p13461_1 := h13461c.2.1
                          have p13461_2 := h13461c.2.2.1
                          have p13461_3 := h13461c.2.2.2
                          linarith only [h13439, h13442, h7360, hc01, hc12, hlam, hphi, p13461_1]
                        · have p13461_0 := h13461c.1
                          have p13461_1 := h13461c.2.1
                          have p13461_2 := h13461c.2.2.1
                          have p13461_3 := h13461c.2.2.2
                          linarith only [h13442, hlam, p13461_0]
                        · have p13461_0 := h13461c.1
                          have p13461_1 := h13461c.2.1
                          have p13461_2 := h13461c.2.2.1
                          have p13461_3 := h13461c.2.2.2
                          rcases p13461_3 (m.d 0 3) (by simp) with h13494 | h13494
                          · linarith only [h13096, h13494, hlam]
                          · linarith only [h11548, h13494, hlam]
                        · have p13461_0 := h13461c.1
                          have p13461_1 := h13461c.2.1
                          have p13461_2 := h13461c.2.2.1
                          have p13461_3 := h13461c.2.2.2
                          linarith only [h11550, h13439, h13442, h7360, hc01, hc12, hlam, hphi, p13461_1]
                        · have p13461_0 := h13461c.1
                          have p13461_1 := h13461c.2.1
                          have p13461_2 := h13461c.2.2.1
                          have p13461_3 := h13461c.2.2.2
                          linarith only [hlam, p13461_0]
            · linarith only [h11550, h13441, h13442, h7360, hc01, hc35, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h13500 | h13500
            · linarith only [h13096, h13441, h13500, h7360, hc01, hc34, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13502 | h13502
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13503 | h13503
                · linarith only [h13441, h13503, h7360, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13505 | h13505
                  · linarith only [h10295, h11548, h11550, h13253, h13500, h13505, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13507 | h13507
                    · linarith only [h11549, h13253, h13507, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13509 | h13509
                      · rcases h3bigk with h13510c | h13510c | h13510c | h13510c | h13510c | h13510c | h13510c | h13510c | h13510c | h13510c | h13510c | h13510c | h13510c | h13510c | h13510c | h13510c | h13510c | h13510c | h13510c | h13510c | h13510c | h13510c | h13510c | h13510c | h13510c
                        · have p13510_0 := h13510c.1
                          have p13510_1 := h13510c.2.1
                          have p13510_2 := h13510c.2.2.1
                          have p13510_3 := h13510c.2.2.2
                          linarith only [hlam, p13510_0]
                        · have p13510_0 := h13510c.1
                          have p13510_1 := h13510c.2.1
                          have p13510_2 := h13510c.2.2.1
                          have p13510_3 := h13510c.2.2.2
                          linarith only [h7360, hlam, p13510_1]
                        · have p13510_0 := h13510c.1
                          have p13510_1 := h13510c.2.1
                          have p13510_2 := h13510c.2.2.1
                          have p13510_3 := h13510c.2.2.2
                          linarith only [h11550, h13253, h13441, h13502, hc23, hc34, hlam, hphi, p13510_1]
                        · have p13510_0 := h13510c.1
                          have p13510_1 := h13510c.2.1
                          have p13510_2 := h13510c.2.2.1
                          have p13510_3 := h13510c.2.2.2
                          linarith only [h11550, hlam, p13510_0]
                        · have p13510_0 := h13510c.1
                          have p13510_1 := h13510c.2.1
                          have p13510_2 := h13510c.2.2.1
                          have p13510_3 := h13510c.2.2.2
                          linarith only [h13096, hlam, p13510_0]
                        · have p13510_0 := h13510c.1
                          have p13510_1 := h13510c.2.1
                          have p13510_2 := h13510c.2.2.1
                          have p13510_3 := h13510c.2.2.2
                          linarith only [h13500, hc03, hc35, hlam, hphi, p13510_1]
                        · have p13510_0 := h13510c.1
                          have p13510_1 := h13510c.2.1
                          have p13510_2 := h13510c.2.2.1
                          have p13510_3 := h13510c.2.2.2
                          linarith only [hlam, p13510_0]
                        · have p13510_0 := h13510c.1
                          have p13510_1 := h13510c.2.1
                          have p13510_2 := h13510c.2.2.1
                          have p13510_3 := h13510c.2.2.2
                          linarith only [h13500, hc23, hc35, hlam, hphi, p13510_1]
                        · have p13510_0 := h13510c.1
                          have p13510_1 := h13510c.2.1
                          have p13510_2 := h13510c.2.2.1
                          have p13510_3 := h13510c.2.2.2
                          linarith only [h13441, hlam, p13510_0]
                        · have p13510_0 := h13510c.1
                          have p13510_1 := h13510c.2.1
                          have p13510_2 := h13510c.2.2.1
                          have p13510_3 := h13510c.2.2.2
                          linarith only [h13500, hlam, p13510_0]
                        · have p13510_0 := h13510c.1
                          have p13510_1 := h13510c.2.1
                          have p13510_2 := h13510c.2.2.1
                          have p13510_3 := h13510c.2.2.2
                          linarith only [h11548, hlam, p13510_0]
                        · have p13510_0 := h13510c.1
                          have p13510_1 := h13510c.2.1
                          have p13510_2 := h13510c.2.2.1
                          have p13510_3 := h13510c.2.2.2
                          linarith only [h13439, hlam, p13510_0]
                        · have p13510_0 := h13510c.1
                          have p13510_1 := h13510c.2.1
                          have p13510_2 := h13510c.2.2.1
                          have p13510_3 := h13510c.2.2.2
                          linarith only [hlam, p13510_0]
                        · have p13510_0 := h13510c.1
                          have p13510_1 := h13510c.2.1
                          have p13510_2 := h13510c.2.2.1
                          have p13510_3 := h13510c.2.2.2
                          linarith only [h13503, hlam, p13510_0]
                        · have p13510_0 := h13510c.1
                          have p13510_1 := h13510c.2.1
                          have p13510_2 := h13510c.2.2.1
                          have p13510_3 := h13510c.2.2.2
                          linarith only [h13505, hlam, p13510_0]
                        · have p13510_0 := h13510c.1
                          have p13510_1 := h13510c.2.1
                          have p13510_2 := h13510c.2.2.1
                          have p13510_3 := h13510c.2.2.2
                          rcases p13510_3 (m.d 0 3) (by simp) with h13526 | h13526
                          · linarith only [h13526, hlam, p13510_0]
                          · rcases p13510_3 (m.d 1 3) (by simp) with h13528 | h13528
                            · linarith only [h13441, h13528, hlam]
                            · linarith only [h13528, h7360, hlam]
                        · have p13510_0 := h13510c.1
                          have p13510_1 := h13510c.2.1
                          have p13510_2 := h13510c.2.2.1
                          have p13510_3 := h13510c.2.2.2
                          linarith only [h7360, hc01, hc34, hlam, hphi, ht12, ht23, p13510_1]
                        · have p13510_0 := h13510c.1
                          have p13510_1 := h13510c.2.1
                          have p13510_2 := h13510c.2.2.1
                          have p13510_3 := h13510c.2.2.2
                          rcases p13510_3 (m.d 0 3) (by simp) with h13532 | h13532
                          · linarith only [h11550, h13532, hlam]
                          · linarith only [h11548, h13532, hlam]
                        · have p13510_0 := h13510c.1
                          have p13510_1 := h13510c.2.1
                          have p13510_2 := h13510c.2.2.1
                          have p13510_3 := h13510c.2.2.2
                          linarith only [hlam, p13510_0]
                        · have p13510_0 := h13510c.1
                          have p13510_1 := h13510c.2.1
                          have p13510_2 := h13510c.2.2.1
                          have p13510_3 := h13510c.2.2.2
                          linarith only [h13096, h7360, hc01, hc34, hlam, hphi, ht12, ht23, p13510_1]
                        · have p13510_0 := h13510c.1
                          have p13510_1 := h13510c.2.1
                          have p13510_2 := h13510c.2.2.1
                          have p13510_3 := h13510c.2.2.2
                          rcases p13510_3 (m.d 0 3) (by simp) with h13537 | h13537
                          · linarith only [h13537, hlam, p13510_0]
                          · rcases p13510_3 (m.d 1 3) (by simp) with h13539 | h13539
                            · linarith only [h13500, h13539, hlam]
                            · linarith only [h13539, h7360, hlam]
                        · have p13510_0 := h13510c.1
                          have p13510_1 := h13510c.2.1
                          have p13510_2 := h13510c.2.2.1
                          have p13510_3 := h13510c.2.2.2
                          linarith only [h7360, hc01, hc35, hlam, hphi, ht12, ht23, p13510_1]
                        · have p13510_0 := h13510c.1
                          have p13510_1 := h13510c.2.1
                          have p13510_2 := h13510c.2.2.1
                          have p13510_3 := h13510c.2.2.2
                          rcases p13510_3 (m.d 0 3) (by simp) with h13543 | h13543
                          · linarith only [h13096, h13543, hlam]
                          · linarith only [h11548, h13543, hlam]
                        · have p13510_0 := h13510c.1
                          have p13510_1 := h13510c.2.1
                          have p13510_2 := h13510c.2.2.1
                          have p13510_3 := h13510c.2.2.2
                          linarith only [h13509, hlam, p13510_0]
                        · have p13510_0 := h13510c.1
                          have p13510_1 := h13510c.2.1
                          have p13510_2 := h13510c.2.2.1
                          have p13510_3 := h13510c.2.2.2
                          linarith only [hlam, p13510_0]
                      · linarith only [h13441, h13502, h13509, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13549 | h13549
                · linarith only [h11548, h11550, h13549, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13551 | h13551
                  · linarith only [h11548, h13096, h13551, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13553 | h13553
                    · linarith only [h11549, h13502, h13553, h8811, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13555 | h13555
                      · linarith only [h13441, h13502, h13555, h7360, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h13441, h13555, h7360, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
        · linarith only [h0, h11549, h13440, hlam]
      · linarith only [h0, h11548, h13439, hlam]

set_option maxHeartbeats 8270000 in
set_option maxHeartbeats 8270000 in
theorem r1l7_13_24_L_I_H_I_s11_x0_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7360 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8811 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg10295 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h11548 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h11549 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h7360 := hg7360
  have h8811 := hg8811
  have h10295 := hg10295
  rcases m.htr 0 3 4 (by decide) (by decide) with h11550 | h11550
  · exact r1l7_13_24_L_I_H_I_s11_x0_x0_x0 m hb3 hb4 hg0 hg7360 hg8811 hg10295 h11548 h11549 h11550
  · exact r1l7_13_24_L_I_H_I_s11_x0_x0_x1 m hb3 hb4 hg0 hg7360 hg8811 hg10295 h11548 h11549 h11550

end R2N4
