import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_3S16
import Jsp000404.R1LeavesN7_3S17

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6296000 in
set_option maxHeartbeats 6296000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x1_x1_x1_x1_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg8674 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9870 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h10361 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10362 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h10363 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h11298 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h11300 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h11302 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h11304 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h11305 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h8674 := hg8674
  have h9870 := hg9870
  rcases m.htr 1 4 5 (by decide) (by decide) with h11969 | h11969
  · linarith only [h10362, h10363, h11304, h11305, h11969, h8674, hc02, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
  · rcases m.htr 2 3 4 (by decide) (by decide) with h11971 | h11971
    · rcases m.htr 2 3 5 (by decide) (by decide) with h11972 | h11972
      · rcases m.htr 2 4 5 (by decide) (by decide) with h11973 | h11973
        · rcases m.htr 3 4 5 (by decide) (by decide) with h11974 | h11974
          · linarith only [h10362, h10363, h11304, h11305, h11974, hlam]
          · rcases h1bigk with h11976c | h11976c | h11976c | h11976c | h11976c | h11976c | h11976c | h11976c | h11976c | h11976c | h11976c | h11976c | h11976c | h11976c | h11976c | h11976c | h11976c | h11976c | h11976c | h11976c | h11976c | h11976c | h11976c | h11976c | h11976c
            · have p11976_0 := h11976c.1
              have p11976_1 := h11976c.2.1
              have p11976_2 := h11976c.2.2.1
              have p11976_3 := h11976c.2.2.2
              linarith only [hlam, p11976_0]
            · have p11976_0 := h11976c.1
              have p11976_1 := h11976c.2.1
              have p11976_2 := h11976c.2.2.1
              have p11976_3 := h11976c.2.2.2
              rcases p11976_3 (m.d 0 1) (by simp) with h11978 | h11978
              · rcases p11976_3 (m.d 1 2) (by simp) with h11979 | h11979
                · linarith only [h11979, hlam, p11976_0]
                · rcases p11976_3 (m.d 1 3) (by simp) with h11981 | h11981
                  · linarith only [h1, h11981, hlam]
                  · linarith only [h11298, h11981, hlam]
              · linarith only [h11978, hlam, p11976_0]
            · have p11976_0 := h11976c.1
              have p11976_1 := h11976c.2.1
              have p11976_2 := h11976c.2.2.1
              have p11976_3 := h11976c.2.2.2
              rcases p11976_3 (m.d 0 1) (by simp) with h11985 | h11985
              · rcases p11976_3 (m.d 1 2) (by simp) with h11986 | h11986
                · linarith only [h0, h11986, hlam]
                · rcases p11976_3 (m.d 1 3) (by simp) with h11988 | h11988
                  · linarith only [h11988, hlam, p11976_0]
                  · rcases p11976_3 (m.d 1 4) (by simp) with h11990 | h11990
                    · linarith only [h11990, h2, hlam]
                    · rcases p11976_3 (m.d 1 5) (by simp) with h11992 | h11992
                      · linarith only [h11992, h3, hlam]
                      · linarith only [h11305, h11992, hlam]
              · linarith only [h11985, hlam, p11976_0]
            · have p11976_0 := h11976c.1
              have p11976_1 := h11976c.2.1
              have p11976_2 := h11976c.2.2.1
              have p11976_3 := h11976c.2.2.2
              rcases p11976_3 (m.d 0 1) (by simp) with h11996 | h11996
              · rcases p11976_3 (m.d 1 2) (by simp) with h11997 | h11997
                · linarith only [h0, h11997, hlam]
                · rcases p11976_3 (m.d 1 3) (by simp) with h11999 | h11999
                  · linarith only [h1, h11999, hlam]
                  · linarith only [h11304, h11999, hlam]
              · linarith only [h11996, hlam, p11976_0]
            · have p11976_0 := h11976c.1
              have p11976_1 := h11976c.2.1
              have p11976_2 := h11976c.2.2.1
              have p11976_3 := h11976c.2.2.2
              rcases p11976_3 (m.d 0 1) (by simp) with h12003 | h12003
              · rcases p11976_3 (m.d 1 2) (by simp) with h12004 | h12004
                · linarith only [h0, h12004, hlam]
                · rcases p11976_3 (m.d 1 3) (by simp) with h12006 | h12006
                  · linarith only [h1, h12006, hlam]
                  · rcases p11976_3 (m.d 1 4) (by simp) with h12008 | h12008
                    · linarith only [h12008, h2, hlam]
                    · rcases p11976_3 (m.d 1 5) (by simp) with h12010 | h12010
                      · linarith only [h12010, hlam, p11976_0]
                      · rcases h3bigk with h12012c | h12012c | h12012c | h12012c | h12012c | h12012c | h12012c | h12012c | h12012c | h12012c | h12012c | h12012c | h12012c | h12012c | h12012c | h12012c | h12012c | h12012c | h12012c | h12012c | h12012c | h12012c | h12012c | h12012c | h12012c
                        · have p12012_0 := h12012c.1
                          have p12012_1 := h12012c.2.1
                          have p12012_2 := h12012c.2.2.1
                          have p12012_3 := h12012c.2.2.2
                          linarith only [hlam, p12012_0]
                        · have p12012_0 := h12012c.1
                          have p12012_1 := h12012c.2.1
                          have p12012_2 := h12012c.2.2.1
                          have p12012_3 := h12012c.2.2.2
                          rcases p12012_3 (m.d 0 3) (by simp) with h12014 | h12014
                          · rcases p12012_3 (m.d 1 3) (by simp) with h12015 | h12015
                            · linarith only [h1, h12015, hlam]
                            · rcases p12012_3 (m.d 2 3) (by simp) with h12017 | h12017
                              · rcases p12012_3 (m.d 3 4) (by simp) with h12018 | h12018
                                · linarith only [h10361, h12018, hlam]
                                · rcases p12012_3 (m.d 3 5) (by simp) with h12020 | h12020
                                  · linarith only [h10362, h12020, hlam]
                                  · linarith only [h11305, h12020, hlam]
                              · linarith only [h11298, h12017, hlam]
                          · linarith only [h1, h12014, hlam]
                        · have p12012_0 := h12012c.1
                          have p12012_1 := h12012c.2.1
                          have p12012_2 := h12012c.2.2.1
                          have p12012_3 := h12012c.2.2.2
                          linarith only [h4, hlam, p12012_1]
                        · have p12012_0 := h12012c.1
                          have p12012_1 := h12012c.2.1
                          have p12012_2 := h12012c.2.2.1
                          have p12012_3 := h12012c.2.2.2
                          linarith only [h10362, h11304, h11305, hlam, p12012_2]
                        · have p12012_0 := h12012c.1
                          have p12012_1 := h12012c.2.1
                          have p12012_2 := h12012c.2.2.1
                          have p12012_3 := h12012c.2.2.2
                          linarith only [h11304, h11305, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p12012_1]
                        · have p12012_0 := h12012c.1
                          have p12012_1 := h12012c.2.1
                          have p12012_2 := h12012c.2.2.1
                          have p12012_3 := h12012c.2.2.2
                          linarith only [h1, hlam, p12012_0]
                        · have p12012_0 := h12012c.1
                          have p12012_1 := h12012c.2.1
                          have p12012_2 := h12012c.2.2.1
                          have p12012_3 := h12012c.2.2.2
                          linarith only [hlam, p12012_0]
                        · have p12012_0 := h12012c.1
                          have p12012_1 := h12012c.2.1
                          have p12012_2 := h12012c.2.2.1
                          have p12012_3 := h12012c.2.2.2
                          linarith only [h11298, hlam, p12012_1]
                        · have p12012_0 := h12012c.1
                          have p12012_1 := h12012c.2.1
                          have p12012_2 := h12012c.2.2.1
                          have p12012_3 := h12012c.2.2.2
                          linarith only [h10362, h10363, h11305, hc34, hc45, hlam, hphi, p12012_1]
                        · have p12012_0 := h12012c.1
                          have p12012_1 := h12012c.2.1
                          have p12012_2 := h12012c.2.2.1
                          have p12012_3 := h12012c.2.2.2
                          linarith only [h11305, hlam, p12012_0]
                        · have p12012_0 := h12012c.1
                          have p12012_1 := h12012c.2.1
                          have p12012_2 := h12012c.2.2.1
                          have p12012_3 := h12012c.2.2.2
                          linarith only [h10362, h11305, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p12012_1]
                        · have p12012_0 := h12012c.1
                          have p12012_1 := h12012c.2.1
                          have p12012_2 := h12012c.2.2.1
                          have p12012_3 := h12012c.2.2.2
                          rcases p12012_3 (m.d 0 3) (by simp) with h12034 | h12034
                          · linarith only [h12034, h4, hlam]
                          · linarith only [h1, h12034, hlam]
                        · have p12012_0 := h12012c.1
                          have p12012_1 := h12012c.2.1
                          have p12012_2 := h12012c.2.2.1
                          have p12012_3 := h12012c.2.2.2
                          linarith only [hlam, p12012_0]
                        · have p12012_0 := h12012c.1
                          have p12012_1 := h12012c.2.1
                          have p12012_2 := h12012c.2.2.1
                          have p12012_3 := h12012c.2.2.2
                          linarith only [h10362, h10363, h11304, h11305, h11971, h11973, hlam, p12012_2]
                        · have p12012_0 := h12012c.1
                          have p12012_1 := h12012c.2.1
                          have p12012_2 := h12012c.2.2.1
                          have p12012_3 := h12012c.2.2.2
                          linarith only [h11304, h11305, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12012_1]
                        · have p12012_0 := h12012c.1
                          have p12012_1 := h12012c.2.1
                          have p12012_2 := h12012c.2.2.1
                          have p12012_3 := h12012c.2.2.2
                          linarith only [h10361, hlam, p12012_0]
                        · have p12012_0 := h12012c.1
                          have p12012_1 := h12012c.2.1
                          have p12012_2 := h12012c.2.2.1
                          have p12012_3 := h12012c.2.2.2
                          linarith only [h11304, hlam, p12012_0]
                        · have p12012_0 := h12012c.1
                          have p12012_1 := h12012c.2.1
                          have p12012_2 := h12012c.2.2.1
                          have p12012_3 := h12012c.2.2.2
                          linarith only [h11971, hlam, p12012_0]
                        · have p12012_0 := h12012c.1
                          have p12012_1 := h12012c.2.1
                          have p12012_2 := h12012c.2.2.1
                          have p12012_3 := h12012c.2.2.2
                          linarith only [hlam, p12012_0]
                        · have p12012_0 := h12012c.1
                          have p12012_1 := h12012c.2.1
                          have p12012_2 := h12012c.2.2.1
                          have p12012_3 := h12012c.2.2.2
                          linarith only [h11974, hlam, p12012_1]
                        · have p12012_0 := h12012c.1
                          have p12012_1 := h12012c.2.1
                          have p12012_2 := h12012c.2.2.1
                          have p12012_3 := h12012c.2.2.2
                          linarith only [h10362, hlam, p12012_0]
                        · have p12012_0 := h12012c.1
                          have p12012_1 := h12012c.2.1
                          have p12012_2 := h12012c.2.2.1
                          have p12012_3 := h12012c.2.2.2
                          linarith only [h10362, h11304, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p12012_1]
                        · have p12012_0 := h12012c.1
                          have p12012_1 := h12012c.2.1
                          have p12012_2 := h12012c.2.2.1
                          have p12012_3 := h12012c.2.2.2
                          linarith only [h11972, hlam, p12012_0]
                        · have p12012_0 := h12012c.1
                          have p12012_1 := h12012c.2.1
                          have p12012_2 := h12012c.2.2.1
                          have p12012_3 := h12012c.2.2.2
                          rcases p12012_3 (m.d 0 3) (by simp) with h12048 | h12048
                          · rcases p12012_3 (m.d 1 3) (by simp) with h12049 | h12049
                            · linarith only [h11305, h12049, hlam]
                            · linarith only [h11304, h12049, hlam]
                          · linarith only [h10361, h12048, hlam]
                        · have p12012_0 := h12012c.1
                          have p12012_1 := h12012c.2.1
                          have p12012_2 := h12012c.2.2.1
                          have p12012_3 := h12012c.2.2.2
                          linarith only [hlam, p12012_0]
              · linarith only [h12003, hlam, p11976_0]
            · have p11976_0 := h11976c.1
              have p11976_1 := h11976c.2.1
              have p11976_2 := h11976c.2.2.1
              have p11976_3 := h11976c.2.2.2
              linarith only [h0, hlam, p11976_0]
            · have p11976_0 := h11976c.1
              have p11976_1 := h11976c.2.1
              have p11976_2 := h11976c.2.2.1
              have p11976_3 := h11976c.2.2.2
              linarith only [hlam, p11976_0]
            · have p11976_0 := h11976c.1
              have p11976_1 := h11976c.2.1
              have p11976_2 := h11976c.2.2.1
              have p11976_3 := h11976c.2.2.2
              linarith only [h11298, hlam, p11976_0]
            · have p11976_0 := h11976c.1
              have p11976_1 := h11976c.2.1
              have p11976_2 := h11976c.2.2.1
              have p11976_3 := h11976c.2.2.2
              linarith only [h11300, hlam, p11976_0]
            · have p11976_0 := h11976c.1
              have p11976_1 := h11976c.2.1
              have p11976_2 := h11976c.2.2.1
              have p11976_3 := h11976c.2.2.2
              linarith only [h11302, hlam, p11976_0]
            · have p11976_0 := h11976c.1
              have p11976_1 := h11976c.2.1
              have p11976_2 := h11976c.2.2.1
              have p11976_3 := h11976c.2.2.2
              linarith only [h1, hlam, p11976_0]
            · have p11976_0 := h11976c.1
              have p11976_1 := h11976c.2.1
              have p11976_2 := h11976c.2.2.1
              have p11976_3 := h11976c.2.2.2
              linarith only [h10362, h10363, h11305, h11971, h11973, hc12, hc23, hlam, hphi, p11976_1]
            · have p11976_0 := h11976c.1
              have p11976_1 := h11976c.2.1
              have p11976_2 := h11976c.2.2.1
              have p11976_3 := h11976c.2.2.2
              linarith only [hlam, p11976_0]
            · have p11976_0 := h11976c.1
              have p11976_1 := h11976c.2.1
              have p11976_2 := h11976c.2.2.1
              have p11976_3 := h11976c.2.2.2
              linarith only [h10362, h10363, h11300, h11305, h11971, h11973, hc12, hc23, hlam, hphi, p11976_1]
            · have p11976_0 := h11976c.1
              have p11976_1 := h11976c.2.1
              have p11976_2 := h11976c.2.2.1
              have p11976_3 := h11976c.2.2.2
              linarith only [h11305, hlam, p11976_1]
            · have p11976_0 := h11976c.1
              have p11976_1 := h11976c.2.1
              have p11976_2 := h11976c.2.2.1
              have p11976_3 := h11976c.2.2.2
              linarith only [h2, hlam, p11976_0]
            · have p11976_0 := h11976c.1
              have p11976_1 := h11976c.2.1
              have p11976_2 := h11976c.2.2.1
              have p11976_3 := h11976c.2.2.2
              linarith only [h10363, h11971, h11973, h2, hc12, hc23, hlam, hphi, p11976_1]
            · have p11976_0 := h11976c.1
              have p11976_1 := h11976c.2.1
              have p11976_2 := h11976c.2.2.1
              have p11976_3 := h11976c.2.2.2
              linarith only [h11304, hlam, p11976_0]
            · have p11976_0 := h11976c.1
              have p11976_1 := h11976c.2.1
              have p11976_2 := h11976c.2.2.1
              have p11976_3 := h11976c.2.2.2
              linarith only [hlam, p11976_0]
            · have p11976_0 := h11976c.1
              have p11976_1 := h11976c.2.1
              have p11976_2 := h11976c.2.2.1
              have p11976_3 := h11976c.2.2.2
              linarith only [h11969, hlam, p11976_1]
            · have p11976_0 := h11976c.1
              have p11976_1 := h11976c.2.1
              have p11976_2 := h11976c.2.2.1
              have p11976_3 := h11976c.2.2.2
              linarith only [h3, hlam, p11976_0]
            · have p11976_0 := h11976c.1
              have p11976_1 := h11976c.2.1
              have p11976_2 := h11976c.2.2.1
              have p11976_3 := h11976c.2.2.2
              linarith only [h10363, h11971, h11973, h3, hc12, hc23, hlam, hphi, p11976_1]
            · have p11976_0 := h11976c.1
              have p11976_1 := h11976c.2.1
              have p11976_2 := h11976c.2.2.1
              have p11976_3 := h11976c.2.2.2
              linarith only [h10362, h10363, h11298, h11305, h11971, h11973, hc12, hc23, hlam, hphi, p11976_1]
            · have p11976_0 := h11976c.1
              have p11976_1 := h11976c.2.1
              have p11976_2 := h11976c.2.2.1
              have p11976_3 := h11976c.2.2.2
              linarith only [h10362, h10363, h11300, h11305, h11971, h11973, hc12, hc23, hlam, hphi, p11976_1]
            · have p11976_0 := h11976c.1
              have p11976_1 := h11976c.2.1
              have p11976_2 := h11976c.2.2.1
              have p11976_3 := h11976c.2.2.2
              linarith only [hlam, p11976_0]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h12075 | h12075
          · linarith only [h0, h11304, h11973, h12075, h8674, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
          · rcases h1bigk with h12077c | h12077c | h12077c | h12077c | h12077c | h12077c | h12077c | h12077c | h12077c | h12077c | h12077c | h12077c | h12077c | h12077c | h12077c | h12077c | h12077c | h12077c | h12077c | h12077c | h12077c | h12077c | h12077c | h12077c | h12077c
            · have p12077_0 := h12077c.1
              have p12077_1 := h12077c.2.1
              have p12077_2 := h12077c.2.2.1
              have p12077_3 := h12077c.2.2.2
              linarith only [hlam, p12077_0]
            · have p12077_0 := h12077c.1
              have p12077_1 := h12077c.2.1
              have p12077_2 := h12077c.2.2.1
              have p12077_3 := h12077c.2.2.2
              rcases p12077_3 (m.d 0 1) (by simp) with h12079 | h12079
              · rcases p12077_3 (m.d 1 2) (by simp) with h12080 | h12080
                · linarith only [h12080, hlam, p12077_0]
                · rcases p12077_3 (m.d 1 3) (by simp) with h12082 | h12082
                  · linarith only [h1, h12082, hlam]
                  · linarith only [h11298, h12082, hlam]
              · linarith only [h12079, hlam, p12077_0]
            · have p12077_0 := h12077c.1
              have p12077_1 := h12077c.2.1
              have p12077_2 := h12077c.2.2.1
              have p12077_3 := h12077c.2.2.2
              rcases p12077_3 (m.d 0 1) (by simp) with h12086 | h12086
              · rcases p12077_3 (m.d 1 2) (by simp) with h12087 | h12087
                · linarith only [h0, h12087, hlam]
                · rcases p12077_3 (m.d 1 3) (by simp) with h12089 | h12089
                  · linarith only [h12089, hlam, p12077_0]
                  · rcases p12077_3 (m.d 1 4) (by simp) with h12091 | h12091
                    · linarith only [h12091, h2, hlam]
                    · rcases p12077_3 (m.d 1 5) (by simp) with h12093 | h12093
                      · linarith only [h12093, h3, hlam]
                      · linarith only [h11305, h12093, hlam]
              · linarith only [h12086, hlam, p12077_0]
            · have p12077_0 := h12077c.1
              have p12077_1 := h12077c.2.1
              have p12077_2 := h12077c.2.2.1
              have p12077_3 := h12077c.2.2.2
              rcases p12077_3 (m.d 0 1) (by simp) with h12097 | h12097
              · rcases p12077_3 (m.d 1 2) (by simp) with h12098 | h12098
                · linarith only [h0, h12098, hlam]
                · rcases p12077_3 (m.d 1 3) (by simp) with h12100 | h12100
                  · linarith only [h1, h12100, hlam]
                  · linarith only [h11304, h12100, hlam]
              · linarith only [h12097, hlam, p12077_0]
            · have p12077_0 := h12077c.1
              have p12077_1 := h12077c.2.1
              have p12077_2 := h12077c.2.2.1
              have p12077_3 := h12077c.2.2.2
              rcases p12077_3 (m.d 0 1) (by simp) with h12104 | h12104
              · rcases p12077_3 (m.d 1 2) (by simp) with h12105 | h12105
                · linarith only [h0, h12105, hlam]
                · rcases p12077_3 (m.d 1 3) (by simp) with h12107 | h12107
                  · linarith only [h1, h12107, hlam]
                  · rcases p12077_3 (m.d 1 4) (by simp) with h12109 | h12109
                    · linarith only [h12109, h2, hlam]
                    · rcases p12077_3 (m.d 1 5) (by simp) with h12111 | h12111
                      · linarith only [h12111, hlam, p12077_0]
                      · rcases h3bigk with h12113c | h12113c | h12113c | h12113c | h12113c | h12113c | h12113c | h12113c | h12113c | h12113c | h12113c | h12113c | h12113c | h12113c | h12113c | h12113c | h12113c | h12113c | h12113c | h12113c | h12113c | h12113c | h12113c | h12113c | h12113c
                        · have p12113_0 := h12113c.1
                          have p12113_1 := h12113c.2.1
                          have p12113_2 := h12113c.2.2.1
                          have p12113_3 := h12113c.2.2.2
                          linarith only [hlam, p12113_0]
                        · have p12113_0 := h12113c.1
                          have p12113_1 := h12113c.2.1
                          have p12113_2 := h12113c.2.2.1
                          have p12113_3 := h12113c.2.2.2
                          rcases p12113_3 (m.d 0 3) (by simp) with h12115 | h12115
                          · rcases p12113_3 (m.d 1 3) (by simp) with h12116 | h12116
                            · linarith only [h1, h12116, hlam]
                            · rcases p12113_3 (m.d 2 3) (by simp) with h12118 | h12118
                              · rcases p12113_3 (m.d 3 4) (by simp) with h12119 | h12119
                                · linarith only [h10361, h12119, hlam]
                                · rcases p12113_3 (m.d 3 5) (by simp) with h12121 | h12121
                                  · linarith only [h10362, h12121, hlam]
                                  · linarith only [h11305, h12121, hlam]
                              · linarith only [h11298, h12118, hlam]
                          · linarith only [h1, h12115, hlam]
                        · have p12113_0 := h12113c.1
                          have p12113_1 := h12113c.2.1
                          have p12113_2 := h12113c.2.2.1
                          have p12113_3 := h12113c.2.2.2
                          linarith only [h4, hlam, p12113_1]
                        · have p12113_0 := h12113c.1
                          have p12113_1 := h12113c.2.1
                          have p12113_2 := h12113c.2.2.1
                          have p12113_3 := h12113c.2.2.2
                          linarith only [h10362, h11304, h11305, hlam, p12113_2]
                        · have p12113_0 := h12113c.1
                          have p12113_1 := h12113c.2.1
                          have p12113_2 := h12113c.2.2.1
                          have p12113_3 := h12113c.2.2.2
                          linarith only [h11304, h11305, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12113_1]
                        · have p12113_0 := h12113c.1
                          have p12113_1 := h12113c.2.1
                          have p12113_2 := h12113c.2.2.1
                          have p12113_3 := h12113c.2.2.2
                          linarith only [h1, hlam, p12113_0]
                        · have p12113_0 := h12113c.1
                          have p12113_1 := h12113c.2.1
                          have p12113_2 := h12113c.2.2.1
                          have p12113_3 := h12113c.2.2.2
                          linarith only [hlam, p12113_0]
                        · have p12113_0 := h12113c.1
                          have p12113_1 := h12113c.2.1
                          have p12113_2 := h12113c.2.2.1
                          have p12113_3 := h12113c.2.2.2
                          linarith only [h11298, hlam, p12113_1]
                        · have p12113_0 := h12113c.1
                          have p12113_1 := h12113c.2.1
                          have p12113_2 := h12113c.2.2.1
                          have p12113_3 := h12113c.2.2.2
                          linarith only [h11305, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p12077_1, p12113_1]
                        · have p12113_0 := h12113c.1
                          have p12113_1 := h12113c.2.1
                          have p12113_2 := h12113c.2.2.1
                          have p12113_3 := h12113c.2.2.2
                          linarith only [h11305, hlam, p12113_0]
                        · have p12113_0 := h12113c.1
                          have p12113_1 := h12113c.2.1
                          have p12113_2 := h12113c.2.2.1
                          have p12113_3 := h12113c.2.2.2
                          linarith only [h10362, h11305, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p12113_1]
                        · have p12113_0 := h12113c.1
                          have p12113_1 := h12113c.2.1
                          have p12113_2 := h12113c.2.2.1
                          have p12113_3 := h12113c.2.2.2
                          rcases p12113_3 (m.d 0 3) (by simp) with h12135 | h12135
                          · linarith only [h12135, h4, hlam]
                          · linarith only [h1, h12135, hlam]
                        · have p12113_0 := h12113c.1
                          have p12113_1 := h12113c.2.1
                          have p12113_2 := h12113c.2.2.1
                          have p12113_3 := h12113c.2.2.2
                          linarith only [hlam, p12113_0]
                        · have p12113_0 := h12113c.1
                          have p12113_1 := h12113c.2.1
                          have p12113_2 := h12113c.2.2.1
                          have p12113_3 := h12113c.2.2.2
                          linarith only [h10362, h11304, h11305, h4, hlam, p12113_2]
                        · have p12113_0 := h12113c.1
                          have p12113_1 := h12113c.2.1
                          have p12113_2 := h12113c.2.2.1
                          have p12113_3 := h12113c.2.2.2
                          linarith only [h11304, h11305, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12113_1]
                        · have p12113_0 := h12113c.1
                          have p12113_1 := h12113c.2.1
                          have p12113_2 := h12113c.2.2.1
                          have p12113_3 := h12113c.2.2.2
                          linarith only [h10361, hlam, p12113_0]
                        · have p12113_0 := h12113c.1
                          have p12113_1 := h12113c.2.1
                          have p12113_2 := h12113c.2.2.1
                          have p12113_3 := h12113c.2.2.2
                          linarith only [h11304, hlam, p12113_0]
                        · have p12113_0 := h12113c.1
                          have p12113_1 := h12113c.2.1
                          have p12113_2 := h12113c.2.2.1
                          have p12113_3 := h12113c.2.2.2
                          linarith only [h11971, hlam, p12113_0]
                        · have p12113_0 := h12113c.1
                          have p12113_1 := h12113c.2.1
                          have p12113_2 := h12113c.2.2.1
                          have p12113_3 := h12113c.2.2.2
                          linarith only [hlam, p12113_0]
                        · have p12113_0 := h12113c.1
                          have p12113_1 := h12113c.2.1
                          have p12113_2 := h12113c.2.2.1
                          have p12113_3 := h12113c.2.2.2
                          linarith only [h12075, hlam, p12113_1]
                        · have p12113_0 := h12113c.1
                          have p12113_1 := h12113c.2.1
                          have p12113_2 := h12113c.2.2.1
                          have p12113_3 := h12113c.2.2.2
                          linarith only [h10362, hlam, p12113_0]
                        · have p12113_0 := h12113c.1
                          have p12113_1 := h12113c.2.1
                          have p12113_2 := h12113c.2.2.1
                          have p12113_3 := h12113c.2.2.2
                          linarith only [h10362, h11304, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p12113_1]
                        · have p12113_0 := h12113c.1
                          have p12113_1 := h12113c.2.1
                          have p12113_2 := h12113c.2.2.1
                          have p12113_3 := h12113c.2.2.2
                          linarith only [h11972, hlam, p12113_0]
                        · have p12113_0 := h12113c.1
                          have p12113_1 := h12113c.2.1
                          have p12113_2 := h12113c.2.2.1
                          have p12113_3 := h12113c.2.2.2
                          rcases p12113_3 (m.d 0 3) (by simp) with h12149 | h12149
                          · rcases p12113_3 (m.d 1 3) (by simp) with h12150 | h12150
                            · linarith only [h11305, h12150, hlam]
                            · linarith only [h11304, h12150, hlam]
                          · linarith only [h10361, h12149, hlam]
                        · have p12113_0 := h12113c.1
                          have p12113_1 := h12113c.2.1
                          have p12113_2 := h12113c.2.2.1
                          have p12113_3 := h12113c.2.2.2
                          linarith only [hlam, p12113_0]
              · linarith only [h12104, hlam, p12077_0]
            · have p12077_0 := h12077c.1
              have p12077_1 := h12077c.2.1
              have p12077_2 := h12077c.2.2.1
              have p12077_3 := h12077c.2.2.2
              linarith only [h0, hlam, p12077_0]
            · have p12077_0 := h12077c.1
              have p12077_1 := h12077c.2.1
              have p12077_2 := h12077c.2.2.1
              have p12077_3 := h12077c.2.2.2
              linarith only [hlam, p12077_0]
            · have p12077_0 := h12077c.1
              have p12077_1 := h12077c.2.1
              have p12077_2 := h12077c.2.2.1
              have p12077_3 := h12077c.2.2.2
              linarith only [h11298, hlam, p12077_0]
            · have p12077_0 := h12077c.1
              have p12077_1 := h12077c.2.1
              have p12077_2 := h12077c.2.2.1
              have p12077_3 := h12077c.2.2.2
              linarith only [h11300, hlam, p12077_0]
            · have p12077_0 := h12077c.1
              have p12077_1 := h12077c.2.1
              have p12077_2 := h12077c.2.2.1
              have p12077_3 := h12077c.2.2.2
              linarith only [h11302, hlam, p12077_0]
            · have p12077_0 := h12077c.1
              have p12077_1 := h12077c.2.1
              have p12077_2 := h12077c.2.2.1
              have p12077_3 := h12077c.2.2.2
              linarith only [h1, hlam, p12077_0]
            · have p12077_0 := h12077c.1
              have p12077_1 := h12077c.2.1
              have p12077_2 := h12077c.2.2.1
              have p12077_3 := h12077c.2.2.2
              linarith only [h10362, h11305, h4, hc12, hc23, hlam, hphi, p12077_1]
            · have p12077_0 := h12077c.1
              have p12077_1 := h12077c.2.1
              have p12077_2 := h12077c.2.2.1
              have p12077_3 := h12077c.2.2.2
              linarith only [hlam, p12077_0]
            · have p12077_0 := h12077c.1
              have p12077_1 := h12077c.2.1
              have p12077_2 := h12077c.2.2.1
              have p12077_3 := h12077c.2.2.2
              linarith only [h10362, h11300, h11305, h4, hc12, hc23, hlam, hphi, p12077_1]
            · have p12077_0 := h12077c.1
              have p12077_1 := h12077c.2.1
              have p12077_2 := h12077c.2.2.1
              have p12077_3 := h12077c.2.2.2
              linarith only [h11305, hlam, p12077_1]
            · have p12077_0 := h12077c.1
              have p12077_1 := h12077c.2.1
              have p12077_2 := h12077c.2.2.1
              have p12077_3 := h12077c.2.2.2
              linarith only [h2, hlam, p12077_0]
            · have p12077_0 := h12077c.1
              have p12077_1 := h12077c.2.1
              have p12077_2 := h12077c.2.2.1
              have p12077_3 := h12077c.2.2.2
              linarith only [h11973, h2, h8674, hc12, hc45, hlam, hphi, ht23, ht34, p12077_1]
            · have p12077_0 := h12077c.1
              have p12077_1 := h12077c.2.1
              have p12077_2 := h12077c.2.2.1
              have p12077_3 := h12077c.2.2.2
              linarith only [h11304, hlam, p12077_0]
            · have p12077_0 := h12077c.1
              have p12077_1 := h12077c.2.1
              have p12077_2 := h12077c.2.2.1
              have p12077_3 := h12077c.2.2.2
              linarith only [hlam, p12077_0]
            · have p12077_0 := h12077c.1
              have p12077_1 := h12077c.2.1
              have p12077_2 := h12077c.2.2.1
              have p12077_3 := h12077c.2.2.2
              linarith only [h11969, hlam, p12077_1]
            · have p12077_0 := h12077c.1
              have p12077_1 := h12077c.2.1
              have p12077_2 := h12077c.2.2.1
              have p12077_3 := h12077c.2.2.2
              linarith only [h3, hlam, p12077_0]
            · have p12077_0 := h12077c.1
              have p12077_1 := h12077c.2.1
              have p12077_2 := h12077c.2.2.1
              have p12077_3 := h12077c.2.2.2
              linarith only [h10362, h11305, h4, hc12, hc23, hlam, hphi, p12077_1]
            · have p12077_0 := h12077c.1
              have p12077_1 := h12077c.2.1
              have p12077_2 := h12077c.2.2.1
              have p12077_3 := h12077c.2.2.2
              linarith only [h10362, h11298, h11305, h4, hc12, hc23, hlam, hphi, p12077_1]
            · have p12077_0 := h12077c.1
              have p12077_1 := h12077c.2.1
              have p12077_2 := h12077c.2.2.1
              have p12077_3 := h12077c.2.2.2
              linarith only [h10362, h11300, h11305, h4, hc12, hc23, hlam, hphi, p12077_1]
            · have p12077_0 := h12077c.1
              have p12077_1 := h12077c.2.1
              have p12077_2 := h12077c.2.2.1
              have p12077_3 := h12077c.2.2.2
              linarith only [hlam, p12077_0]
      · linarith only [h10362, h11972, h4, hlam]
    · linarith only [h1, h10362, h11304, h11305, h11971, h4, hc01, hc15, hlam, hphi, ht0b, ht5b]

set_option maxHeartbeats 6296000 in
set_option maxHeartbeats 6296000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x1_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg8674 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9870 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h10361 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10362 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h10363 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h11298 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h11300 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h11302 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h11304 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h8674 := hg8674
  have h9870 := hg9870
  rcases m.htr 1 3 5 (by decide) (by decide) with h11305 | h11305
  · exact r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x1_x1_x1_x1_x0_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg8674 hg9870 h10361 h10362 h10363 h11298 h11300 h11302 h11304 h11305
  · exact r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x1_x1_x1_x1_x0_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg8674 hg9870 h10361 h10362 h10363 h11298 h11300 h11302 h11304 h11305

set_option maxHeartbeats 6296000 in
set_option maxHeartbeats 6296000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg8674 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9870 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h10361 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10362 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h10363 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h11298 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h11300 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h11302 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h11304 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h8674 := hg8674
  have h9870 := hg9870
  rcases m.htr 1 3 5 (by decide) (by decide) with h12178 | h12178
  · rcases m.htr 1 4 5 (by decide) (by decide) with h12179 | h12179
    · linarith only [h10363, h12179, h2, hlam]
    · linarith only [h11304, h12178, h12179, hlam]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h12182 | h12182
    · linarith only [h10363, h12182, h2, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h12184 | h12184
      · rcases m.htr 2 3 5 (by decide) (by decide) with h12185 | h12185
        · rcases m.htr 2 4 5 (by decide) (by decide) with h12186 | h12186
          · linarith only [h10361, h10363, h11298, h11304, h12186, hc12, hc24, hlam, hphi]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h12188 | h12188
            · linarith only [h0, h12186, h12188, h8674, hc12, hc34, hlam, hphi, ht23]
            · rcases h1bigk with h12190c | h12190c | h12190c | h12190c | h12190c | h12190c | h12190c | h12190c | h12190c | h12190c | h12190c | h12190c | h12190c | h12190c | h12190c | h12190c | h12190c | h12190c | h12190c | h12190c | h12190c | h12190c | h12190c | h12190c | h12190c
              · have p12190_0 := h12190c.1
                have p12190_1 := h12190c.2.1
                have p12190_2 := h12190c.2.2.1
                have p12190_3 := h12190c.2.2.2
                linarith only [hlam, p12190_0]
              · have p12190_0 := h12190c.1
                have p12190_1 := h12190c.2.1
                have p12190_2 := h12190c.2.2.1
                have p12190_3 := h12190c.2.2.2
                rcases p12190_3 (m.d 0 1) (by simp) with h12192 | h12192
                · rcases p12190_3 (m.d 1 2) (by simp) with h12193 | h12193
                  · linarith only [h12193, hlam, p12190_0]
                  · rcases p12190_3 (m.d 1 3) (by simp) with h12195 | h12195
                    · linarith only [h1, h12195, hlam]
                    · linarith only [h11298, h12195, hlam]
                · linarith only [h12192, hlam, p12190_0]
              · have p12190_0 := h12190c.1
                have p12190_1 := h12190c.2.1
                have p12190_2 := h12190c.2.2.1
                have p12190_3 := h12190c.2.2.2
                rcases p12190_3 (m.d 0 1) (by simp) with h12199 | h12199
                · rcases p12190_3 (m.d 1 2) (by simp) with h12200 | h12200
                  · linarith only [h0, h12200, hlam]
                  · rcases p12190_3 (m.d 1 3) (by simp) with h12202 | h12202
                    · linarith only [h12202, hlam, p12190_0]
                    · rcases p12190_3 (m.d 1 4) (by simp) with h12204 | h12204
                      · linarith only [h12204, h2, hlam]
                      · linarith only [h11304, h12204, hlam]
                · linarith only [h12199, hlam, p12190_0]
              · have p12190_0 := h12190c.1
                have p12190_1 := h12190c.2.1
                have p12190_2 := h12190c.2.2.1
                have p12190_3 := h12190c.2.2.2
                rcases p12190_3 (m.d 0 1) (by simp) with h12208 | h12208
                · rcases p12190_3 (m.d 1 2) (by simp) with h12209 | h12209
                  · linarith only [h0, h12209, hlam]
                  · rcases p12190_3 (m.d 1 3) (by simp) with h12211 | h12211
                    · linarith only [h1, h12211, hlam]
                    · rcases p12190_3 (m.d 1 4) (by simp) with h12213 | h12213
                      · linarith only [h12213, hlam, p12190_0]
                      · rcases p12190_3 (m.d 1 5) (by simp) with h12215 | h12215
                        · linarith only [h12215, h3, hlam]
                        · linarith only [h12182, h12215, hlam]
                · linarith only [h12208, hlam, p12190_0]
              · have p12190_0 := h12190c.1
                have p12190_1 := h12190c.2.1
                have p12190_2 := h12190c.2.2.1
                have p12190_3 := h12190c.2.2.2
                rcases p12190_3 (m.d 0 1) (by simp) with h12219 | h12219
                · rcases p12190_3 (m.d 1 2) (by simp) with h12220 | h12220
                  · linarith only [h0, h12220, hlam]
                  · rcases p12190_3 (m.d 1 3) (by simp) with h12222 | h12222
                    · linarith only [h1, h12222, hlam]
                    · rcases p12190_3 (m.d 1 4) (by simp) with h12224 | h12224
                      · linarith only [h12224, h2, hlam]
                      · rcases p12190_3 (m.d 1 5) (by simp) with h12226 | h12226
                        · linarith only [h12226, hlam, p12190_0]
                        · rcases h3bigk with h12228c | h12228c | h12228c | h12228c | h12228c | h12228c | h12228c | h12228c | h12228c | h12228c | h12228c | h12228c | h12228c | h12228c | h12228c | h12228c | h12228c | h12228c | h12228c | h12228c | h12228c | h12228c | h12228c | h12228c | h12228c
                          · have p12228_0 := h12228c.1
                            have p12228_1 := h12228c.2.1
                            have p12228_2 := h12228c.2.2.1
                            have p12228_3 := h12228c.2.2.2
                            linarith only [hlam, p12228_0]
                          · have p12228_0 := h12228c.1
                            have p12228_1 := h12228c.2.1
                            have p12228_2 := h12228c.2.2.1
                            have p12228_3 := h12228c.2.2.2
                            rcases p12228_3 (m.d 0 3) (by simp) with h12230 | h12230
                            · rcases p12228_3 (m.d 1 3) (by simp) with h12231 | h12231
                              · linarith only [h1, h12231, hlam]
                              · rcases p12228_3 (m.d 2 3) (by simp) with h12233 | h12233
                                · rcases p12228_3 (m.d 3 4) (by simp) with h12234 | h12234
                                  · linarith only [h10361, h12234, hlam]
                                  · linarith only [h11304, h12234, hlam]
                                · linarith only [h11298, h12233, hlam]
                            · linarith only [h1, h12230, hlam]
                          · have p12228_0 := h12228c.1
                            have p12228_1 := h12228c.2.1
                            have p12228_2 := h12228c.2.2.1
                            have p12228_3 := h12228c.2.2.2
                            linarith only [h4, hlam, p12228_1]
                          · have p12228_0 := h12228c.1
                            have p12228_1 := h12228c.2.1
                            have p12228_2 := h12228c.2.2.1
                            have p12228_3 := h12228c.2.2.2
                            linarith only [h11298, h11304, h4, hc12, hc23, hlam, hphi, p12228_1]
                          · have p12228_0 := h12228c.1
                            have p12228_1 := h12228c.2.1
                            have p12228_2 := h12228c.2.2.1
                            have p12228_3 := h12228c.2.2.2
                            linarith only [h11298, h12178, h4, hc12, hc23, hlam, hphi, p12228_1]
                          · have p12228_0 := h12228c.1
                            have p12228_1 := h12228c.2.1
                            have p12228_2 := h12228c.2.2.1
                            have p12228_3 := h12228c.2.2.2
                            linarith only [h1, hlam, p12228_0]
                          · have p12228_0 := h12228c.1
                            have p12228_1 := h12228c.2.1
                            have p12228_2 := h12228c.2.2.1
                            have p12228_3 := h12228c.2.2.2
                            linarith only [hlam, p12228_0]
                          · have p12228_0 := h12228c.1
                            have p12228_1 := h12228c.2.1
                            have p12228_2 := h12228c.2.2.1
                            have p12228_3 := h12228c.2.2.2
                            linarith only [h11298, hlam, p12228_1]
                          · have p12228_0 := h12228c.1
                            have p12228_1 := h12228c.2.1
                            have p12228_2 := h12228c.2.2.1
                            have p12228_3 := h12228c.2.2.2
                            linarith only [h11304, hlam, p12228_0]
                          · have p12228_0 := h12228c.1
                            have p12228_1 := h12228c.2.1
                            have p12228_2 := h12228c.2.2.1
                            have p12228_3 := h12228c.2.2.2
                            linarith only [h12178, hlam, p12228_0]
                          · have p12228_0 := h12228c.1
                            have p12228_1 := h12228c.2.1
                            have p12228_2 := h12228c.2.2.1
                            have p12228_3 := h12228c.2.2.2
                            linarith only [h10361, h11298, h11304, hc12, hc23, hlam, hphi, p12228_1]
                          · have p12228_0 := h12228c.1
                            have p12228_1 := h12228c.2.1
                            have p12228_2 := h12228c.2.2.1
                            have p12228_3 := h12228c.2.2.2
                            rcases p12228_3 (m.d 0 3) (by simp) with h12248 | h12248
                            · linarith only [h12248, h4, hlam]
                            · linarith only [h1, h12248, hlam]
                          · have p12228_0 := h12228c.1
                            have p12228_1 := h12228c.2.1
                            have p12228_2 := h12228c.2.2.1
                            have p12228_3 := h12228c.2.2.2
                            linarith only [hlam, p12228_0]
                          · have p12228_0 := h12228c.1
                            have p12228_1 := h12228c.2.1
                            have p12228_2 := h12228c.2.2.1
                            have p12228_3 := h12228c.2.2.2
                            linarith only [h11298, h11304, hc12, hc23, hlam, hphi, p12228_1]
                          · have p12228_0 := h12228c.1
                            have p12228_1 := h12228c.2.1
                            have p12228_2 := h12228c.2.2.1
                            have p12228_3 := h12228c.2.2.2
                            linarith only [h11298, h11304, h12188, hc12, hc23, hlam, hphi, p12228_1]
                          · have p12228_0 := h12228c.1
                            have p12228_1 := h12228c.2.1
                            have p12228_2 := h12228c.2.2.1
                            have p12228_3 := h12228c.2.2.2
                            linarith only [h10361, hlam, p12228_0]
                          · have p12228_0 := h12228c.1
                            have p12228_1 := h12228c.2.1
                            have p12228_2 := h12228c.2.2.1
                            have p12228_3 := h12228c.2.2.2
                            linarith only [h10361, h11298, h12186, h8674, hc12, hc45, hlam, hphi, ht23, ht34, p12228_1]
                          · have p12228_0 := h12228c.1
                            have p12228_1 := h12228c.2.1
                            have p12228_2 := h12228c.2.2.1
                            have p12228_3 := h12228c.2.2.2
                            linarith only [h12184, hlam, p12228_0]
                          · have p12228_0 := h12228c.1
                            have p12228_1 := h12228c.2.1
                            have p12228_2 := h12228c.2.2.1
                            have p12228_3 := h12228c.2.2.2
                            linarith only [hlam, p12228_0]
                          · have p12228_0 := h12228c.1
                            have p12228_1 := h12228c.2.1
                            have p12228_2 := h12228c.2.2.1
                            have p12228_3 := h12228c.2.2.2
                            linarith only [h12188, hlam, p12228_1]
                          · have p12228_0 := h12228c.1
                            have p12228_1 := h12228c.2.1
                            have p12228_2 := h12228c.2.2.1
                            have p12228_3 := h12228c.2.2.2
                            linarith only [h10362, hlam, p12228_0]
                          · have p12228_0 := h12228c.1
                            have p12228_1 := h12228c.2.1
                            have p12228_2 := h12228c.2.2.1
                            have p12228_3 := h12228c.2.2.2
                            linarith only [h10362, h11298, h4, hc12, hc23, hlam, hphi, p12228_1]
                          · have p12228_0 := h12228c.1
                            have p12228_1 := h12228c.2.1
                            have p12228_2 := h12228c.2.2.1
                            have p12228_3 := h12228c.2.2.2
                            linarith only [h12185, hlam, p12228_0]
                          · have p12228_0 := h12228c.1
                            have p12228_1 := h12228c.2.1
                            have p12228_2 := h12228c.2.2.1
                            have p12228_3 := h12228c.2.2.2
                            linarith only [h10362, h11298, h11304, h4, hc12, hc23, hlam, hphi, p12228_1]
                          · have p12228_0 := h12228c.1
                            have p12228_1 := h12228c.2.1
                            have p12228_2 := h12228c.2.2.1
                            have p12228_3 := h12228c.2.2.2
                            linarith only [hlam, p12228_0]
                · linarith only [h12219, hlam, p12190_0]
              · have p12190_0 := h12190c.1
                have p12190_1 := h12190c.2.1
                have p12190_2 := h12190c.2.2.1
                have p12190_3 := h12190c.2.2.2
                linarith only [h0, hlam, p12190_0]
              · have p12190_0 := h12190c.1
                have p12190_1 := h12190c.2.1
                have p12190_2 := h12190c.2.2.1
                have p12190_3 := h12190c.2.2.2
                linarith only [hlam, p12190_0]
              · have p12190_0 := h12190c.1
                have p12190_1 := h12190c.2.1
                have p12190_2 := h12190c.2.2.1
                have p12190_3 := h12190c.2.2.2
                linarith only [h11298, hlam, p12190_0]
              · have p12190_0 := h12190c.1
                have p12190_1 := h12190c.2.1
                have p12190_2 := h12190c.2.2.1
                have p12190_3 := h12190c.2.2.2
                linarith only [h11300, hlam, p12190_0]
              · have p12190_0 := h12190c.1
                have p12190_1 := h12190c.2.1
                have p12190_2 := h12190c.2.2.1
                have p12190_3 := h12190c.2.2.2
                linarith only [h11302, hlam, p12190_0]
              · have p12190_0 := h12190c.1
                have p12190_1 := h12190c.2.1
                have p12190_2 := h12190c.2.2.1
                have p12190_3 := h12190c.2.2.2
                linarith only [h1, hlam, p12190_0]
              · have p12190_0 := h12190c.1
                have p12190_1 := h12190c.2.1
                have p12190_2 := h12190c.2.2.1
                have p12190_3 := h12190c.2.2.2
                linarith only [h11304, h12186, h2, h8674, hc12, hc45, hlam, hphi, ht23, ht34, p12190_1]
              · have p12190_0 := h12190c.1
                have p12190_1 := h12190c.2.1
                have p12190_2 := h12190c.2.2.1
                have p12190_3 := h12190c.2.2.2
                linarith only [hlam, p12190_0]
              · have p12190_0 := h12190c.1
                have p12190_1 := h12190c.2.1
                have p12190_2 := h12190c.2.2.1
                have p12190_3 := h12190c.2.2.2
                linarith only [h11304, hlam, p12190_1]
              · have p12190_0 := h12190c.1
                have p12190_1 := h12190c.2.1
                have p12190_2 := h12190c.2.2.1
                have p12190_3 := h12190c.2.2.2
                linarith only [h12178, hlam, p12190_1]
              · have p12190_0 := h12190c.1
                have p12190_1 := h12190c.2.1
                have p12190_2 := h12190c.2.2.1
                have p12190_3 := h12190c.2.2.2
                linarith only [h2, hlam, p12190_0]
              · have p12190_0 := h12190c.1
                have p12190_1 := h12190c.2.1
                have p12190_2 := h12190c.2.2.1
                have p12190_3 := h12190c.2.2.2
                linarith only [h12186, h2, h8674, hc12, hc45, hlam, hphi, ht23, ht34, p12190_1]
              · have p12190_0 := h12190c.1
                have p12190_1 := h12190c.2.1
                have p12190_2 := h12190c.2.2.1
                have p12190_3 := h12190c.2.2.2
                linarith only [h12186, h2, h8674, hc13, hc45, hlam, hphi, ht34, p12190_1]
              · have p12190_0 := h12190c.1
                have p12190_1 := h12190c.2.1
                have p12190_2 := h12190c.2.2.1
                have p12190_3 := h12190c.2.2.2
                linarith only [hlam, p12190_0]
              · have p12190_0 := h12190c.1
                have p12190_1 := h12190c.2.1
                have p12190_2 := h12190c.2.2.1
                have p12190_3 := h12190c.2.2.2
                linarith only [h12182, hlam, p12190_1]
              · have p12190_0 := h12190c.1
                have p12190_1 := h12190c.2.1
                have p12190_2 := h12190c.2.2.1
                have p12190_3 := h12190c.2.2.2
                linarith only [h3, hlam, p12190_0]
              · have p12190_0 := h12190c.1
                have p12190_1 := h12190c.2.1
                have p12190_2 := h12190c.2.2.1
                have p12190_3 := h12190c.2.2.2
                linarith only [h10362, h12178, h4, hc12, hc23, hlam, hphi, p12190_1]
              · have p12190_0 := h12190c.1
                have p12190_1 := h12190c.2.1
                have p12190_2 := h12190c.2.2.1
                have p12190_3 := h12190c.2.2.2
                linarith only [h10362, h11298, h12178, h4, hc12, hc23, hlam, hphi, p12190_1]
              · have p12190_0 := h12190c.1
                have p12190_1 := h12190c.2.1
                have p12190_2 := h12190c.2.2.1
                have p12190_3 := h12190c.2.2.2
                linarith only [h10362, h11300, h12178, h4, hc12, hc23, hlam, hphi, p12190_1]
              · have p12190_0 := h12190c.1
                have p12190_1 := h12190c.2.1
                have p12190_2 := h12190c.2.2.1
                have p12190_3 := h12190c.2.2.2
                linarith only [hlam, p12190_0]
        · linarith only [h10362, h12185, h4, hlam]
      · linarith only [h10361, h12184, h4, hlam]

set_option maxHeartbeats 6296000 in
set_option maxHeartbeats 6296000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg8674 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9870 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h10361 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10362 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h10363 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h11298 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h11300 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h11302 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h8674 := hg8674
  have h9870 := hg9870
  rcases m.htr 1 3 4 (by decide) (by decide) with h11304 | h11304
  · exact r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x1_x1_x1_x1_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg8674 hg9870 h10361 h10362 h10363 h11298 h11300 h11302 h11304
  · exact r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x1_x1_x1_x1_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg8674 hg9870 h10361 h10362 h10363 h11298 h11300 h11302 h11304

set_option maxHeartbeats 6296000 in
set_option maxHeartbeats 6296000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg8674 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9870 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h10361 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10362 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h10363 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h11298 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h11300 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h8674 := hg8674
  have h9870 := hg9870
  rcases m.htr 1 2 5 (by decide) (by decide) with h11302 | h11302
  · exact r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x1_x1_x1_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg8674 hg9870 h10361 h10362 h10363 h11298 h11300 h11302
  · exact r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x1_x1_x1_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg8674 hg9870 h10361 h10362 h10363 h11298 h11300 h11302

set_option maxHeartbeats 6296000 in
set_option maxHeartbeats 6296000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg8674 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9870 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h10361 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10362 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h10363 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h11298 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h8674 := hg8674
  have h9870 := hg9870
  rcases m.htr 1 2 4 (by decide) (by decide) with h11300 | h11300
  · exact r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x1_x1_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg8674 hg9870 h10361 h10362 h10363 h11298 h11300
  · exact r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x1_x1_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg8674 hg9870 h10361 h10362 h10363 h11298 h11300

set_option maxHeartbeats 6296000 in
set_option maxHeartbeats 6296000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg8674 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9870 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h10361 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10362 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h10363 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h8674 := hg8674
  have h9870 := hg9870
  rcases m.htr 1 2 3 (by decide) (by decide) with h11298 | h11298
  · exact r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x1_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg8674 hg9870 h10361 h10362 h10363 h11298
  · exact r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x1_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg8674 hg9870 h10361 h10362 h10363 h11298

set_option maxHeartbeats 6296000 in
set_option maxHeartbeats 6296000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg8674 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9870 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h10361 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10362 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h8674 := hg8674
  have h9870 := hg9870
  rcases m.htr 0 4 5 (by decide) (by decide) with h10363 | h10363
  · exact r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg8674 hg9870 h10361 h10362 h10363
  · exact r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg8674 hg9870 h10361 h10362 h10363

set_option maxHeartbeats 6296000 in
set_option maxHeartbeats 6296000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg8674 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9870 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h10361 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10362 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h8674 := hg8674
  have h9870 := hg9870
  rcases m.htr 0 4 5 (by decide) (by decide) with h12287 | h12287
  · linarith only [h10361, h10362, h12287, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h12289 | h12289
    · linarith only [h0, h12289, h4, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h12291 | h12291
      · linarith only [h0, h12291, h8674, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h12293 | h12293
        · linarith only [h0, h12293, h9870, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h12295 | h12295
          · rcases m.htr 1 3 5 (by decide) (by decide) with h12296 | h12296
            · linarith only [h1, h10362, h12296, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h12298 | h12298
              · linarith only [h12287, h12298, h2, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h12300 | h12300
                · rcases m.htr 2 3 5 (by decide) (by decide) with h12301 | h12301
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h12302 | h12302
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h12303 | h12303
                      · linarith only [h0, h1, h10362, h12287, h12295, h12301, h12303, h8674, hc12, hc23, hlam, hphi]
                      · rcases h1bigk with h12305c | h12305c | h12305c | h12305c | h12305c | h12305c | h12305c | h12305c | h12305c | h12305c | h12305c | h12305c | h12305c | h12305c | h12305c | h12305c | h12305c | h12305c | h12305c | h12305c | h12305c | h12305c | h12305c | h12305c | h12305c
                        · have p12305_0 := h12305c.1
                          have p12305_1 := h12305c.2.1
                          have p12305_2 := h12305c.2.2.1
                          have p12305_3 := h12305c.2.2.2
                          linarith only [hlam, p12305_0]
                        · have p12305_0 := h12305c.1
                          have p12305_1 := h12305c.2.1
                          have p12305_2 := h12305c.2.2.1
                          have p12305_3 := h12305c.2.2.2
                          rcases p12305_3 (m.d 0 1) (by simp) with h12307 | h12307
                          · rcases p12305_3 (m.d 1 2) (by simp) with h12308 | h12308
                            · linarith only [h12308, hlam, p12305_0]
                            · rcases p12305_3 (m.d 1 3) (by simp) with h12310 | h12310
                              · linarith only [h1, h12310, hlam]
                              · linarith only [h12289, h12310, hlam]
                          · linarith only [h12307, hlam, p12305_0]
                        · have p12305_0 := h12305c.1
                          have p12305_1 := h12305c.2.1
                          have p12305_2 := h12305c.2.2.1
                          have p12305_3 := h12305c.2.2.2
                          rcases p12305_3 (m.d 0 1) (by simp) with h12314 | h12314
                          · rcases p12305_3 (m.d 1 2) (by simp) with h12315 | h12315
                            · linarith only [h0, h12315, hlam]
                            · rcases p12305_3 (m.d 1 3) (by simp) with h12317 | h12317
                              · linarith only [h12317, hlam, p12305_0]
                              · rcases p12305_3 (m.d 1 4) (by simp) with h12319 | h12319
                                · linarith only [h12319, h2, hlam]
                                · rcases p12305_3 (m.d 1 5) (by simp) with h12321 | h12321
                                  · linarith only [h12321, h3, hlam]
                                  · linarith only [h12296, h12321, hlam]
                          · linarith only [h12314, hlam, p12305_0]
                        · have p12305_0 := h12305c.1
                          have p12305_1 := h12305c.2.1
                          have p12305_2 := h12305c.2.2.1
                          have p12305_3 := h12305c.2.2.2
                          rcases p12305_3 (m.d 0 1) (by simp) with h12325 | h12325
                          · rcases p12305_3 (m.d 1 2) (by simp) with h12326 | h12326
                            · linarith only [h0, h12326, hlam]
                            · rcases p12305_3 (m.d 1 3) (by simp) with h12328 | h12328
                              · linarith only [h1, h12328, hlam]
                              · linarith only [h12295, h12328, hlam]
                          · linarith only [h12325, hlam, p12305_0]
                        · have p12305_0 := h12305c.1
                          have p12305_1 := h12305c.2.1
                          have p12305_2 := h12305c.2.2.1
                          have p12305_3 := h12305c.2.2.2
                          rcases p12305_3 (m.d 0 1) (by simp) with h12332 | h12332
                          · rcases p12305_3 (m.d 1 2) (by simp) with h12333 | h12333
                            · linarith only [h0, h12333, hlam]
                            · rcases p12305_3 (m.d 1 3) (by simp) with h12335 | h12335
                              · linarith only [h1, h12335, hlam]
                              · rcases p12305_3 (m.d 1 4) (by simp) with h12337 | h12337
                                · linarith only [h12337, h2, hlam]
                                · rcases p12305_3 (m.d 1 5) (by simp) with h12339 | h12339
                                  · linarith only [h12339, hlam, p12305_0]
                                  · rcases h3bigk with h12341c | h12341c | h12341c | h12341c | h12341c | h12341c | h12341c | h12341c | h12341c | h12341c | h12341c | h12341c | h12341c | h12341c | h12341c | h12341c | h12341c | h12341c | h12341c | h12341c | h12341c | h12341c | h12341c | h12341c | h12341c
                                    · have p12341_0 := h12341c.1
                                      have p12341_1 := h12341c.2.1
                                      have p12341_2 := h12341c.2.2.1
                                      have p12341_3 := h12341c.2.2.2
                                      linarith only [hlam, p12341_0]
                                    · have p12341_0 := h12341c.1
                                      have p12341_1 := h12341c.2.1
                                      have p12341_2 := h12341c.2.2.1
                                      have p12341_3 := h12341c.2.2.2
                                      linarith only [h10362, h12295, h12300, h12302, h12303, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12341_1]
                                    · have p12341_0 := h12341c.1
                                      have p12341_1 := h12341c.2.1
                                      have p12341_2 := h12341c.2.2.1
                                      have p12341_3 := h12341c.2.2.2
                                      linarith only [h4, hlam, p12341_1]
                                    · have p12341_0 := h12341c.1
                                      have p12341_1 := h12341c.2.1
                                      have p12341_2 := h12341c.2.2.1
                                      have p12341_3 := h12341c.2.2.2
                                      linarith only [h10362, h12300, h12302, h12303, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12341_1]
                                    · have p12341_0 := h12341c.1
                                      have p12341_1 := h12341c.2.1
                                      have p12341_2 := h12341c.2.2.1
                                      have p12341_3 := h12341c.2.2.2
                                      linarith only [h10362, hlam, p12341_0]
                                    · have p12341_0 := h12341c.1
                                      have p12341_1 := h12341c.2.1
                                      have p12341_2 := h12341c.2.2.1
                                      have p12341_3 := h12341c.2.2.2
                                      linarith only [h1, hlam, p12341_0]
                                    · have p12341_0 := h12341c.1
                                      have p12341_1 := h12341c.2.1
                                      have p12341_2 := h12341c.2.2.1
                                      have p12341_3 := h12341c.2.2.2
                                      linarith only [hlam, p12341_0]
                                    · have p12341_0 := h12341c.1
                                      have p12341_1 := h12341c.2.1
                                      have p12341_2 := h12341c.2.2.1
                                      have p12341_3 := h12341c.2.2.2
                                      linarith only [h12289, hlam, p12341_1]
                                    · have p12341_0 := h12341c.1
                                      have p12341_1 := h12341c.2.1
                                      have p12341_2 := h12341c.2.2.1
                                      have p12341_3 := h12341c.2.2.2
                                      linarith only [h1, h10362, h12300, h12302, h12303, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12341_1]
                                    · have p12341_0 := h12341c.1
                                      have p12341_1 := h12341c.2.1
                                      have p12341_2 := h12341c.2.2.1
                                      have p12341_3 := h12341c.2.2.2
                                      linarith only [h12296, hlam, p12341_0]
                                    · have p12341_0 := h12341c.1
                                      have p12341_1 := h12341c.2.1
                                      have p12341_2 := h12341c.2.2.1
                                      have p12341_3 := h12341c.2.2.2
                                      rcases p12341_3 (m.d 0 3) (by simp) with h12352 | h12352
                                      · linarith only [h12352, h4, hlam]
                                      · rcases p12341_3 (m.d 1 3) (by simp) with h12354 | h12354
                                        · linarith only [h12289, h12354, hlam]
                                        · rcases p12341_3 (m.d 2 3) (by simp) with h12356 | h12356
                                          · rcases p12341_3 (m.d 3 4) (by simp) with h12357 | h12357
                                            · linarith only [h12300, h12357, hlam]
                                            · rcases p12341_3 (m.d 3 5) (by simp) with h12359 | h12359
                                              · linarith only [h12301, h12359, hlam]
                                              · linarith only [h10362, h12359, hlam]
                                          · linarith only [h12356, h4, hlam]
                                    · have p12341_0 := h12341c.1
                                      have p12341_1 := h12341c.2.1
                                      have p12341_2 := h12341c.2.2.1
                                      have p12341_3 := h12341c.2.2.2
                                      rcases p12341_3 (m.d 0 3) (by simp) with h12363 | h12363
                                      · linarith only [h12363, h4, hlam]
                                      · linarith only [h1, h12363, hlam]
                                    · have p12341_0 := h12341c.1
                                      have p12341_1 := h12341c.2.1
                                      have p12341_2 := h12341c.2.2.1
                                      have p12341_3 := h12341c.2.2.2
                                      linarith only [hlam, p12341_0]
                                    · have p12341_0 := h12341c.1
                                      have p12341_1 := h12341c.2.1
                                      have p12341_2 := h12341c.2.2.1
                                      have p12341_3 := h12341c.2.2.2
                                      linarith only [h10361, h10362, h12300, h12302, h12303, hlam, p12341_2]
                                    · have p12341_0 := h12341c.1
                                      have p12341_1 := h12341c.2.1
                                      have p12341_2 := h12341c.2.2.1
                                      have p12341_3 := h12341c.2.2.2
                                      linarith only [h1, h10362, h12295, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12341_1]
                                    · have p12341_0 := h12341c.1
                                      have p12341_1 := h12341c.2.1
                                      have p12341_2 := h12341c.2.2.1
                                      have p12341_3 := h12341c.2.2.2
                                      linarith only [h10361, hlam, p12341_0]
                                    · have p12341_0 := h12341c.1
                                      have p12341_1 := h12341c.2.1
                                      have p12341_2 := h12341c.2.2.1
                                      have p12341_3 := h12341c.2.2.2
                                      linarith only [h12295, hlam, p12341_0]
                                    · have p12341_0 := h12341c.1
                                      have p12341_1 := h12341c.2.1
                                      have p12341_2 := h12341c.2.2.1
                                      have p12341_3 := h12341c.2.2.2
                                      linarith only [h12300, hlam, p12341_0]
                                    · have p12341_0 := h12341c.1
                                      have p12341_1 := h12341c.2.1
                                      have p12341_2 := h12341c.2.2.1
                                      have p12341_3 := h12341c.2.2.2
                                      linarith only [hlam, p12341_0]
                                    · have p12341_0 := h12341c.1
                                      have p12341_1 := h12341c.2.1
                                      have p12341_2 := h12341c.2.2.1
                                      have p12341_3 := h12341c.2.2.2
                                      linarith only [h12303, hlam, p12341_1]
                                    · have p12341_0 := h12341c.1
                                      have p12341_1 := h12341c.2.1
                                      have p12341_2 := h12341c.2.2.1
                                      have p12341_3 := h12341c.2.2.2
                                      linarith only [h1, h12295, h12301, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12341_1]
                                    · have p12341_0 := h12341c.1
                                      have p12341_1 := h12341c.2.1
                                      have p12341_2 := h12341c.2.2.1
                                      have p12341_3 := h12341c.2.2.2
                                      linarith only [h12295, h12301, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12341_1]
                                    · have p12341_0 := h12341c.1
                                      have p12341_1 := h12341c.2.1
                                      have p12341_2 := h12341c.2.2.1
                                      have p12341_3 := h12341c.2.2.2
                                      linarith only [h12301, hlam, p12341_0]
                                    · have p12341_0 := h12341c.1
                                      have p12341_1 := h12341c.2.1
                                      have p12341_2 := h12341c.2.2.1
                                      have p12341_3 := h12341c.2.2.2
                                      rcases p12341_3 (m.d 0 3) (by simp) with h12377 | h12377
                                      · linarith only [h10362, h12377, hlam]
                                      · linarith only [h10361, h12377, hlam]
                                    · have p12341_0 := h12341c.1
                                      have p12341_1 := h12341c.2.1
                                      have p12341_2 := h12341c.2.2.1
                                      have p12341_3 := h12341c.2.2.2
                                      linarith only [hlam, p12341_0]
                          · linarith only [h12332, hlam, p12305_0]
                        · have p12305_0 := h12305c.1
                          have p12305_1 := h12305c.2.1
                          have p12305_2 := h12305c.2.2.1
                          have p12305_3 := h12305c.2.2.2
                          linarith only [h0, hlam, p12305_0]
                        · have p12305_0 := h12305c.1
                          have p12305_1 := h12305c.2.1
                          have p12305_2 := h12305c.2.2.1
                          have p12305_3 := h12305c.2.2.2
                          linarith only [hlam, p12305_0]
                        · have p12305_0 := h12305c.1
                          have p12305_1 := h12305c.2.1
                          have p12305_2 := h12305c.2.2.1
                          have p12305_3 := h12305c.2.2.2
                          linarith only [h12289, hlam, p12305_0]
                        · have p12305_0 := h12305c.1
                          have p12305_1 := h12305c.2.1
                          have p12305_2 := h12305c.2.2.1
                          have p12305_3 := h12305c.2.2.2
                          linarith only [h12291, hlam, p12305_0]
                        · have p12305_0 := h12305c.1
                          have p12305_1 := h12305c.2.1
                          have p12305_2 := h12305c.2.2.1
                          have p12305_3 := h12305c.2.2.2
                          linarith only [h12293, hlam, p12305_0]
                        · have p12305_0 := h12305c.1
                          have p12305_1 := h12305c.2.1
                          have p12305_2 := h12305c.2.2.1
                          have p12305_3 := h12305c.2.2.2
                          linarith only [h1, hlam, p12305_0]
                        · have p12305_0 := h12305c.1
                          have p12305_1 := h12305c.2.1
                          have p12305_2 := h12305c.2.2.1
                          have p12305_3 := h12305c.2.2.2
                          linarith only [h1, h10362, h12300, h12302, h12303, hc12, hc23, hlam, hphi, p12305_1]
                        · have p12305_0 := h12305c.1
                          have p12305_1 := h12305c.2.1
                          have p12305_2 := h12305c.2.2.1
                          have p12305_3 := h12305c.2.2.2
                          linarith only [hlam, p12305_0]
                        · have p12305_0 := h12305c.1
                          have p12305_1 := h12305c.2.1
                          have p12305_2 := h12305c.2.2.1
                          have p12305_3 := h12305c.2.2.2
                          linarith only [h1, h10362, h12300, h12302, h12303, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12305_1]
                        · have p12305_0 := h12305c.1
                          have p12305_1 := h12305c.2.1
                          have p12305_2 := h12305c.2.2.1
                          have p12305_3 := h12305c.2.2.2
                          linarith only [h12296, hlam, p12305_1]
                        · have p12305_0 := h12305c.1
                          have p12305_1 := h12305c.2.1
                          have p12305_2 := h12305c.2.2.1
                          have p12305_3 := h12305c.2.2.2
                          linarith only [h2, hlam, p12305_0]
                        · have p12305_0 := h12305c.1
                          have p12305_1 := h12305c.2.1
                          have p12305_2 := h12305c.2.2.1
                          have p12305_3 := h12305c.2.2.2
                          linarith only [h10361, h10362, h12300, h12302, h12303, h2, hc12, hc23, hlam, hphi, p12305_1]
                        · have p12305_0 := h12305c.1
                          have p12305_1 := h12305c.2.1
                          have p12305_2 := h12305c.2.2.1
                          have p12305_3 := h12305c.2.2.2
                          linarith only [h12295, hlam, p12305_0]
                        · have p12305_0 := h12305c.1
                          have p12305_1 := h12305c.2.1
                          have p12305_2 := h12305c.2.2.1
                          have p12305_3 := h12305c.2.2.2
                          linarith only [hlam, p12305_0]
                        · have p12305_0 := h12305c.1
                          have p12305_1 := h12305c.2.1
                          have p12305_2 := h12305c.2.2.1
                          have p12305_3 := h12305c.2.2.2
                          linarith only [h12298, hlam, p12305_1]
                        · have p12305_0 := h12305c.1
                          have p12305_1 := h12305c.2.1
                          have p12305_2 := h12305c.2.2.1
                          have p12305_3 := h12305c.2.2.2
                          linarith only [h3, hlam, p12305_0]
                        · have p12305_0 := h12305c.1
                          have p12305_1 := h12305c.2.1
                          have p12305_2 := h12305c.2.2.1
                          have p12305_3 := h12305c.2.2.2
                          linarith only [h10362, h12300, h12302, h12303, h3, hc12, hc23, hlam, hphi, p12305_1]
                        · have p12305_0 := h12305c.1
                          have p12305_1 := h12305c.2.1
                          have p12305_2 := h12305c.2.2.1
                          have p12305_3 := h12305c.2.2.2
                          linarith only [h10362, h12289, h12300, h12302, h12303, h3, hc12, hc23, hlam, hphi, p12305_1]
                        · have p12305_0 := h12305c.1
                          have p12305_1 := h12305c.2.1
                          have p12305_2 := h12305c.2.2.1
                          have p12305_3 := h12305c.2.2.2
                          linarith only [h10362, h12291, h12300, h12302, h12303, h3, hc12, hc23, hlam, hphi, p12305_1]
                        · have p12305_0 := h12305c.1
                          have p12305_1 := h12305c.2.1
                          have p12305_2 := h12305c.2.2.1
                          have p12305_3 := h12305c.2.2.2
                          linarith only [hlam, p12305_0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h12402 | h12402
                      · linarith only [h1, h12295, h12302, h12402, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases h1bigk with h12404c | h12404c | h12404c | h12404c | h12404c | h12404c | h12404c | h12404c | h12404c | h12404c | h12404c | h12404c | h12404c | h12404c | h12404c | h12404c | h12404c | h12404c | h12404c | h12404c | h12404c | h12404c | h12404c | h12404c | h12404c
                        · have p12404_0 := h12404c.1
                          have p12404_1 := h12404c.2.1
                          have p12404_2 := h12404c.2.2.1
                          have p12404_3 := h12404c.2.2.2
                          linarith only [hlam, p12404_0]
                        · have p12404_0 := h12404c.1
                          have p12404_1 := h12404c.2.1
                          have p12404_2 := h12404c.2.2.1
                          have p12404_3 := h12404c.2.2.2
                          rcases p12404_3 (m.d 0 1) (by simp) with h12406 | h12406
                          · rcases p12404_3 (m.d 1 2) (by simp) with h12407 | h12407
                            · linarith only [h12407, hlam, p12404_0]
                            · rcases p12404_3 (m.d 1 3) (by simp) with h12409 | h12409
                              · linarith only [h1, h12409, hlam]
                              · linarith only [h12289, h12409, hlam]
                          · linarith only [h12406, hlam, p12404_0]
                        · have p12404_0 := h12404c.1
                          have p12404_1 := h12404c.2.1
                          have p12404_2 := h12404c.2.2.1
                          have p12404_3 := h12404c.2.2.2
                          rcases p12404_3 (m.d 0 1) (by simp) with h12413 | h12413
                          · rcases p12404_3 (m.d 1 2) (by simp) with h12414 | h12414
                            · linarith only [h0, h12414, hlam]
                            · rcases p12404_3 (m.d 1 3) (by simp) with h12416 | h12416
                              · linarith only [h12416, hlam, p12404_0]
                              · rcases p12404_3 (m.d 1 4) (by simp) with h12418 | h12418
                                · linarith only [h12418, h2, hlam]
                                · rcases p12404_3 (m.d 1 5) (by simp) with h12420 | h12420
                                  · linarith only [h12420, h3, hlam]
                                  · linarith only [h12296, h12420, hlam]
                          · linarith only [h12413, hlam, p12404_0]
                        · have p12404_0 := h12404c.1
                          have p12404_1 := h12404c.2.1
                          have p12404_2 := h12404c.2.2.1
                          have p12404_3 := h12404c.2.2.2
                          rcases p12404_3 (m.d 0 1) (by simp) with h12424 | h12424
                          · rcases p12404_3 (m.d 1 2) (by simp) with h12425 | h12425
                            · linarith only [h0, h12425, hlam]
                            · rcases p12404_3 (m.d 1 3) (by simp) with h12427 | h12427
                              · linarith only [h1, h12427, hlam]
                              · linarith only [h12295, h12427, hlam]
                          · linarith only [h12424, hlam, p12404_0]
                        · have p12404_0 := h12404c.1
                          have p12404_1 := h12404c.2.1
                          have p12404_2 := h12404c.2.2.1
                          have p12404_3 := h12404c.2.2.2
                          rcases p12404_3 (m.d 0 1) (by simp) with h12431 | h12431
                          · rcases p12404_3 (m.d 1 2) (by simp) with h12432 | h12432
                            · linarith only [h0, h12432, hlam]
                            · rcases p12404_3 (m.d 1 3) (by simp) with h12434 | h12434
                              · linarith only [h1, h12434, hlam]
                              · rcases p12404_3 (m.d 1 4) (by simp) with h12436 | h12436
                                · linarith only [h12436, h2, hlam]
                                · rcases p12404_3 (m.d 1 5) (by simp) with h12438 | h12438
                                  · linarith only [h12438, hlam, p12404_0]
                                  · rcases h3bigk with h12440c | h12440c | h12440c | h12440c | h12440c | h12440c | h12440c | h12440c | h12440c | h12440c | h12440c | h12440c | h12440c | h12440c | h12440c | h12440c | h12440c | h12440c | h12440c | h12440c | h12440c | h12440c | h12440c | h12440c | h12440c
                                    · have p12440_0 := h12440c.1
                                      have p12440_1 := h12440c.2.1
                                      have p12440_2 := h12440c.2.2.1
                                      have p12440_3 := h12440c.2.2.2
                                      linarith only [hlam, p12440_0]
                                    · have p12440_0 := h12440c.1
                                      have p12440_1 := h12440c.2.1
                                      have p12440_2 := h12440c.2.2.1
                                      have p12440_3 := h12440c.2.2.2
                                      linarith only [h10362, h12301, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p12440_1]
                                    · have p12440_0 := h12440c.1
                                      have p12440_1 := h12440c.2.1
                                      have p12440_2 := h12440c.2.2.1
                                      have p12440_3 := h12440c.2.2.2
                                      linarith only [h4, hlam, p12440_1]
                                    · have p12440_0 := h12440c.1
                                      have p12440_1 := h12440c.2.1
                                      have p12440_2 := h12440c.2.2.1
                                      have p12440_3 := h12440c.2.2.2
                                      linarith only [h10362, h12301, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12440_1]
                                    · have p12440_0 := h12440c.1
                                      have p12440_1 := h12440c.2.1
                                      have p12440_2 := h12440c.2.2.1
                                      have p12440_3 := h12440c.2.2.2
                                      linarith only [h10362, hlam, p12440_0]
                                    · have p12440_0 := h12440c.1
                                      have p12440_1 := h12440c.2.1
                                      have p12440_2 := h12440c.2.2.1
                                      have p12440_3 := h12440c.2.2.2
                                      linarith only [h1, hlam, p12440_0]
                                    · have p12440_0 := h12440c.1
                                      have p12440_1 := h12440c.2.1
                                      have p12440_2 := h12440c.2.2.1
                                      have p12440_3 := h12440c.2.2.2
                                      linarith only [hlam, p12440_0]
                                    · have p12440_0 := h12440c.1
                                      have p12440_1 := h12440c.2.1
                                      have p12440_2 := h12440c.2.2.1
                                      have p12440_3 := h12440c.2.2.2
                                      linarith only [h12289, hlam, p12440_1]
                                    · have p12440_0 := h12440c.1
                                      have p12440_1 := h12440c.2.1
                                      have p12440_2 := h12440c.2.2.1
                                      have p12440_3 := h12440c.2.2.2
                                      linarith only [h1, h10362, h12301, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12440_1]
                                    · have p12440_0 := h12440c.1
                                      have p12440_1 := h12440c.2.1
                                      have p12440_2 := h12440c.2.2.1
                                      have p12440_3 := h12440c.2.2.2
                                      linarith only [h12296, hlam, p12440_0]
                                    · have p12440_0 := h12440c.1
                                      have p12440_1 := h12440c.2.1
                                      have p12440_2 := h12440c.2.2.1
                                      have p12440_3 := h12440c.2.2.2
                                      rcases p12440_3 (m.d 0 3) (by simp) with h12451 | h12451
                                      · linarith only [h12451, h4, hlam]
                                      · rcases p12440_3 (m.d 1 3) (by simp) with h12453 | h12453
                                        · linarith only [h12289, h12453, hlam]
                                        · rcases p12440_3 (m.d 2 3) (by simp) with h12455 | h12455
                                          · rcases p12440_3 (m.d 3 4) (by simp) with h12456 | h12456
                                            · linarith only [h12300, h12456, hlam]
                                            · rcases p12440_3 (m.d 3 5) (by simp) with h12458 | h12458
                                              · linarith only [h12301, h12458, hlam]
                                              · linarith only [h10362, h12458, hlam]
                                          · linarith only [h12455, h4, hlam]
                                    · have p12440_0 := h12440c.1
                                      have p12440_1 := h12440c.2.1
                                      have p12440_2 := h12440c.2.2.1
                                      have p12440_3 := h12440c.2.2.2
                                      rcases p12440_3 (m.d 0 3) (by simp) with h12462 | h12462
                                      · linarith only [h12462, h4, hlam]
                                      · linarith only [h1, h12462, hlam]
                                    · have p12440_0 := h12440c.1
                                      have p12440_1 := h12440c.2.1
                                      have p12440_2 := h12440c.2.2.1
                                      have p12440_3 := h12440c.2.2.2
                                      linarith only [hlam, p12440_0]
                                    · have p12440_0 := h12440c.1
                                      have p12440_1 := h12440c.2.1
                                      have p12440_2 := h12440c.2.2.1
                                      have p12440_3 := h12440c.2.2.2
                                      linarith only [h10361, h10362, h12301, hlam, p12440_2]
                                    · have p12440_0 := h12440c.1
                                      have p12440_1 := h12440c.2.1
                                      have p12440_2 := h12440c.2.2.1
                                      have p12440_3 := h12440c.2.2.2
                                      linarith only [h10361, h10362, h12291, h2, hc12, hc23, hlam, hphi, p12440_1]
                                    · have p12440_0 := h12440c.1
                                      have p12440_1 := h12440c.2.1
                                      have p12440_2 := h12440c.2.2.1
                                      have p12440_3 := h12440c.2.2.2
                                      linarith only [h10361, hlam, p12440_0]
                                    · have p12440_0 := h12440c.1
                                      have p12440_1 := h12440c.2.1
                                      have p12440_2 := h12440c.2.2.1
                                      have p12440_3 := h12440c.2.2.2
                                      linarith only [h12295, hlam, p12440_0]
                                    · have p12440_0 := h12440c.1
                                      have p12440_1 := h12440c.2.1
                                      have p12440_2 := h12440c.2.2.1
                                      have p12440_3 := h12440c.2.2.2
                                      linarith only [h12300, hlam, p12440_0]
                                    · have p12440_0 := h12440c.1
                                      have p12440_1 := h12440c.2.1
                                      have p12440_2 := h12440c.2.2.1
                                      have p12440_3 := h12440c.2.2.2
                                      linarith only [hlam, p12440_0]
                                    · have p12440_0 := h12440c.1
                                      have p12440_1 := h12440c.2.1
                                      have p12440_2 := h12440c.2.2.1
                                      have p12440_3 := h12440c.2.2.2
                                      linarith only [h12402, hlam, p12440_1]
                                    · have p12440_0 := h12440c.1
                                      have p12440_1 := h12440c.2.1
                                      have p12440_2 := h12440c.2.2.1
                                      have p12440_3 := h12440c.2.2.2
                                      linarith only [h1, h12295, h12301, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12440_1]
                                    · have p12440_0 := h12440c.1
                                      have p12440_1 := h12440c.2.1
                                      have p12440_2 := h12440c.2.2.1
                                      have p12440_3 := h12440c.2.2.2
                                      linarith only [h12295, h12301, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p12440_1]
                                    · have p12440_0 := h12440c.1
                                      have p12440_1 := h12440c.2.1
                                      have p12440_2 := h12440c.2.2.1
                                      have p12440_3 := h12440c.2.2.2
                                      linarith only [h12301, hlam, p12440_0]
                                    · have p12440_0 := h12440c.1
                                      have p12440_1 := h12440c.2.1
                                      have p12440_2 := h12440c.2.2.1
                                      have p12440_3 := h12440c.2.2.2
                                      rcases p12440_3 (m.d 0 3) (by simp) with h12476 | h12476
                                      · linarith only [h10362, h12476, hlam]
                                      · linarith only [h10361, h12476, hlam]
                                    · have p12440_0 := h12440c.1
                                      have p12440_1 := h12440c.2.1
                                      have p12440_2 := h12440c.2.2.1
                                      have p12440_3 := h12440c.2.2.2
                                      linarith only [hlam, p12440_0]
                          · linarith only [h12431, hlam, p12404_0]
                        · have p12404_0 := h12404c.1
                          have p12404_1 := h12404c.2.1
                          have p12404_2 := h12404c.2.2.1
                          have p12404_3 := h12404c.2.2.2
                          linarith only [h0, hlam, p12404_0]
                        · have p12404_0 := h12404c.1
                          have p12404_1 := h12404c.2.1
                          have p12404_2 := h12404c.2.2.1
                          have p12404_3 := h12404c.2.2.2
                          linarith only [hlam, p12404_0]
                        · have p12404_0 := h12404c.1
                          have p12404_1 := h12404c.2.1
                          have p12404_2 := h12404c.2.2.1
                          have p12404_3 := h12404c.2.2.2
                          linarith only [h12289, hlam, p12404_0]
                        · have p12404_0 := h12404c.1
                          have p12404_1 := h12404c.2.1
                          have p12404_2 := h12404c.2.2.1
                          have p12404_3 := h12404c.2.2.2
                          linarith only [h12291, hlam, p12404_0]
                        · have p12404_0 := h12404c.1
                          have p12404_1 := h12404c.2.1
                          have p12404_2 := h12404c.2.2.1
                          have p12404_3 := h12404c.2.2.2
                          linarith only [h12293, hlam, p12404_0]
                        · have p12404_0 := h12404c.1
                          have p12404_1 := h12404c.2.1
                          have p12404_2 := h12404c.2.2.1
                          have p12404_3 := h12404c.2.2.2
                          linarith only [h1, hlam, p12404_0]
                        · have p12404_0 := h12404c.1
                          have p12404_1 := h12404c.2.1
                          have p12404_2 := h12404c.2.2.1
                          have p12404_3 := h12404c.2.2.2
                          linarith only [h1, h10362, h12301, hc12, hc23, hlam, hphi, p12404_1]
                        · have p12404_0 := h12404c.1
                          have p12404_1 := h12404c.2.1
                          have p12404_2 := h12404c.2.2.1
                          have p12404_3 := h12404c.2.2.2
                          linarith only [hlam, p12404_0]
                        · have p12404_0 := h12404c.1
                          have p12404_1 := h12404c.2.1
                          have p12404_2 := h12404c.2.2.1
                          have p12404_3 := h12404c.2.2.2
                          linarith only [h1, h10362, h12291, h12301, hc12, hc23, hlam, hphi, p12404_1]
                        · have p12404_0 := h12404c.1
                          have p12404_1 := h12404c.2.1
                          have p12404_2 := h12404c.2.2.1
                          have p12404_3 := h12404c.2.2.2
                          linarith only [h12296, hlam, p12404_1]
                        · have p12404_0 := h12404c.1
                          have p12404_1 := h12404c.2.1
                          have p12404_2 := h12404c.2.2.1
                          have p12404_3 := h12404c.2.2.2
                          linarith only [h2, hlam, p12404_0]
                        · have p12404_0 := h12404c.1
                          have p12404_1 := h12404c.2.1
                          have p12404_2 := h12404c.2.2.1
                          have p12404_3 := h12404c.2.2.2
                          linarith only [h10361, h10362, h12301, h2, hc12, hc23, hlam, hphi, p12404_1]
                        · have p12404_0 := h12404c.1
                          have p12404_1 := h12404c.2.1
                          have p12404_2 := h12404c.2.2.1
                          have p12404_3 := h12404c.2.2.2
                          linarith only [h12295, hlam, p12404_0]
                        · have p12404_0 := h12404c.1
                          have p12404_1 := h12404c.2.1
                          have p12404_2 := h12404c.2.2.1
                          have p12404_3 := h12404c.2.2.2
                          linarith only [hlam, p12404_0]
                        · have p12404_0 := h12404c.1
                          have p12404_1 := h12404c.2.1
                          have p12404_2 := h12404c.2.2.1
                          have p12404_3 := h12404c.2.2.2
                          linarith only [h12298, hlam, p12404_1]
                        · have p12404_0 := h12404c.1
                          have p12404_1 := h12404c.2.1
                          have p12404_2 := h12404c.2.2.1
                          have p12404_3 := h12404c.2.2.2
                          linarith only [h3, hlam, p12404_0]
                        · have p12404_0 := h12404c.1
                          have p12404_1 := h12404c.2.1
                          have p12404_2 := h12404c.2.2.1
                          have p12404_3 := h12404c.2.2.2
                          linarith only [h10362, h12301, h3, hc12, hc23, hlam, hphi, p12404_1]
                        · have p12404_0 := h12404c.1
                          have p12404_1 := h12404c.2.1
                          have p12404_2 := h12404c.2.2.1
                          have p12404_3 := h12404c.2.2.2
                          linarith only [h10362, h12289, h12301, h3, hc12, hc23, hlam, hphi, p12404_1]
                        · have p12404_0 := h12404c.1
                          have p12404_1 := h12404c.2.1
                          have p12404_2 := h12404c.2.2.1
                          have p12404_3 := h12404c.2.2.2
                          linarith only [h10362, h12291, h12301, h3, hc12, hc23, hlam, hphi, p12404_1]
                        · have p12404_0 := h12404c.1
                          have p12404_1 := h12404c.2.1
                          have p12404_2 := h12404c.2.2.1
                          have p12404_3 := h12404c.2.2.2
                          linarith only [hlam, p12404_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h12501 | h12501
                    · linarith only [h12287, h12291, h12300, h12301, h12501, h2, hc12, hc35, hlam, hphi, ht23]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h12503 | h12503
                      · linarith only [h0, h1, h12295, h12501, h12503, h8674, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases h1bigk with h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c
                        · have p12505_0 := h12505c.1
                          have p12505_1 := h12505c.2.1
                          have p12505_2 := h12505c.2.2.1
                          have p12505_3 := h12505c.2.2.2
                          linarith only [hlam, p12505_0]
                        · have p12505_0 := h12505c.1
                          have p12505_1 := h12505c.2.1
                          have p12505_2 := h12505c.2.2.1
                          have p12505_3 := h12505c.2.2.2
                          rcases p12505_3 (m.d 0 1) (by simp) with h12507 | h12507
                          · rcases p12505_3 (m.d 1 2) (by simp) with h12508 | h12508
                            · linarith only [h12508, hlam, p12505_0]
                            · rcases p12505_3 (m.d 1 3) (by simp) with h12510 | h12510
                              · linarith only [h1, h12510, hlam]
                              · linarith only [h12289, h12510, hlam]
                          · linarith only [h12507, hlam, p12505_0]
                        · have p12505_0 := h12505c.1
                          have p12505_1 := h12505c.2.1
                          have p12505_2 := h12505c.2.2.1
                          have p12505_3 := h12505c.2.2.2
                          rcases p12505_3 (m.d 0 1) (by simp) with h12514 | h12514
                          · rcases p12505_3 (m.d 1 2) (by simp) with h12515 | h12515
                            · linarith only [h0, h12515, hlam]
                            · rcases p12505_3 (m.d 1 3) (by simp) with h12517 | h12517
                              · linarith only [h12517, hlam, p12505_0]
                              · rcases p12505_3 (m.d 1 4) (by simp) with h12519 | h12519
                                · linarith only [h12519, h2, hlam]
                                · rcases p12505_3 (m.d 1 5) (by simp) with h12521 | h12521
                                  · linarith only [h12521, h3, hlam]
                                  · linarith only [h12296, h12521, hlam]
                          · linarith only [h12514, hlam, p12505_0]
                        · have p12505_0 := h12505c.1
                          have p12505_1 := h12505c.2.1
                          have p12505_2 := h12505c.2.2.1
                          have p12505_3 := h12505c.2.2.2
                          rcases p12505_3 (m.d 0 1) (by simp) with h12525 | h12525
                          · rcases p12505_3 (m.d 1 2) (by simp) with h12526 | h12526
                            · linarith only [h0, h12526, hlam]
                            · rcases p12505_3 (m.d 1 3) (by simp) with h12528 | h12528
                              · linarith only [h1, h12528, hlam]
                              · linarith only [h12295, h12528, hlam]
                          · linarith only [h12525, hlam, p12505_0]
                        · have p12505_0 := h12505c.1
                          have p12505_1 := h12505c.2.1
                          have p12505_2 := h12505c.2.2.1
                          have p12505_3 := h12505c.2.2.2
                          rcases p12505_3 (m.d 0 1) (by simp) with h12532 | h12532
                          · rcases p12505_3 (m.d 1 2) (by simp) with h12533 | h12533
                            · linarith only [h0, h12533, hlam]
                            · rcases p12505_3 (m.d 1 3) (by simp) with h12535 | h12535
                              · linarith only [h1, h12535, hlam]
                              · rcases p12505_3 (m.d 1 4) (by simp) with h12537 | h12537
                                · linarith only [h12537, h2, hlam]
                                · rcases p12505_3 (m.d 1 5) (by simp) with h12539 | h12539
                                  · linarith only [h12539, hlam, p12505_0]
                                  · rcases h3bigk with h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c | h12541c
                                    · have p12541_0 := h12541c.1
                                      have p12541_1 := h12541c.2.1
                                      have p12541_2 := h12541c.2.2.1
                                      have p12541_3 := h12541c.2.2.2
                                      linarith only [hlam, p12541_0]
                                    · have p12541_0 := h12541c.1
                                      have p12541_1 := h12541c.2.1
                                      have p12541_2 := h12541c.2.2.1
                                      have p12541_3 := h12541c.2.2.2
                                      linarith only [h12301, h12503, h4, hc13, hc45, hlam, hphi, ht34, p12541_1]
                                    · have p12541_0 := h12541c.1
                                      have p12541_1 := h12541c.2.1
                                      have p12541_2 := h12541c.2.2.1
                                      have p12541_3 := h12541c.2.2.2
                                      linarith only [h4, hlam, p12541_1]
                                    · have p12541_0 := h12541c.1
                                      have p12541_1 := h12541c.2.1
                                      have p12541_2 := h12541c.2.2.1
                                      have p12541_3 := h12541c.2.2.2
                                      linarith only [h12301, h12503, h4, hc34, hc45, hlam, hphi, p12541_1]
                                    · have p12541_0 := h12541c.1
                                      have p12541_1 := h12541c.2.1
                                      have p12541_2 := h12541c.2.2.1
                                      have p12541_3 := h12541c.2.2.2
                                      linarith only [h10362, hlam, p12541_0]
                                    · have p12541_0 := h12541c.1
                                      have p12541_1 := h12541c.2.1
                                      have p12541_2 := h12541c.2.2.1
                                      have p12541_3 := h12541c.2.2.2
                                      linarith only [h1, hlam, p12541_0]
                                    · have p12541_0 := h12541c.1
                                      have p12541_1 := h12541c.2.1
                                      have p12541_2 := h12541c.2.2.1
                                      have p12541_3 := h12541c.2.2.2
                                      linarith only [hlam, p12541_0]
                                    · have p12541_0 := h12541c.1
                                      have p12541_1 := h12541c.2.1
                                      have p12541_2 := h12541c.2.2.1
                                      have p12541_3 := h12541c.2.2.2
                                      linarith only [h12289, hlam, p12541_1]
                                    · have p12541_0 := h12541c.1
                                      have p12541_1 := h12541c.2.1
                                      have p12541_2 := h12541c.2.2.1
                                      have p12541_3 := h12541c.2.2.2
                                      linarith only [h1, h12301, h12503, h4, hc34, hc45, hlam, hphi, p12541_1]
                                    · have p12541_0 := h12541c.1
                                      have p12541_1 := h12541c.2.1
                                      have p12541_2 := h12541c.2.2.1
                                      have p12541_3 := h12541c.2.2.2
                                      linarith only [h12296, hlam, p12541_0]
                                    · have p12541_0 := h12541c.1
                                      have p12541_1 := h12541c.2.1
                                      have p12541_2 := h12541c.2.2.1
                                      have p12541_3 := h12541c.2.2.2
                                      linarith only [h12301, h12503, hc03, hc45, hlam, hphi, ht34, p12541_1]
                                    · have p12541_0 := h12541c.1
                                      have p12541_1 := h12541c.2.1
                                      have p12541_2 := h12541c.2.2.1
                                      have p12541_3 := h12541c.2.2.2
                                      linarith only [h12301, h12503, hc13, hc45, hlam, hphi, ht34, p12541_1]
                                    · have p12541_0 := h12541c.1
                                      have p12541_1 := h12541c.2.1
                                      have p12541_2 := h12541c.2.2.1
                                      have p12541_3 := h12541c.2.2.2
                                      linarith only [hlam, p12541_0]
                                    · have p12541_0 := h12541c.1
                                      have p12541_1 := h12541c.2.1
                                      have p12541_2 := h12541c.2.2.1
                                      have p12541_3 := h12541c.2.2.2
                                      linarith only [h12301, h12503, hc34, hc45, hlam, hphi, p12541_1]
                                    · have p12541_0 := h12541c.1
                                      have p12541_1 := h12541c.2.1
                                      have p12541_2 := h12541c.2.2.1
                                      have p12541_3 := h12541c.2.2.2
                                      linarith only [h12301, hlam, p12541_0]
                                    · have p12541_0 := h12541c.1
                                      have p12541_1 := h12541c.2.1
                                      have p12541_2 := h12541c.2.2.1
                                      have p12541_3 := h12541c.2.2.2
                                      linarith only [h10361, hlam, p12541_0]
                                    · have p12541_0 := h12541c.1
                                      have p12541_1 := h12541c.2.1
                                      have p12541_2 := h12541c.2.2.1
                                      have p12541_3 := h12541c.2.2.2
                                      linarith only [h12295, hlam, p12541_0]
                                    · have p12541_0 := h12541c.1
                                      have p12541_1 := h12541c.2.1
                                      have p12541_2 := h12541c.2.2.1
                                      have p12541_3 := h12541c.2.2.2
                                      linarith only [h12300, hlam, p12541_0]
                                    · have p12541_0 := h12541c.1
                                      have p12541_1 := h12541c.2.1
                                      have p12541_2 := h12541c.2.2.1
                                      have p12541_3 := h12541c.2.2.2
                                      linarith only [hlam, p12541_0]
                                    · have p12541_0 := h12541c.1
                                      have p12541_1 := h12541c.2.1
                                      have p12541_2 := h12541c.2.2.1
                                      have p12541_3 := h12541c.2.2.2
                                      linarith only [h12503, hlam, p12541_1]
                                    · have p12541_0 := h12541c.1
                                      have p12541_1 := h12541c.2.1
                                      have p12541_2 := h12541c.2.2.1
                                      have p12541_3 := h12541c.2.2.2
                                      linarith only [h1, h12295, h12503, hc34, hc45, hlam, hphi, p12541_1]
                                    · have p12541_0 := h12541c.1
                                      have p12541_1 := h12541c.2.1
                                      have p12541_2 := h12541c.2.2.1
                                      have p12541_3 := h12541c.2.2.2
                                      linarith only [h12295, h12503, hc34, hc45, hlam, hphi, p12541_1]
                                    · have p12541_0 := h12541c.1
                                      have p12541_1 := h12541c.2.1
                                      have p12541_2 := h12541c.2.2.1
                                      have p12541_3 := h12541c.2.2.2
                                      linarith only [h0, h12503, h4, hc12, hc45, hlam, hphi, ht23, ht34, p12541_1]
                                    · have p12541_0 := h12541c.1
                                      have p12541_1 := h12541c.2.1
                                      have p12541_2 := h12541c.2.2.1
                                      have p12541_3 := h12541c.2.2.2
                                      rcases p12541_3 (m.d 0 3) (by simp) with h12565 | h12565
                                      · linarith only [h10362, h12565, hlam]
                                      · linarith only [h10361, h12565, hlam]
                                    · have p12541_0 := h12541c.1
                                      have p12541_1 := h12541c.2.1
                                      have p12541_2 := h12541c.2.2.1
                                      have p12541_3 := h12541c.2.2.2
                                      linarith only [hlam, p12541_0]
                          · linarith only [h12532, hlam, p12505_0]
                        · have p12505_0 := h12505c.1
                          have p12505_1 := h12505c.2.1
                          have p12505_2 := h12505c.2.2.1
                          have p12505_3 := h12505c.2.2.2
                          linarith only [h0, hlam, p12505_0]
                        · have p12505_0 := h12505c.1
                          have p12505_1 := h12505c.2.1
                          have p12505_2 := h12505c.2.2.1
                          have p12505_3 := h12505c.2.2.2
                          linarith only [hlam, p12505_0]
                        · have p12505_0 := h12505c.1
                          have p12505_1 := h12505c.2.1
                          have p12505_2 := h12505c.2.2.1
                          have p12505_3 := h12505c.2.2.2
                          linarith only [h12289, hlam, p12505_0]
                        · have p12505_0 := h12505c.1
                          have p12505_1 := h12505c.2.1
                          have p12505_2 := h12505c.2.2.1
                          have p12505_3 := h12505c.2.2.2
                          linarith only [h12291, hlam, p12505_0]
                        · have p12505_0 := h12505c.1
                          have p12505_1 := h12505c.2.1
                          have p12505_2 := h12505c.2.2.1
                          have p12505_3 := h12505c.2.2.2
                          linarith only [h12293, hlam, p12505_0]
                        · have p12505_0 := h12505c.1
                          have p12505_1 := h12505c.2.1
                          have p12505_2 := h12505c.2.2.1
                          have p12505_3 := h12505c.2.2.2
                          linarith only [h1, hlam, p12505_0]
                        · have p12505_0 := h12505c.1
                          have p12505_1 := h12505c.2.1
                          have p12505_2 := h12505c.2.2.1
                          have p12505_3 := h12505c.2.2.2
                          linarith only [h1, h10362, h12503, hc12, hc45, hlam, hphi, ht23, ht34, p12505_1]
                        · have p12505_0 := h12505c.1
                          have p12505_1 := h12505c.2.1
                          have p12505_2 := h12505c.2.2.1
                          have p12505_3 := h12505c.2.2.2
                          linarith only [hlam, p12505_0]
                        · have p12505_0 := h12505c.1
                          have p12505_1 := h12505c.2.1
                          have p12505_2 := h12505c.2.2.1
                          have p12505_3 := h12505c.2.2.2
                          linarith only [h1, h10362, h12291, h12503, hc12, hc45, hlam, hphi, ht23, ht34, p12505_1]
                        · have p12505_0 := h12505c.1
                          have p12505_1 := h12505c.2.1
                          have p12505_2 := h12505c.2.2.1
                          have p12505_3 := h12505c.2.2.2
                          linarith only [h12296, hlam, p12505_1]
                        · have p12505_0 := h12505c.1
                          have p12505_1 := h12505c.2.1
                          have p12505_2 := h12505c.2.2.1
                          have p12505_3 := h12505c.2.2.2
                          linarith only [h2, hlam, p12505_0]
                        · have p12505_0 := h12505c.1
                          have p12505_1 := h12505c.2.1
                          have p12505_2 := h12505c.2.2.1
                          have p12505_3 := h12505c.2.2.2
                          linarith only [h10361, h10362, h12503, h2, hc12, hc45, hlam, hphi, ht23, ht34, p12505_1]
                        · have p12505_0 := h12505c.1
                          have p12505_1 := h12505c.2.1
                          have p12505_2 := h12505c.2.2.1
                          have p12505_3 := h12505c.2.2.2
                          linarith only [h12295, hlam, p12505_0]
                        · have p12505_0 := h12505c.1
                          have p12505_1 := h12505c.2.1
                          have p12505_2 := h12505c.2.2.1
                          have p12505_3 := h12505c.2.2.2
                          linarith only [hlam, p12505_0]
                        · have p12505_0 := h12505c.1
                          have p12505_1 := h12505c.2.1
                          have p12505_2 := h12505c.2.2.1
                          have p12505_3 := h12505c.2.2.2
                          linarith only [h12298, hlam, p12505_1]
                        · have p12505_0 := h12505c.1
                          have p12505_1 := h12505c.2.1
                          have p12505_2 := h12505c.2.2.1
                          have p12505_3 := h12505c.2.2.2
                          linarith only [h3, hlam, p12505_0]
                        · have p12505_0 := h12505c.1
                          have p12505_1 := h12505c.2.1
                          have p12505_2 := h12505c.2.2.1
                          have p12505_3 := h12505c.2.2.2
                          rcases p12505_3 (m.d 0 1) (by simp) with h12586 | h12586
                          · rcases p12505_3 (m.d 1 2) (by simp) with h12587 | h12587
                            · linarith only [h12293, h12587, hlam]
                            · rcases p12505_3 (m.d 1 3) (by simp) with h12589 | h12589
                              · linarith only [h12296, h12589, hlam]
                              · linarith only [h12289, h12589, hlam]
                          · linarith only [h0, h12586, hlam]
                        · have p12505_0 := h12505c.1
                          have p12505_1 := h12505c.2.1
                          have p12505_2 := h12505c.2.2.1
                          have p12505_3 := h12505c.2.2.2
                          linarith only [h12295, h12301, h12503, h3, h9870, hc34, hc45, hlam, hphi, p12505_1]
                        · have p12505_0 := h12505c.1
                          have p12505_1 := h12505c.2.1
                          have p12505_2 := h12505c.2.2.1
                          have p12505_3 := h12505c.2.2.2
                          rcases p12505_3 (m.d 0 1) (by simp) with h12594 | h12594
                          · rcases p12505_3 (m.d 1 2) (by simp) with h12595 | h12595
                            · linarith only [h12293, h12595, hlam]
                            · rcases p12505_3 (m.d 1 3) (by simp) with h12597 | h12597
                              · linarith only [h12296, h12597, hlam]
                              · linarith only [h12295, h12597, hlam]
                          · linarith only [h12594, h2, hlam]
                        · have p12505_0 := h12505c.1
                          have p12505_1 := h12505c.2.1
                          have p12505_2 := h12505c.2.2.1
                          have p12505_3 := h12505c.2.2.2
                          linarith only [hlam, p12505_0]
                · linarith only [h1, h12295, h12300, h4, hlam]
          · linarith only [h10361, h10362, h12295, hc13, hc35, hlam, hphi]

set_option maxHeartbeats 6296000 in
set_option maxHeartbeats 6296000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s12_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg8674 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9870 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h10361 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h8674 := hg8674
  have h9870 := hg9870
  rcases m.htr 0 3 5 (by decide) (by decide) with h10362 | h10362
  · exact r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg8674 hg9870 h10361 h10362
  · exact r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg8674 hg9870 h10361 h10362

end R2N4
