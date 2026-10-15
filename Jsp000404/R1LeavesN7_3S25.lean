import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_3S24

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 29596000 in
set_option maxHeartbeats 29596000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_13_25_L_I_L_I_H_I_s1 m hb1 hb3 hb5 h0 h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h13951 | h13951
    · rcases m.htr 0 1 5 (by decide) (by decide) with h13952 | h13952
      · rcases m.htr 0 2 3 (by decide) (by decide) with h13953 | h13953
        · linarith only [h0, h1, h13953, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h13955 | h13955
          · rcases m.htr 0 2 5 (by decide) (by decide) with h13956 | h13956
            · rcases m.htr 0 3 4 (by decide) (by decide) with h13957 | h13957
              · rcases m.htr 0 3 5 (by decide) (by decide) with h13958 | h13958
                · rcases m.htr 0 4 5 (by decide) (by decide) with h13959 | h13959
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h13960 | h13960
                    · linarith only [h0, h1, h13953, h13960, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h13962 | h13962
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h13963 | h13963
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h13964 | h13964
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h13965 | h13965
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h13966 | h13966
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h13967 | h13967
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h13968 | h13968
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13969 | h13969
                                    · linarith only [h0, h1, h13960, h13962, h13969, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                    · linarith only [h0, h1, h13960, h13962, h13966, h13969, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h0, h1, h13960, h13968, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h0, h1, h13960, h13967, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h13974 | h13974
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h13975 | h13975
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13976 | h13976
                                    · linarith only [h0, h1, h13960, h13962, h13966, h13976, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13978 | h13978
                                      · linarith only [h13962, h13966, h13974, h13978, hlam]
                                      · rcases h1bigk with h13980c | h13980c | h13980c | h13980c | h13980c | h13980c | h13980c | h13980c | h13980c | h13980c | h13980c | h13980c | h13980c | h13980c | h13980c | h13980c | h13980c | h13980c | h13980c | h13980c | h13980c | h13980c | h13980c | h13980c | h13980c
                                        · have p13980_0 := h13980c.1
                                          have p13980_1 := h13980c.2.1
                                          have p13980_2 := h13980c.2.2.1
                                          have p13980_3 := h13980c.2.2.2
                                          linarith only [hlam, p13980_0]
                                        · have p13980_0 := h13980c.1
                                          have p13980_1 := h13980c.2.1
                                          have p13980_2 := h13980c.2.2.1
                                          have p13980_3 := h13980c.2.2.2
                                          linarith only [h1, h13960, hc12, hc23, hlam, hphi, p13980_1]
                                        · have p13980_0 := h13980c.1
                                          have p13980_1 := h13980c.2.1
                                          have p13980_2 := h13980c.2.2.1
                                          have p13980_3 := h13980c.2.2.2
                                          linarith only [h1, hlam, p13980_0]
                                        · have p13980_0 := h13980c.1
                                          have p13980_1 := h13980c.2.1
                                          have p13980_2 := h13980c.2.2.1
                                          have p13980_3 := h13980c.2.2.2
                                          rcases p13980_3 (m.d 0 1) (by simp) with h13984 | h13984
                                          · rcases p13980_3 (m.d 1 2) (by simp) with h13985 | h13985
                                            · linarith only [h0, h13985, hlam]
                                            · linarith only [h13962, h13985, hlam]
                                          · linarith only [h13984, hlam, p13980_0]
                                        · have p13980_0 := h13980c.1
                                          have p13980_1 := h13980c.2.1
                                          have p13980_2 := h13980c.2.2.1
                                          have p13980_3 := h13980c.2.2.2
                                          rcases p13980_3 (m.d 0 1) (by simp) with h13989 | h13989
                                          · rcases p13980_3 (m.d 1 2) (by simp) with h13990 | h13990
                                            · linarith only [h0, h13990, hlam]
                                            · linarith only [h13963, h13990, hlam]
                                          · linarith only [h13989, hlam, p13980_0]
                                        · have p13980_0 := h13980c.1
                                          have p13980_1 := h13980c.2.1
                                          have p13980_2 := h13980c.2.2.1
                                          have p13980_3 := h13980c.2.2.2
                                          linarith only [h0, hlam, p13980_0]
                                        · have p13980_0 := h13980c.1
                                          have p13980_1 := h13980c.2.1
                                          have p13980_2 := h13980c.2.2.1
                                          have p13980_3 := h13980c.2.2.2
                                          linarith only [hlam, p13980_0]
                                        · have p13980_0 := h13980c.1
                                          have p13980_1 := h13980c.2.1
                                          have p13980_2 := h13980c.2.2.1
                                          have p13980_3 := h13980c.2.2.2
                                          linarith only [h13960, hlam, p13980_0]
                                        · have p13980_0 := h13980c.1
                                          have p13980_1 := h13980c.2.1
                                          have p13980_2 := h13980c.2.2.1
                                          have p13980_3 := h13980c.2.2.2
                                          linarith only [h0, h1, h13960, h13962, h13974, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13980_1]
                                        · have p13980_0 := h13980c.1
                                          have p13980_1 := h13980c.2.1
                                          have p13980_2 := h13980c.2.2.1
                                          have p13980_3 := h13980c.2.2.2
                                          linarith only [h0, h1, h13960, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p13980_1]
                                        · have p13980_0 := h13980c.1
                                          have p13980_1 := h13980c.2.1
                                          have p13980_2 := h13980c.2.2.1
                                          have p13980_3 := h13980c.2.2.2
                                          linarith only [h0, h13960, hc12, hc23, hlam, hphi, p13980_1]
                                        · have p13980_0 := h13980c.1
                                          have p13980_1 := h13980c.2.1
                                          have p13980_2 := h13980c.2.2.1
                                          have p13980_3 := h13980c.2.2.2
                                          rcases p13980_3 (m.d 0 1) (by simp) with h14000 | h14000
                                          · linarith only [h1, h14000, hlam]
                                          · linarith only [h0, h14000, hlam]
                                        · have p13980_0 := h13980c.1
                                          have p13980_1 := h13980c.2.1
                                          have p13980_2 := h13980c.2.2.1
                                          have p13980_3 := h13980c.2.2.2
                                          linarith only [hlam, p13980_0]
                                        · have p13980_0 := h13980c.1
                                          have p13980_1 := h13980c.2.1
                                          have p13980_2 := h13980c.2.2.1
                                          have p13980_3 := h13980c.2.2.2
                                          linarith only [h0, h1, h13955, h13959, h13966, hlam, p13980_2]
                                        · have p13980_0 := h13980c.1
                                          have p13980_1 := h13980c.2.1
                                          have p13980_2 := h13980c.2.2.1
                                          have p13980_3 := h13980c.2.2.2
                                          rcases p13980_3 (m.d 0 1) (by simp) with h14005 | h14005
                                          · linarith only [h1, h14005, hlam]
                                          · linarith only [h13952, h14005, hlam]
                                        · have p13980_0 := h13980c.1
                                          have p13980_1 := h13980c.2.1
                                          have p13980_2 := h13980c.2.2.1
                                          have p13980_3 := h13980c.2.2.2
                                          linarith only [h13951, hlam, p13980_0]
                                        · have p13980_0 := h13980c.1
                                          have p13980_1 := h13980c.2.1
                                          have p13980_2 := h13980c.2.2.1
                                          have p13980_3 := h13980c.2.2.2
                                          linarith only [h13962, hlam, p13980_1]
                                        · have p13980_0 := h13980c.1
                                          have p13980_1 := h13980c.2.1
                                          have p13980_2 := h13980c.2.2.1
                                          have p13980_3 := h13980c.2.2.2
                                          linarith only [h13964, hlam, p13980_0]
                                        · have p13980_0 := h13980c.1
                                          have p13980_1 := h13980c.2.1
                                          have p13980_2 := h13980c.2.2.1
                                          have p13980_3 := h13980c.2.2.2
                                          linarith only [hlam, p13980_0]
                                        · have p13980_0 := h13980c.1
                                          have p13980_1 := h13980c.2.1
                                          have p13980_2 := h13980c.2.2.1
                                          have p13980_3 := h13980c.2.2.2
                                          linarith only [h13966, hlam, p13980_1]
                                        · have p13980_0 := h13980c.1
                                          have p13980_1 := h13980c.2.1
                                          have p13980_2 := h13980c.2.2.1
                                          have p13980_3 := h13980c.2.2.2
                                          linarith only [h13952, hlam, p13980_0]
                                        · have p13980_0 := h13980c.1
                                          have p13980_1 := h13980c.2.1
                                          have p13980_2 := h13980c.2.2.1
                                          have p13980_3 := h13980c.2.2.2
                                          linarith only [h13963, hlam, p13980_1]
                                        · have p13980_0 := h13980c.1
                                          have p13980_1 := h13980c.2.1
                                          have p13980_2 := h13980c.2.2.1
                                          have p13980_3 := h13980c.2.2.2
                                          linarith only [h13965, hlam, p13980_0]
                                        · have p13980_0 := h13980c.1
                                          have p13980_1 := h13980c.2.1
                                          have p13980_2 := h13980c.2.2.1
                                          have p13980_3 := h13980c.2.2.2
                                          linarith only [h1, h13952, h13962, h13974, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13980_1]
                                        · have p13980_0 := h13980c.1
                                          have p13980_1 := h13980c.2.1
                                          have p13980_2 := h13980c.2.2.1
                                          have p13980_3 := h13980c.2.2.2
                                          linarith only [hlam, p13980_0]
                                  · linarith only [h0, h1, h13960, h13975, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h0, h1, h13955, h13959, h13960, h13966, h13974, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h0, h1, h13962, h13965, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h13962, h13964, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h13956, h13962, h13963, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h1, h13955, h13960, h13962, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h14024 | h14024
                    · linarith only [h0, h1, h13953, h14024, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h14026 | h14026
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h14027 | h14027
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h14028 | h14028
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h14029 | h14029
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h14030 | h14030
                              · linarith only [h13951, h13959, h14030, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h14032 | h14032
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h14033 | h14033
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h14034 | h14034
                                    · linarith only [h13951, h13959, h14026, h14034, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h14036 | h14036
                                      · linarith only [h13951, h13959, h14026, h14032, h14036, hlam]
                                      · rcases h1bigk with h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c | h14038c
                                        · have p14038_0 := h14038c.1
                                          have p14038_1 := h14038c.2.1
                                          have p14038_2 := h14038c.2.2.1
                                          have p14038_3 := h14038c.2.2.2
                                          linarith only [hlam, p14038_0]
                                        · have p14038_0 := h14038c.1
                                          have p14038_1 := h14038c.2.1
                                          have p14038_2 := h14038c.2.2.1
                                          have p14038_3 := h14038c.2.2.2
                                          linarith only [h1, h14024, h14027, h14032, h14034, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14038_1]
                                        · have p14038_0 := h14038c.1
                                          have p14038_1 := h14038c.2.1
                                          have p14038_2 := h14038c.2.2.1
                                          have p14038_3 := h14038c.2.2.2
                                          linarith only [h1, hlam, p14038_0]
                                        · have p14038_0 := h14038c.1
                                          have p14038_1 := h14038c.2.1
                                          have p14038_2 := h14038c.2.2.1
                                          have p14038_3 := h14038c.2.2.2
                                          rcases p14038_3 (m.d 0 1) (by simp) with h14042 | h14042
                                          · rcases p14038_3 (m.d 1 2) (by simp) with h14043 | h14043
                                            · linarith only [h0, h14043, hlam]
                                            · linarith only [h14026, h14043, hlam]
                                          · linarith only [h14042, hlam, p14038_0]
                                        · have p14038_0 := h14038c.1
                                          have p14038_1 := h14038c.2.1
                                          have p14038_2 := h14038c.2.2.1
                                          have p14038_3 := h14038c.2.2.2
                                          rcases p14038_3 (m.d 0 1) (by simp) with h14047 | h14047
                                          · rcases p14038_3 (m.d 1 2) (by simp) with h14048 | h14048
                                            · linarith only [h0, h14048, hlam]
                                            · linarith only [h14027, h14048, hlam]
                                          · linarith only [h14047, hlam, p14038_0]
                                        · have p14038_0 := h14038c.1
                                          have p14038_1 := h14038c.2.1
                                          have p14038_2 := h14038c.2.2.1
                                          have p14038_3 := h14038c.2.2.2
                                          linarith only [h0, hlam, p14038_0]
                                        · have p14038_0 := h14038c.1
                                          have p14038_1 := h14038c.2.1
                                          have p14038_2 := h14038c.2.2.1
                                          have p14038_3 := h14038c.2.2.2
                                          linarith only [hlam, p14038_0]
                                        · have p14038_0 := h14038c.1
                                          have p14038_1 := h14038c.2.1
                                          have p14038_2 := h14038c.2.2.1
                                          have p14038_3 := h14038c.2.2.2
                                          linarith only [h14024, hlam, p14038_0]
                                        · have p14038_0 := h14038c.1
                                          have p14038_1 := h14038c.2.1
                                          have p14038_2 := h14038c.2.2.1
                                          have p14038_3 := h14038c.2.2.2
                                          linarith only [h0, h1, h14024, h14026, h14032, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14038_1]
                                        · have p14038_0 := h14038c.1
                                          have p14038_1 := h14038c.2.1
                                          have p14038_2 := h14038c.2.2.1
                                          have p14038_3 := h14038c.2.2.2
                                          linarith only [h0, h1, h14024, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p14038_1]
                                        · have p14038_0 := h14038c.1
                                          have p14038_1 := h14038c.2.1
                                          have p14038_2 := h14038c.2.2.1
                                          have p14038_3 := h14038c.2.2.2
                                          linarith only [h0, h14024, hc12, hc23, hlam, hphi, p14038_1]
                                        · have p14038_0 := h14038c.1
                                          have p14038_1 := h14038c.2.1
                                          have p14038_2 := h14038c.2.2.1
                                          have p14038_3 := h14038c.2.2.2
                                          rcases p14038_3 (m.d 0 1) (by simp) with h14058 | h14058
                                          · linarith only [h1, h14058, hlam]
                                          · linarith only [h0, h14058, hlam]
                                        · have p14038_0 := h14038c.1
                                          have p14038_1 := h14038c.2.1
                                          have p14038_2 := h14038c.2.2.1
                                          have p14038_3 := h14038c.2.2.2
                                          linarith only [hlam, p14038_0]
                                        · have p14038_0 := h14038c.1
                                          have p14038_1 := h14038c.2.1
                                          have p14038_2 := h14038c.2.2.1
                                          have p14038_3 := h14038c.2.2.2
                                          rcases p14038_3 (m.d 0 1) (by simp) with h14062 | h14062
                                          · linarith only [h1, h14062, hlam]
                                          · linarith only [h13951, h14062, hlam]
                                        · have p14038_0 := h14038c.1
                                          have p14038_1 := h14038c.2.1
                                          have p14038_2 := h14038c.2.2.1
                                          have p14038_3 := h14038c.2.2.2
                                          rcases p14038_3 (m.d 0 1) (by simp) with h14065 | h14065
                                          · linarith only [h1, h14065, hlam]
                                          · linarith only [h13952, h14065, hlam]
                                        · have p14038_0 := h14038c.1
                                          have p14038_1 := h14038c.2.1
                                          have p14038_2 := h14038c.2.2.1
                                          have p14038_3 := h14038c.2.2.2
                                          linarith only [h13951, hlam, p14038_0]
                                        · have p14038_0 := h14038c.1
                                          have p14038_1 := h14038c.2.1
                                          have p14038_2 := h14038c.2.2.1
                                          have p14038_3 := h14038c.2.2.2
                                          linarith only [h14026, hlam, p14038_1]
                                        · have p14038_0 := h14038c.1
                                          have p14038_1 := h14038c.2.1
                                          have p14038_2 := h14038c.2.2.1
                                          have p14038_3 := h14038c.2.2.2
                                          linarith only [h14028, hlam, p14038_0]
                                        · have p14038_0 := h14038c.1
                                          have p14038_1 := h14038c.2.1
                                          have p14038_2 := h14038c.2.2.1
                                          have p14038_3 := h14038c.2.2.2
                                          linarith only [hlam, p14038_0]
                                        · have p14038_0 := h14038c.1
                                          have p14038_1 := h14038c.2.1
                                          have p14038_2 := h14038c.2.2.1
                                          have p14038_3 := h14038c.2.2.2
                                          linarith only [h14030, hlam, p14038_1]
                                        · have p14038_0 := h14038c.1
                                          have p14038_1 := h14038c.2.1
                                          have p14038_2 := h14038c.2.2.1
                                          have p14038_3 := h14038c.2.2.2
                                          linarith only [h13952, hlam, p14038_0]
                                        · have p14038_0 := h14038c.1
                                          have p14038_1 := h14038c.2.1
                                          have p14038_2 := h14038c.2.2.1
                                          have p14038_3 := h14038c.2.2.2
                                          linarith only [h14027, hlam, p14038_1]
                                        · have p14038_0 := h14038c.1
                                          have p14038_1 := h14038c.2.1
                                          have p14038_2 := h14038c.2.2.1
                                          have p14038_3 := h14038c.2.2.2
                                          linarith only [h14029, hlam, p14038_0]
                                        · have p14038_0 := h14038c.1
                                          have p14038_1 := h14038c.2.1
                                          have p14038_2 := h14038c.2.2.1
                                          have p14038_3 := h14038c.2.2.2
                                          linarith only [h1, h13952, hc13, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p14038_1]
                                        · have p14038_0 := h14038c.1
                                          have p14038_1 := h14038c.2.1
                                          have p14038_2 := h14038c.2.2.1
                                          have p14038_3 := h14038c.2.2.2
                                          linarith only [hlam, p14038_0]
                                  · linarith only [h0, h1, h14024, h14033, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h0, h1, h14024, h14026, h14032, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h0, h1, h14026, h14029, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h14026, h14028, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h13956, h14026, h14027, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h1, h13955, h14024, h14026, hc12, hc23, hlam, hphi]
                · linarith only [h1, h13952, h13958, hlam]
              · linarith only [h1, h13951, h13957, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h14086 | h14086
              · rcases m.htr 0 3 5 (by decide) (by decide) with h14087 | h14087
                · rcases m.htr 0 4 5 (by decide) (by decide) with h14088 | h14088
                  · linarith only [h13955, h13956, h14088, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h14090 | h14090
                    · linarith only [h0, h1, h13953, h14090, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h14092 | h14092
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h14093 | h14093
                        · linarith only [h0, h13956, h14093, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h14095 | h14095
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h14096 | h14096
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h14097 | h14097
                              · linarith only [h13951, h14088, h14097, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h14099 | h14099
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h14100 | h14100
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h14101 | h14101
                                    · linarith only [h0, h13951, h13956, h14088, h14092, h14101, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h14103 | h14103
                                      · linarith only [h0, h1, h13951, h13956, h14090, h14092, h14099, h14101, h14103, hc12, hc23, hlam, hphi]
                                      · rcases h1bigk with h14105c | h14105c | h14105c | h14105c | h14105c | h14105c | h14105c | h14105c | h14105c | h14105c | h14105c | h14105c | h14105c | h14105c | h14105c | h14105c | h14105c | h14105c | h14105c | h14105c | h14105c | h14105c | h14105c | h14105c | h14105c
                                        · have p14105_0 := h14105c.1
                                          have p14105_1 := h14105c.2.1
                                          have p14105_2 := h14105c.2.2.1
                                          have p14105_3 := h14105c.2.2.2
                                          linarith only [hlam, p14105_0]
                                        · have p14105_0 := h14105c.1
                                          have p14105_1 := h14105c.2.1
                                          have p14105_2 := h14105c.2.2.1
                                          have p14105_3 := h14105c.2.2.2
                                          linarith only [h1, h14090, h14092, h14099, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14105_1]
                                        · have p14105_0 := h14105c.1
                                          have p14105_1 := h14105c.2.1
                                          have p14105_2 := h14105c.2.2.1
                                          have p14105_3 := h14105c.2.2.2
                                          linarith only [h1, hlam, p14105_0]
                                        · have p14105_0 := h14105c.1
                                          have p14105_1 := h14105c.2.1
                                          have p14105_2 := h14105c.2.2.1
                                          have p14105_3 := h14105c.2.2.2
                                          rcases p14105_3 (m.d 0 1) (by simp) with h14109 | h14109
                                          · rcases p14105_3 (m.d 1 2) (by simp) with h14110 | h14110
                                            · linarith only [h0, h14110, hlam]
                                            · linarith only [h14092, h14110, hlam]
                                          · linarith only [h14109, hlam, p14105_0]
                                        · have p14105_0 := h14105c.1
                                          have p14105_1 := h14105c.2.1
                                          have p14105_2 := h14105c.2.2.1
                                          have p14105_3 := h14105c.2.2.2
                                          linarith only [h1, h14090, h14092, h14093, h14099, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14105_1]
                                        · have p14105_0 := h14105c.1
                                          have p14105_1 := h14105c.2.1
                                          have p14105_2 := h14105c.2.2.1
                                          have p14105_3 := h14105c.2.2.2
                                          linarith only [h0, hlam, p14105_0]
                                        · have p14105_0 := h14105c.1
                                          have p14105_1 := h14105c.2.1
                                          have p14105_2 := h14105c.2.2.1
                                          have p14105_3 := h14105c.2.2.2
                                          linarith only [hlam, p14105_0]
                                        · have p14105_0 := h14105c.1
                                          have p14105_1 := h14105c.2.1
                                          have p14105_2 := h14105c.2.2.1
                                          have p14105_3 := h14105c.2.2.2
                                          linarith only [h14090, hlam, p14105_0]
                                        · have p14105_0 := h14105c.1
                                          have p14105_1 := h14105c.2.1
                                          have p14105_2 := h14105c.2.2.1
                                          have p14105_3 := h14105c.2.2.2
                                          linarith only [h0, h13956, h14101, hc14, hc45, hlam, hphi, p14105_1]
                                        · have p14105_0 := h14105c.1
                                          have p14105_1 := h14105c.2.1
                                          have p14105_2 := h14105c.2.2.1
                                          have p14105_3 := h14105c.2.2.2
                                          linarith only [h14093, hlam, p14105_0]
                                        · have p14105_0 := h14105c.1
                                          have p14105_1 := h14105c.2.1
                                          have p14105_2 := h14105c.2.2.1
                                          have p14105_3 := h14105c.2.2.2
                                          linarith only [h0, h14090, hc12, hc23, hlam, hphi, p14105_1]
                                        · have p14105_0 := h14105c.1
                                          have p14105_1 := h14105c.2.1
                                          have p14105_2 := h14105c.2.2.1
                                          have p14105_3 := h14105c.2.2.2
                                          rcases p14105_3 (m.d 0 1) (by simp) with h14121 | h14121
                                          · linarith only [h1, h14121, hlam]
                                          · linarith only [h0, h14121, hlam]
                                        · have p14105_0 := h14105c.1
                                          have p14105_1 := h14105c.2.1
                                          have p14105_2 := h14105c.2.2.1
                                          have p14105_3 := h14105c.2.2.2
                                          linarith only [hlam, p14105_0]
                                        · have p14105_0 := h14105c.1
                                          have p14105_1 := h14105c.2.1
                                          have p14105_2 := h14105c.2.2.1
                                          have p14105_3 := h14105c.2.2.2
                                          rcases p14105_3 (m.d 0 1) (by simp) with h14125 | h14125
                                          · linarith only [h1, h14125, hlam]
                                          · linarith only [h13951, h14125, hlam]
                                        · have p14105_0 := h14105c.1
                                          have p14105_1 := h14105c.2.1
                                          have p14105_2 := h14105c.2.2.1
                                          have p14105_3 := h14105c.2.2.2
                                          rcases p14105_3 (m.d 0 1) (by simp) with h14128 | h14128
                                          · linarith only [h1, h14128, hlam]
                                          · linarith only [h13952, h14128, hlam]
                                        · have p14105_0 := h14105c.1
                                          have p14105_1 := h14105c.2.1
                                          have p14105_2 := h14105c.2.2.1
                                          have p14105_3 := h14105c.2.2.2
                                          linarith only [h13951, hlam, p14105_0]
                                        · have p14105_0 := h14105c.1
                                          have p14105_1 := h14105c.2.1
                                          have p14105_2 := h14105c.2.2.1
                                          have p14105_3 := h14105c.2.2.2
                                          linarith only [h14092, hlam, p14105_1]
                                        · have p14105_0 := h14105c.1
                                          have p14105_1 := h14105c.2.1
                                          have p14105_2 := h14105c.2.2.1
                                          have p14105_3 := h14105c.2.2.2
                                          linarith only [h14095, hlam, p14105_0]
                                        · have p14105_0 := h14105c.1
                                          have p14105_1 := h14105c.2.1
                                          have p14105_2 := h14105c.2.2.1
                                          have p14105_3 := h14105c.2.2.2
                                          linarith only [hlam, p14105_0]
                                        · have p14105_0 := h14105c.1
                                          have p14105_1 := h14105c.2.1
                                          have p14105_2 := h14105c.2.2.1
                                          have p14105_3 := h14105c.2.2.2
                                          linarith only [h14097, hlam, p14105_1]
                                        · have p14105_0 := h14105c.1
                                          have p14105_1 := h14105c.2.1
                                          have p14105_2 := h14105c.2.2.1
                                          have p14105_3 := h14105c.2.2.2
                                          linarith only [h13952, hlam, p14105_0]
                                        · have p14105_0 := h14105c.1
                                          have p14105_1 := h14105c.2.1
                                          have p14105_2 := h14105c.2.2.1
                                          have p14105_3 := h14105c.2.2.2
                                          linarith only [h13952, h14092, h14099, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p14105_1]
                                        · have p14105_0 := h14105c.1
                                          have p14105_1 := h14105c.2.1
                                          have p14105_2 := h14105c.2.2.1
                                          have p14105_3 := h14105c.2.2.2
                                          linarith only [h14096, hlam, p14105_0]
                                        · have p14105_0 := h14105c.1
                                          have p14105_1 := h14105c.2.1
                                          have p14105_2 := h14105c.2.2.1
                                          have p14105_3 := h14105c.2.2.2
                                          linarith only [h1, h13952, h14090, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14105_1]
                                        · have p14105_0 := h14105c.1
                                          have p14105_1 := h14105c.2.1
                                          have p14105_2 := h14105c.2.2.1
                                          have p14105_3 := h14105c.2.2.2
                                          linarith only [hlam, p14105_0]
                                  · linarith only [h0, h1, h14090, h14092, h14099, h14100, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                                · linarith only [h1, h13952, h14090, h14092, h14093, h14099, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h1, h13952, h14092, h14093, h14096, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h1, h13952, h14092, h14093, h14095, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h13955, h13956, h14092, hc12, hc25, hlam, hphi]
                · linarith only [h1, h13952, h14087, hlam]
              · linarith only [h1, h13952, h13955, h13956, h14086, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h14148 | h14148
            · rcases m.htr 0 3 4 (by decide) (by decide) with h14149 | h14149
              · rcases m.htr 0 3 5 (by decide) (by decide) with h14150 | h14150
                · rcases m.htr 0 4 5 (by decide) (by decide) with h14151 | h14151
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h14152 | h14152
                    · linarith only [h0, h1, h13953, h14148, h14152, hc03, hc25, hlam, hphi, ht0b, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h14154 | h14154
                      · linarith only [h0, h13955, h14154, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h14156 | h14156
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h14157 | h14157
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h14158 | h14158
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h14159 | h14159
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h14160 | h14160
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h14161 | h14161
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h14162 | h14162
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h14163 | h14163
                                      · rcases h1bigk with h14164c | h14164c | h14164c | h14164c | h14164c | h14164c | h14164c | h14164c | h14164c | h14164c | h14164c | h14164c | h14164c | h14164c | h14164c | h14164c | h14164c | h14164c | h14164c | h14164c | h14164c | h14164c | h14164c | h14164c | h14164c
                                        · have p14164_0 := h14164c.1
                                          have p14164_1 := h14164c.2.1
                                          have p14164_2 := h14164c.2.2.1
                                          have p14164_3 := h14164c.2.2.2
                                          linarith only [hlam, p14164_0]
                                        · have p14164_0 := h14164c.1
                                          have p14164_1 := h14164c.2.1
                                          have p14164_2 := h14164c.2.2.1
                                          have p14164_3 := h14164c.2.2.2
                                          linarith only [h1, h14152, h14156, h14161, h14163, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14164_1]
                                        · have p14164_0 := h14164c.1
                                          have p14164_1 := h14164c.2.1
                                          have p14164_2 := h14164c.2.2.1
                                          have p14164_3 := h14164c.2.2.2
                                          linarith only [h1, hlam, p14164_0]
                                        · have p14164_0 := h14164c.1
                                          have p14164_1 := h14164c.2.1
                                          have p14164_2 := h14164c.2.2.1
                                          have p14164_3 := h14164c.2.2.2
                                          linarith only [h1, h14152, h14154, h14156, h14161, h14163, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14164_1]
                                        · have p14164_0 := h14164c.1
                                          have p14164_1 := h14164c.2.1
                                          have p14164_2 := h14164c.2.2.1
                                          have p14164_3 := h14164c.2.2.2
                                          rcases p14164_3 (m.d 0 1) (by simp) with h14169 | h14169
                                          · rcases p14164_3 (m.d 1 2) (by simp) with h14170 | h14170
                                            · linarith only [h0, h14170, hlam]
                                            · linarith only [h14156, h14170, hlam]
                                          · linarith only [h14169, hlam, p14164_0]
                                        · have p14164_0 := h14164c.1
                                          have p14164_1 := h14164c.2.1
                                          have p14164_2 := h14164c.2.2.1
                                          have p14164_3 := h14164c.2.2.2
                                          linarith only [h0, hlam, p14164_0]
                                        · have p14164_0 := h14164c.1
                                          have p14164_1 := h14164c.2.1
                                          have p14164_2 := h14164c.2.2.1
                                          have p14164_3 := h14164c.2.2.2
                                          linarith only [hlam, p14164_0]
                                        · have p14164_0 := h14164c.1
                                          have p14164_1 := h14164c.2.1
                                          have p14164_2 := h14164c.2.2.1
                                          have p14164_3 := h14164c.2.2.2
                                          linarith only [h14152, hlam, p14164_0]
                                        · have p14164_0 := h14164c.1
                                          have p14164_1 := h14164c.2.1
                                          have p14164_2 := h14164c.2.2.1
                                          have p14164_3 := h14164c.2.2.2
                                          linarith only [h14154, hlam, p14164_0]
                                        · have p14164_0 := h14164c.1
                                          have p14164_1 := h14164c.2.1
                                          have p14164_2 := h14164c.2.2.1
                                          have p14164_3 := h14164c.2.2.2
                                          linarith only [h0, h1, h14152, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p14164_1]
                                        · have p14164_0 := h14164c.1
                                          have p14164_1 := h14164c.2.1
                                          have p14164_2 := h14164c.2.2.1
                                          have p14164_3 := h14164c.2.2.2
                                          linarith only [h0, h14152, hc12, hc23, hlam, hphi, p14164_1]
                                        · have p14164_0 := h14164c.1
                                          have p14164_1 := h14164c.2.1
                                          have p14164_2 := h14164c.2.2.1
                                          have p14164_3 := h14164c.2.2.2
                                          rcases p14164_3 (m.d 0 1) (by simp) with h14180 | h14180
                                          · linarith only [h1, h14180, hlam]
                                          · linarith only [h0, h14180, hlam]
                                        · have p14164_0 := h14164c.1
                                          have p14164_1 := h14164c.2.1
                                          have p14164_2 := h14164c.2.2.1
                                          have p14164_3 := h14164c.2.2.2
                                          linarith only [hlam, p14164_0]
                                        · have p14164_0 := h14164c.1
                                          have p14164_1 := h14164c.2.1
                                          have p14164_2 := h14164c.2.2.1
                                          have p14164_3 := h14164c.2.2.2
                                          rcases p14164_3 (m.d 0 1) (by simp) with h14184 | h14184
                                          · linarith only [h1, h14184, hlam]
                                          · linarith only [h13951, h14184, hlam]
                                        · have p14164_0 := h14164c.1
                                          have p14164_1 := h14164c.2.1
                                          have p14164_2 := h14164c.2.2.1
                                          have p14164_3 := h14164c.2.2.2
                                          rcases p14164_3 (m.d 0 1) (by simp) with h14187 | h14187
                                          · linarith only [h1, h14187, hlam]
                                          · linarith only [h13952, h14187, hlam]
                                        · have p14164_0 := h14164c.1
                                          have p14164_1 := h14164c.2.1
                                          have p14164_2 := h14164c.2.2.1
                                          have p14164_3 := h14164c.2.2.2
                                          linarith only [h13951, hlam, p14164_0]
                                        · have p14164_0 := h14164c.1
                                          have p14164_1 := h14164c.2.1
                                          have p14164_2 := h14164c.2.2.1
                                          have p14164_3 := h14164c.2.2.2
                                          linarith only [h13951, h14156, h14161, h14163, hc01, hc45, hlam, hphi, ht0b, ht5b, p14164_1]
                                        · have p14164_0 := h14164c.1
                                          have p14164_1 := h14164c.2.1
                                          have p14164_2 := h14164c.2.2.1
                                          have p14164_3 := h14164c.2.2.2
                                          linarith only [h14157, hlam, p14164_0]
                                        · have p14164_0 := h14164c.1
                                          have p14164_1 := h14164c.2.1
                                          have p14164_2 := h14164c.2.2.1
                                          have p14164_3 := h14164c.2.2.2
                                          linarith only [hlam, p14164_0]
                                        · have p14164_0 := h14164c.1
                                          have p14164_1 := h14164c.2.1
                                          have p14164_2 := h14164c.2.2.1
                                          have p14164_3 := h14164c.2.2.2
                                          linarith only [h1, h13951, h14152, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p14164_1]
                                        · have p14164_0 := h14164c.1
                                          have p14164_1 := h14164c.2.1
                                          have p14164_2 := h14164c.2.2.1
                                          have p14164_3 := h14164c.2.2.2
                                          linarith only [h13952, hlam, p14164_0]
                                        · have p14164_0 := h14164c.1
                                          have p14164_1 := h14164c.2.1
                                          have p14164_2 := h14164c.2.2.1
                                          have p14164_3 := h14164c.2.2.2
                                          linarith only [h14156, hlam, p14164_1]
                                        · have p14164_0 := h14164c.1
                                          have p14164_1 := h14164c.2.1
                                          have p14164_2 := h14164c.2.2.1
                                          have p14164_3 := h14164c.2.2.2
                                          linarith only [h14158, hlam, p14164_0]
                                        · have p14164_0 := h14164c.1
                                          have p14164_1 := h14164c.2.1
                                          have p14164_2 := h14164c.2.2.1
                                          have p14164_3 := h14164c.2.2.2
                                          linarith only [h14159, hlam, p14164_0]
                                        · have p14164_0 := h14164c.1
                                          have p14164_1 := h14164c.2.1
                                          have p14164_2 := h14164c.2.2.1
                                          have p14164_3 := h14164c.2.2.2
                                          linarith only [hlam, p14164_0]
                                      · linarith only [h1, h13951, h14152, h14159, h14163, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · linarith only [h1, h13952, h13955, h14159, h14162, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                  · linarith only [h0, h1, h14152, h14156, h14161, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                · linarith only [h1, h13951, h14152, h14154, h14156, h14160, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h1, h13951, h14151, h14154, h14156, h14159, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h0, h1, h14156, h14158, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h0, h1, h14156, h14157, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h1, h13951, h13955, h14148, h14152, h14156, hc12, hc23, hlam, hphi]
                  · linarith only [h13955, h14148, h14151, hlam]
                · linarith only [h1, h13951, h13955, h14148, h14150, hlam]
              · linarith only [h1, h13951, h14149, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h14211 | h14211
              · rcases m.htr 0 3 5 (by decide) (by decide) with h14212 | h14212
                · rcases m.htr 0 4 5 (by decide) (by decide) with h14213 | h14213
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h14214 | h14214
                    · linarith only [h0, h1, h13953, h14214, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h14216 | h14216
                      · linarith only [h0, h1, h13955, h14213, h14214, h14216, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h14218 | h14218
                        · linarith only [h0, h14148, h14218, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h14220 | h14220
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h14221 | h14221
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h14222 | h14222
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h14223 | h14223
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h14224 | h14224
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h14225 | h14225
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h14226 | h14226
                                      · rcases h1bigk with h14227c | h14227c | h14227c | h14227c | h14227c | h14227c | h14227c | h14227c | h14227c | h14227c | h14227c | h14227c | h14227c | h14227c | h14227c | h14227c | h14227c | h14227c | h14227c | h14227c | h14227c | h14227c | h14227c | h14227c | h14227c
                                        · have p14227_0 := h14227c.1
                                          have p14227_1 := h14227c.2.1
                                          have p14227_2 := h14227c.2.2.1
                                          have p14227_3 := h14227c.2.2.2
                                          linarith only [hlam, p14227_0]
                                        · have p14227_0 := h14227c.1
                                          have p14227_1 := h14227c.2.1
                                          have p14227_2 := h14227c.2.2.1
                                          have p14227_3 := h14227c.2.2.2
                                          linarith only [h1, h14214, hc12, hc23, hlam, hphi, p14227_1]
                                        · have p14227_0 := h14227c.1
                                          have p14227_1 := h14227c.2.1
                                          have p14227_2 := h14227c.2.2.1
                                          have p14227_3 := h14227c.2.2.2
                                          linarith only [h1, hlam, p14227_0]
                                        · have p14227_0 := h14227c.1
                                          have p14227_1 := h14227c.2.1
                                          have p14227_2 := h14227c.2.2.1
                                          have p14227_3 := h14227c.2.2.2
                                          linarith only [h1, h14214, h14216, hc12, hc23, hlam, hphi, p14227_1]
                                        · have p14227_0 := h14227c.1
                                          have p14227_1 := h14227c.2.1
                                          have p14227_2 := h14227c.2.2.1
                                          have p14227_3 := h14227c.2.2.2
                                          linarith only [h1, h14214, h14218, hc12, hc23, hlam, hphi, p14227_1]
                                        · have p14227_0 := h14227c.1
                                          have p14227_1 := h14227c.2.1
                                          have p14227_2 := h14227c.2.2.1
                                          have p14227_3 := h14227c.2.2.2
                                          linarith only [h0, hlam, p14227_0]
                                        · have p14227_0 := h14227c.1
                                          have p14227_1 := h14227c.2.1
                                          have p14227_2 := h14227c.2.2.1
                                          have p14227_3 := h14227c.2.2.2
                                          linarith only [hlam, p14227_0]
                                        · have p14227_0 := h14227c.1
                                          have p14227_1 := h14227c.2.1
                                          have p14227_2 := h14227c.2.2.1
                                          have p14227_3 := h14227c.2.2.2
                                          linarith only [h14214, hlam, p14227_0]
                                        · have p14227_0 := h14227c.1
                                          have p14227_1 := h14227c.2.1
                                          have p14227_2 := h14227c.2.2.1
                                          have p14227_3 := h14227c.2.2.2
                                          linarith only [h14216, hlam, p14227_0]
                                        · have p14227_0 := h14227c.1
                                          have p14227_1 := h14227c.2.1
                                          have p14227_2 := h14227c.2.2.1
                                          have p14227_3 := h14227c.2.2.2
                                          linarith only [h14218, hlam, p14227_0]
                                        · have p14227_0 := h14227c.1
                                          have p14227_1 := h14227c.2.1
                                          have p14227_2 := h14227c.2.2.1
                                          have p14227_3 := h14227c.2.2.2
                                          linarith only [h0, h14214, hc12, hc23, hlam, hphi, p14227_1]
                                        · have p14227_0 := h14227c.1
                                          have p14227_1 := h14227c.2.1
                                          have p14227_2 := h14227c.2.2.1
                                          have p14227_3 := h14227c.2.2.2
                                          rcases p14227_3 (m.d 0 1) (by simp) with h14239 | h14239
                                          · linarith only [h1, h14239, hlam]
                                          · linarith only [h0, h14239, hlam]
                                        · have p14227_0 := h14227c.1
                                          have p14227_1 := h14227c.2.1
                                          have p14227_2 := h14227c.2.2.1
                                          have p14227_3 := h14227c.2.2.2
                                          linarith only [hlam, p14227_0]
                                        · have p14227_0 := h14227c.1
                                          have p14227_1 := h14227c.2.1
                                          have p14227_2 := h14227c.2.2.1
                                          have p14227_3 := h14227c.2.2.2
                                          rcases p14227_3 (m.d 0 1) (by simp) with h14243 | h14243
                                          · linarith only [h1, h14243, hlam]
                                          · linarith only [h13951, h14243, hlam]
                                        · have p14227_0 := h14227c.1
                                          have p14227_1 := h14227c.2.1
                                          have p14227_2 := h14227c.2.2.1
                                          have p14227_3 := h14227c.2.2.2
                                          rcases p14227_3 (m.d 0 1) (by simp) with h14246 | h14246
                                          · linarith only [h1, h14246, hlam]
                                          · linarith only [h13952, h14246, hlam]
                                        · have p14227_0 := h14227c.1
                                          have p14227_1 := h14227c.2.1
                                          have p14227_2 := h14227c.2.2.1
                                          have p14227_3 := h14227c.2.2.2
                                          linarith only [h13951, hlam, p14227_0]
                                        · have p14227_0 := h14227c.1
                                          have p14227_1 := h14227c.2.1
                                          have p14227_2 := h14227c.2.2.1
                                          have p14227_3 := h14227c.2.2.2
                                          linarith only [h1, h13951, h14214, hc12, hc23, hlam, hphi, p14227_1]
                                        · have p14227_0 := h14227c.1
                                          have p14227_1 := h14227c.2.1
                                          have p14227_2 := h14227c.2.2.1
                                          have p14227_3 := h14227c.2.2.2
                                          linarith only [h14220, hlam, p14227_0]
                                        · have p14227_0 := h14227c.1
                                          have p14227_1 := h14227c.2.1
                                          have p14227_2 := h14227c.2.2.1
                                          have p14227_3 := h14227c.2.2.2
                                          linarith only [hlam, p14227_0]
                                        · have p14227_0 := h14227c.1
                                          have p14227_1 := h14227c.2.1
                                          have p14227_2 := h14227c.2.2.1
                                          have p14227_3 := h14227c.2.2.2
                                          linarith only [h1, h13951, h14214, h14218, hc12, hc23, hlam, hphi, p14227_1]
                                        · have p14227_0 := h14227c.1
                                          have p14227_1 := h14227c.2.1
                                          have p14227_2 := h14227c.2.2.1
                                          have p14227_3 := h14227c.2.2.2
                                          linarith only [h13952, hlam, p14227_0]
                                        · have p14227_0 := h14227c.1
                                          have p14227_1 := h14227c.2.1
                                          have p14227_2 := h14227c.2.2.1
                                          have p14227_3 := h14227c.2.2.2
                                          linarith only [h1, h13952, h14214, hc12, hc23, hlam, hphi, p14227_1]
                                        · have p14227_0 := h14227c.1
                                          have p14227_1 := h14227c.2.1
                                          have p14227_2 := h14227c.2.2.1
                                          have p14227_3 := h14227c.2.2.2
                                          linarith only [h14221, hlam, p14227_0]
                                        · have p14227_0 := h14227c.1
                                          have p14227_1 := h14227c.2.1
                                          have p14227_2 := h14227c.2.2.1
                                          have p14227_3 := h14227c.2.2.2
                                          linarith only [h14222, hlam, p14227_0]
                                        · have p14227_0 := h14227c.1
                                          have p14227_1 := h14227c.2.1
                                          have p14227_2 := h14227c.2.2.1
                                          have p14227_3 := h14227c.2.2.2
                                          linarith only [hlam, p14227_0]
                                      · linarith only [h1, h13951, h14214, h14222, h14226, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · linarith only [h1, h13951, h14214, h14222, h14225, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h1, h13951, h14214, h14222, h14224, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                · linarith only [h1, h13951, h14214, h14222, h14223, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h1, h13951, h14213, h14214, h14216, h14222, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1, h14221, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h0, h1, h14220, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h14266 | h14266
                    · linarith only [h0, h13953, h14266, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h14268 | h14268
                      · linarith only [h0, h13955, h14268, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h14270 | h14270
                        · linarith only [h0, h14148, h14270, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h14272 | h14272
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h14273 | h14273
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h14274 | h14274
                              · linarith only [h1, h13951, h14213, h14274, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h14276 | h14276
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h14277 | h14277
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h14278 | h14278
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h14279 | h14279
                                      · linarith only [h13951, h14213, h14272, h14279, hlam]
                                      · rcases h1bigk with h14281c | h14281c | h14281c | h14281c | h14281c | h14281c | h14281c | h14281c | h14281c | h14281c | h14281c | h14281c | h14281c | h14281c | h14281c | h14281c | h14281c | h14281c | h14281c | h14281c | h14281c | h14281c | h14281c | h14281c | h14281c
                                        · have p14281_0 := h14281c.1
                                          have p14281_1 := h14281c.2.1
                                          have p14281_2 := h14281c.2.2.1
                                          have p14281_3 := h14281c.2.2.2
                                          linarith only [hlam, p14281_0]
                                        · have p14281_0 := h14281c.1
                                          have p14281_1 := h14281c.2.1
                                          have p14281_2 := h14281c.2.2.1
                                          have p14281_3 := h14281c.2.2.2
                                          linarith only [h1, h14266, hc12, hc23, hlam, hphi, p14281_1]
                                        · have p14281_0 := h14281c.1
                                          have p14281_1 := h14281c.2.1
                                          have p14281_2 := h14281c.2.2.1
                                          have p14281_3 := h14281c.2.2.2
                                          linarith only [h1, hlam, p14281_0]
                                        · have p14281_0 := h14281c.1
                                          have p14281_1 := h14281c.2.1
                                          have p14281_2 := h14281c.2.2.1
                                          have p14281_3 := h14281c.2.2.2
                                          linarith only [h1, h14266, h14268, hc12, hc23, hlam, hphi, p14281_1]
                                        · have p14281_0 := h14281c.1
                                          have p14281_1 := h14281c.2.1
                                          have p14281_2 := h14281c.2.2.1
                                          have p14281_3 := h14281c.2.2.2
                                          linarith only [h1, h14266, h14270, hc12, hc23, hlam, hphi, p14281_1]
                                        · have p14281_0 := h14281c.1
                                          have p14281_1 := h14281c.2.1
                                          have p14281_2 := h14281c.2.2.1
                                          have p14281_3 := h14281c.2.2.2
                                          linarith only [h0, hlam, p14281_0]
                                        · have p14281_0 := h14281c.1
                                          have p14281_1 := h14281c.2.1
                                          have p14281_2 := h14281c.2.2.1
                                          have p14281_3 := h14281c.2.2.2
                                          linarith only [hlam, p14281_0]
                                        · have p14281_0 := h14281c.1
                                          have p14281_1 := h14281c.2.1
                                          have p14281_2 := h14281c.2.2.1
                                          have p14281_3 := h14281c.2.2.2
                                          linarith only [h14266, hlam, p14281_0]
                                        · have p14281_0 := h14281c.1
                                          have p14281_1 := h14281c.2.1
                                          have p14281_2 := h14281c.2.2.1
                                          have p14281_3 := h14281c.2.2.2
                                          linarith only [h14268, hlam, p14281_0]
                                        · have p14281_0 := h14281c.1
                                          have p14281_1 := h14281c.2.1
                                          have p14281_2 := h14281c.2.2.1
                                          have p14281_3 := h14281c.2.2.2
                                          linarith only [h14270, hlam, p14281_0]
                                        · have p14281_0 := h14281c.1
                                          have p14281_1 := h14281c.2.1
                                          have p14281_2 := h14281c.2.2.1
                                          have p14281_3 := h14281c.2.2.2
                                          linarith only [h0, h14266, hc12, hc23, hlam, hphi, p14281_1]
                                        · have p14281_0 := h14281c.1
                                          have p14281_1 := h14281c.2.1
                                          have p14281_2 := h14281c.2.2.1
                                          have p14281_3 := h14281c.2.2.2
                                          rcases p14281_3 (m.d 0 1) (by simp) with h14293 | h14293
                                          · linarith only [h1, h14293, hlam]
                                          · linarith only [h0, h14293, hlam]
                                        · have p14281_0 := h14281c.1
                                          have p14281_1 := h14281c.2.1
                                          have p14281_2 := h14281c.2.2.1
                                          have p14281_3 := h14281c.2.2.2
                                          linarith only [hlam, p14281_0]
                                        · have p14281_0 := h14281c.1
                                          have p14281_1 := h14281c.2.1
                                          have p14281_2 := h14281c.2.2.1
                                          have p14281_3 := h14281c.2.2.2
                                          rcases p14281_3 (m.d 0 1) (by simp) with h14297 | h14297
                                          · linarith only [h1, h14297, hlam]
                                          · linarith only [h13951, h14297, hlam]
                                        · have p14281_0 := h14281c.1
                                          have p14281_1 := h14281c.2.1
                                          have p14281_2 := h14281c.2.2.1
                                          have p14281_3 := h14281c.2.2.2
                                          rcases p14281_3 (m.d 0 1) (by simp) with h14300 | h14300
                                          · linarith only [h1, h14300, hlam]
                                          · linarith only [h13952, h14300, hlam]
                                        · have p14281_0 := h14281c.1
                                          have p14281_1 := h14281c.2.1
                                          have p14281_2 := h14281c.2.2.1
                                          have p14281_3 := h14281c.2.2.2
                                          linarith only [h13951, hlam, p14281_0]
                                        · have p14281_0 := h14281c.1
                                          have p14281_1 := h14281c.2.1
                                          have p14281_2 := h14281c.2.2.1
                                          have p14281_3 := h14281c.2.2.2
                                          linarith only [h1, h13952, h14266, h14274, hc12, hc23, hlam, hphi, p14281_1]
                                        · have p14281_0 := h14281c.1
                                          have p14281_1 := h14281c.2.1
                                          have p14281_2 := h14281c.2.2.1
                                          have p14281_3 := h14281c.2.2.2
                                          linarith only [h14272, hlam, p14281_0]
                                        · have p14281_0 := h14281c.1
                                          have p14281_1 := h14281c.2.1
                                          have p14281_2 := h14281c.2.2.1
                                          have p14281_3 := h14281c.2.2.2
                                          linarith only [hlam, p14281_0]
                                        · have p14281_0 := h14281c.1
                                          have p14281_1 := h14281c.2.1
                                          have p14281_2 := h14281c.2.2.1
                                          have p14281_3 := h14281c.2.2.2
                                          linarith only [h14274, hlam, p14281_1]
                                        · have p14281_0 := h14281c.1
                                          have p14281_1 := h14281c.2.1
                                          have p14281_2 := h14281c.2.2.1
                                          have p14281_3 := h14281c.2.2.2
                                          linarith only [h13952, hlam, p14281_0]
                                        · have p14281_0 := h14281c.1
                                          have p14281_1 := h14281c.2.1
                                          have p14281_2 := h14281c.2.2.1
                                          have p14281_3 := h14281c.2.2.2
                                          linarith only [h1, h13952, h14266, hc12, hc23, hlam, hphi, p14281_1]
                                        · have p14281_0 := h14281c.1
                                          have p14281_1 := h14281c.2.1
                                          have p14281_2 := h14281c.2.2.1
                                          have p14281_3 := h14281c.2.2.2
                                          linarith only [h14273, hlam, p14281_0]
                                        · have p14281_0 := h14281c.1
                                          have p14281_1 := h14281c.2.1
                                          have p14281_2 := h14281c.2.2.1
                                          have p14281_3 := h14281c.2.2.2
                                          linarith only [h1, h13952, h14266, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14281_1]
                                        · have p14281_0 := h14281c.1
                                          have p14281_1 := h14281c.2.1
                                          have p14281_2 := h14281c.2.2.1
                                          have p14281_3 := h14281c.2.2.2
                                          linarith only [hlam, p14281_0]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h14313 | h14313
                                      · linarith only [h0, h13955, h14278, h14313, hc12, hc34, hlam, hphi, ht23]
                                      · rcases h1bigk with h14315c | h14315c | h14315c | h14315c | h14315c | h14315c | h14315c | h14315c | h14315c | h14315c | h14315c | h14315c | h14315c | h14315c | h14315c | h14315c | h14315c | h14315c | h14315c | h14315c | h14315c | h14315c | h14315c | h14315c | h14315c
                                        · have p14315_0 := h14315c.1
                                          have p14315_1 := h14315c.2.1
                                          have p14315_2 := h14315c.2.2.1
                                          have p14315_3 := h14315c.2.2.2
                                          linarith only [hlam, p14315_0]
                                        · have p14315_0 := h14315c.1
                                          have p14315_1 := h14315c.2.1
                                          have p14315_2 := h14315c.2.2.1
                                          have p14315_3 := h14315c.2.2.2
                                          linarith only [h1, h14266, hc12, hc23, hlam, hphi, p14315_1]
                                        · have p14315_0 := h14315c.1
                                          have p14315_1 := h14315c.2.1
                                          have p14315_2 := h14315c.2.2.1
                                          have p14315_3 := h14315c.2.2.2
                                          linarith only [h1, hlam, p14315_0]
                                        · have p14315_0 := h14315c.1
                                          have p14315_1 := h14315c.2.1
                                          have p14315_2 := h14315c.2.2.1
                                          have p14315_3 := h14315c.2.2.2
                                          linarith only [h1, h14266, h14268, hc12, hc23, hlam, hphi, p14315_1]
                                        · have p14315_0 := h14315c.1
                                          have p14315_1 := h14315c.2.1
                                          have p14315_2 := h14315c.2.2.1
                                          have p14315_3 := h14315c.2.2.2
                                          linarith only [h1, h14266, h14270, hc12, hc23, hlam, hphi, p14315_1]
                                        · have p14315_0 := h14315c.1
                                          have p14315_1 := h14315c.2.1
                                          have p14315_2 := h14315c.2.2.1
                                          have p14315_3 := h14315c.2.2.2
                                          linarith only [h0, hlam, p14315_0]
                                        · have p14315_0 := h14315c.1
                                          have p14315_1 := h14315c.2.1
                                          have p14315_2 := h14315c.2.2.1
                                          have p14315_3 := h14315c.2.2.2
                                          linarith only [hlam, p14315_0]
                                        · have p14315_0 := h14315c.1
                                          have p14315_1 := h14315c.2.1
                                          have p14315_2 := h14315c.2.2.1
                                          have p14315_3 := h14315c.2.2.2
                                          linarith only [h14266, hlam, p14315_0]
                                        · have p14315_0 := h14315c.1
                                          have p14315_1 := h14315c.2.1
                                          have p14315_2 := h14315c.2.2.1
                                          have p14315_3 := h14315c.2.2.2
                                          linarith only [h14268, hlam, p14315_0]
                                        · have p14315_0 := h14315c.1
                                          have p14315_1 := h14315c.2.1
                                          have p14315_2 := h14315c.2.2.1
                                          have p14315_3 := h14315c.2.2.2
                                          linarith only [h14270, hlam, p14315_0]
                                        · have p14315_0 := h14315c.1
                                          have p14315_1 := h14315c.2.1
                                          have p14315_2 := h14315c.2.2.1
                                          have p14315_3 := h14315c.2.2.2
                                          linarith only [h0, h14266, hc12, hc23, hlam, hphi, p14315_1]
                                        · have p14315_0 := h14315c.1
                                          have p14315_1 := h14315c.2.1
                                          have p14315_2 := h14315c.2.2.1
                                          have p14315_3 := h14315c.2.2.2
                                          rcases p14315_3 (m.d 0 1) (by simp) with h14327 | h14327
                                          · linarith only [h1, h14327, hlam]
                                          · linarith only [h0, h14327, hlam]
                                        · have p14315_0 := h14315c.1
                                          have p14315_1 := h14315c.2.1
                                          have p14315_2 := h14315c.2.2.1
                                          have p14315_3 := h14315c.2.2.2
                                          linarith only [hlam, p14315_0]
                                        · have p14315_0 := h14315c.1
                                          have p14315_1 := h14315c.2.1
                                          have p14315_2 := h14315c.2.2.1
                                          have p14315_3 := h14315c.2.2.2
                                          rcases p14315_3 (m.d 0 1) (by simp) with h14331 | h14331
                                          · linarith only [h1, h14331, hlam]
                                          · linarith only [h13951, h14331, hlam]
                                        · have p14315_0 := h14315c.1
                                          have p14315_1 := h14315c.2.1
                                          have p14315_2 := h14315c.2.2.1
                                          have p14315_3 := h14315c.2.2.2
                                          rcases p14315_3 (m.d 0 1) (by simp) with h14334 | h14334
                                          · linarith only [h1, h14334, hlam]
                                          · linarith only [h13952, h14334, hlam]
                                        · have p14315_0 := h14315c.1
                                          have p14315_1 := h14315c.2.1
                                          have p14315_2 := h14315c.2.2.1
                                          have p14315_3 := h14315c.2.2.2
                                          linarith only [h13951, hlam, p14315_0]
                                        · have p14315_0 := h14315c.1
                                          have p14315_1 := h14315c.2.1
                                          have p14315_2 := h14315c.2.2.1
                                          have p14315_3 := h14315c.2.2.2
                                          linarith only [h1, h13951, h14266, hc12, hc23, hlam, hphi, p14315_1]
                                        · have p14315_0 := h14315c.1
                                          have p14315_1 := h14315c.2.1
                                          have p14315_2 := h14315c.2.2.1
                                          have p14315_3 := h14315c.2.2.2
                                          linarith only [h14272, hlam, p14315_0]
                                        · have p14315_0 := h14315c.1
                                          have p14315_1 := h14315c.2.1
                                          have p14315_2 := h14315c.2.2.1
                                          have p14315_3 := h14315c.2.2.2
                                          linarith only [hlam, p14315_0]
                                        · have p14315_0 := h14315c.1
                                          have p14315_1 := h14315c.2.1
                                          have p14315_2 := h14315c.2.2.1
                                          have p14315_3 := h14315c.2.2.2
                                          linarith only [h14274, hlam, p14315_1]
                                        · have p14315_0 := h14315c.1
                                          have p14315_1 := h14315c.2.1
                                          have p14315_2 := h14315c.2.2.1
                                          have p14315_3 := h14315c.2.2.2
                                          linarith only [h13952, hlam, p14315_0]
                                        · have p14315_0 := h14315c.1
                                          have p14315_1 := h14315c.2.1
                                          have p14315_2 := h14315c.2.2.1
                                          have p14315_3 := h14315c.2.2.2
                                          linarith only [h1, h13952, h14266, hc12, hc23, hlam, hphi, p14315_1]
                                        · have p14315_0 := h14315c.1
                                          have p14315_1 := h14315c.2.1
                                          have p14315_2 := h14315c.2.2.1
                                          have p14315_3 := h14315c.2.2.2
                                          linarith only [h14273, hlam, p14315_0]
                                        · have p14315_0 := h14315c.1
                                          have p14315_1 := h14315c.2.1
                                          have p14315_2 := h14315c.2.2.1
                                          have p14315_3 := h14315c.2.2.2
                                          linarith only [h1, h13952, h14266, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14315_1]
                                        · have p14315_0 := h14315c.1
                                          have p14315_1 := h14315c.2.1
                                          have p14315_2 := h14315c.2.2.1
                                          have p14315_3 := h14315c.2.2.2
                                          linarith only [hlam, p14315_0]
                                  · linarith only [h1, h13952, h14266, h14273, h14277, hlam]
                                · linarith only [h0, h1, h14266, h14276, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h1, h13951, h14268, h14273, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h13951, h14268, h14272, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h1, h13952, h14212, hlam]
              · linarith only [h1, h13951, h14211, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h14353 | h14353
        · linarith only [h0, h1, h14353, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h14355 | h14355
          · rcases m.htr 0 2 5 (by decide) (by decide) with h14356 | h14356
            · linarith only [h0, h13952, h14356, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h14358 | h14358
              · rcases m.htr 0 3 5 (by decide) (by decide) with h14359 | h14359
                · rcases m.htr 0 4 5 (by decide) (by decide) with h14360 | h14360
                  · linarith only [h0, h13952, h14355, h14360, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h14362 | h14362
                    · linarith only [h0, h1, h14353, h14355, h14362, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h14364 | h14364
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h14365 | h14365
                        · linarith only [h0, h13952, h14356, h14365, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h14367 | h14367
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h14368 | h14368
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h14369 | h14369
                              · linarith only [h0, h13951, h13952, h14355, h14360, h14369, hlam]
                              · linarith only [h0, h13952, h14364, h14369, hc24, hc45, hlam, hphi]
                            · linarith only [h0, h1, h14359, h14364, h14368, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h0, h1, h14364, h14367, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h14353, h14355, h14364, hc12, hc23, hlam, hphi]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h14375 | h14375
                  · linarith only [h0, h1, h14355, h14359, h14375, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h14377 | h14377
                    · linarith only [h0, h1, h14353, h14377, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h14379 | h14379
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h14380 | h14380
                        · linarith only [h0, h1, h14356, h14359, h14380, hc02, hc35, hlam, hphi, ht23]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h14382 | h14382
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h14383 | h14383
                            · linarith only [h0, h1, h14359, h14377, h14379, h14383, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h1, h14379, h14383, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h14379, h14382, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h14353, h14355, h14379, hc12, hc23, hlam, hphi]
              · linarith only [h0, h1, h14355, h14358, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h14389 | h14389
            · linarith only [h13951, h13952, h14355, h14389, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h14391 | h14391
              · rcases m.htr 0 3 5 (by decide) (by decide) with h14392 | h14392
                · rcases m.htr 0 4 5 (by decide) (by decide) with h14393 | h14393
                  · linarith only [h13951, h13952, h14393, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h14395 | h14395
                    · linarith only [h0, h14353, h14395, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h14397 | h14397
                      · linarith only [h0, h14355, h14397, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h14399 | h14399
                        · linarith only [h0, h13952, h14389, h14399, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h14401 | h14401
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h14402 | h14402
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h14403 | h14403
                              · linarith only [h13951, h13952, h14355, h14393, h14402, h14403, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h14405 | h14405
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h14406 | h14406
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h14407 | h14407
                                    · linarith only [h0, h13952, h14403, h14405, h14407, hc12, hc23, hlam, hphi]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h14409 | h14409
                                      · linarith only [h13951, h13952, h14401, h14407, h14409, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                      · rcases h1bigk with h14411c | h14411c | h14411c | h14411c | h14411c | h14411c | h14411c | h14411c | h14411c | h14411c | h14411c | h14411c | h14411c | h14411c | h14411c | h14411c | h14411c | h14411c | h14411c | h14411c | h14411c | h14411c | h14411c | h14411c | h14411c
                                        · have p14411_0 := h14411c.1
                                          have p14411_1 := h14411c.2.1
                                          have p14411_2 := h14411c.2.2.1
                                          have p14411_3 := h14411c.2.2.2
                                          linarith only [hlam, p14411_0]
                                        · have p14411_0 := h14411c.1
                                          have p14411_1 := h14411c.2.1
                                          have p14411_2 := h14411c.2.2.1
                                          have p14411_3 := h14411c.2.2.2
                                          linarith only [h13952, h14399, h14407, hc12, hc45, hlam, hphi, ht23, ht34, p14411_1]
                                        · have p14411_0 := h14411c.1
                                          have p14411_1 := h14411c.2.1
                                          have p14411_2 := h14411c.2.2.1
                                          have p14411_3 := h14411c.2.2.2
                                          linarith only [h1, hlam, p14411_0]
                                        · have p14411_0 := h14411c.1
                                          have p14411_1 := h14411c.2.1
                                          have p14411_2 := h14411c.2.2.1
                                          have p14411_3 := h14411c.2.2.2
                                          linarith only [h13952, h14399, h14407, hc14, hc45, hlam, hphi, p14411_1]
                                        · have p14411_0 := h14411c.1
                                          have p14411_1 := h14411c.2.1
                                          have p14411_2 := h14411c.2.2.1
                                          have p14411_3 := h14411c.2.2.2
                                          linarith only [h13952, hlam, p14411_0]
                                        · have p14411_0 := h14411c.1
                                          have p14411_1 := h14411c.2.1
                                          have p14411_2 := h14411c.2.2.1
                                          have p14411_3 := h14411c.2.2.2
                                          linarith only [h0, hlam, p14411_0]
                                        · have p14411_0 := h14411c.1
                                          have p14411_1 := h14411c.2.1
                                          have p14411_2 := h14411c.2.2.1
                                          have p14411_3 := h14411c.2.2.2
                                          linarith only [hlam, p14411_0]
                                        · have p14411_0 := h14411c.1
                                          have p14411_1 := h14411c.2.1
                                          have p14411_2 := h14411c.2.2.1
                                          have p14411_3 := h14411c.2.2.2
                                          linarith only [h14395, hlam, p14411_0]
                                        · have p14411_0 := h14411c.1
                                          have p14411_1 := h14411c.2.1
                                          have p14411_2 := h14411c.2.2.1
                                          have p14411_3 := h14411c.2.2.2
                                          linarith only [h14397, hlam, p14411_0]
                                        · have p14411_0 := h14411c.1
                                          have p14411_1 := h14411c.2.1
                                          have p14411_2 := h14411c.2.2.1
                                          have p14411_3 := h14411c.2.2.2
                                          linarith only [h14399, hlam, p14411_0]
                                        · have p14411_0 := h14411c.1
                                          have p14411_1 := h14411c.2.1
                                          have p14411_2 := h14411c.2.2.1
                                          have p14411_3 := h14411c.2.2.2
                                          linarith only [h0, h14395, hc12, hc23, hlam, hphi, p14411_1]
                                        · have p14411_0 := h14411c.1
                                          have p14411_1 := h14411c.2.1
                                          have p14411_2 := h14411c.2.2.1
                                          have p14411_3 := h14411c.2.2.2
                                          rcases p14411_3 (m.d 0 1) (by simp) with h14423 | h14423
                                          · linarith only [h1, h14423, hlam]
                                          · linarith only [h0, h14423, hlam]
                                        · have p14411_0 := h14411c.1
                                          have p14411_1 := h14411c.2.1
                                          have p14411_2 := h14411c.2.2.1
                                          have p14411_3 := h14411c.2.2.2
                                          linarith only [hlam, p14411_0]
                                        · have p14411_0 := h14411c.1
                                          have p14411_1 := h14411c.2.1
                                          have p14411_2 := h14411c.2.2.1
                                          have p14411_3 := h14411c.2.2.2
                                          rcases p14411_3 (m.d 0 1) (by simp) with h14427 | h14427
                                          · linarith only [h1, h14427, hlam]
                                          · linarith only [h13951, h14427, hlam]
                                        · have p14411_0 := h14411c.1
                                          have p14411_1 := h14411c.2.1
                                          have p14411_2 := h14411c.2.2.1
                                          have p14411_3 := h14411c.2.2.2
                                          linarith only [h13951, h13952, h14395, h14397, hc12, hc23, hlam, hphi, p14411_1]
                                        · have p14411_0 := h14411c.1
                                          have p14411_1 := h14411c.2.1
                                          have p14411_2 := h14411c.2.2.1
                                          have p14411_3 := h14411c.2.2.2
                                          linarith only [h13951, hlam, p14411_0]
                                        · have p14411_0 := h14411c.1
                                          have p14411_1 := h14411c.2.1
                                          have p14411_2 := h14411c.2.2.1
                                          have p14411_3 := h14411c.2.2.2
                                          linarith only [h13951, h13952, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p14411_1]
                                        · have p14411_0 := h14411c.1
                                          have p14411_1 := h14411c.2.1
                                          have p14411_2 := h14411c.2.2.1
                                          have p14411_3 := h14411c.2.2.2
                                          linarith only [h14401, hlam, p14411_0]
                                        · have p14411_0 := h14411c.1
                                          have p14411_1 := h14411c.2.1
                                          have p14411_2 := h14411c.2.2.1
                                          have p14411_3 := h14411c.2.2.2
                                          linarith only [hlam, p14411_0]
                                        · have p14411_0 := h14411c.1
                                          have p14411_1 := h14411c.2.1
                                          have p14411_2 := h14411c.2.2.1
                                          have p14411_3 := h14411c.2.2.2
                                          linarith only [h14403, hlam, p14411_1]
                                        · have p14411_0 := h14411c.1
                                          have p14411_1 := h14411c.2.1
                                          have p14411_2 := h14411c.2.2.1
                                          have p14411_3 := h14411c.2.2.2
                                          linarith only [h13951, h14399, h14407, hc14, hc45, hlam, hphi, p14411_1]
                                        · have p14411_0 := h14411c.1
                                          have p14411_1 := h14411c.2.1
                                          have p14411_2 := h14411c.2.2.1
                                          have p14411_3 := h14411c.2.2.2
                                          rcases p14411_3 (m.d 0 1) (by simp) with h14437 | h14437
                                          · linarith only [h13952, h14437, hlam]
                                          · linarith only [h0, h14437, hlam]
                                        · have p14411_0 := h14411c.1
                                          have p14411_1 := h14411c.2.1
                                          have p14411_2 := h14411c.2.2.1
                                          have p14411_3 := h14411c.2.2.2
                                          linarith only [h14402, hlam, p14411_0]
                                        · have p14411_0 := h14411c.1
                                          have p14411_1 := h14411c.2.1
                                          have p14411_2 := h14411c.2.2.1
                                          have p14411_3 := h14411c.2.2.2
                                          rcases p14411_3 (m.d 0 1) (by simp) with h14441 | h14441
                                          · linarith only [h13952, h14441, hlam]
                                          · linarith only [h13951, h14441, hlam]
                                        · have p14411_0 := h14411c.1
                                          have p14411_1 := h14411c.2.1
                                          have p14411_2 := h14411c.2.2.1
                                          have p14411_3 := h14411c.2.2.2
                                          linarith only [hlam, p14411_0]
                                  · linarith only [h1, h14392, h14395, h14406, hlam]
                                · linarith only [h1, h13951, h14395, h14397, h14405, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h1, h14392, h14402, hlam]
                          · linarith only [h1, h13951, h14397, h14401, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h14449 | h14449
                  · linarith only [h13951, h13952, h14449, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h14451 | h14451
                    · linarith only [h0, h1, h14392, h14451, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h14453 | h14453
                      · linarith only [h0, h14355, h14453, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h14455 | h14455
                        · linarith only [h0, h14389, h14455, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h14457 | h14457
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h14458 | h14458
                            · linarith only [h0, h1, h14392, h14451, h14458, hc12, hc23, hlam, hphi]
                            · linarith only [h1, h13951, h14453, h14458, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h13951, h14453, h14457, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h13951, h14391, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h14463 | h14463
      · rcases m.htr 0 2 3 (by decide) (by decide) with h14464 | h14464
        · linarith only [h0, h1, h14464, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h14466 | h14466
          · linarith only [h0, h13951, h14466, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h14468 | h14468
            · rcases m.htr 0 3 4 (by decide) (by decide) with h14469 | h14469
              · rcases m.htr 0 3 5 (by decide) (by decide) with h14470 | h14470
                · rcases m.htr 0 4 5 (by decide) (by decide) with h14471 | h14471
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h14472 | h14472
                    · linarith only [h0, h1, h14464, h14468, h14472, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h14474 | h14474
                      · linarith only [h0, h13951, h14466, h14474, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h14476 | h14476
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h14477 | h14477
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h14478 | h14478
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h14479 | h14479
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h14480 | h14480
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h14481 | h14481
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h14482 | h14482
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h14483 | h14483
                                      · rcases h1bigk with h14484c | h14484c | h14484c | h14484c | h14484c | h14484c | h14484c | h14484c | h14484c | h14484c | h14484c | h14484c | h14484c | h14484c | h14484c | h14484c | h14484c | h14484c | h14484c | h14484c | h14484c | h14484c | h14484c | h14484c | h14484c
                                        · have p14484_0 := h14484c.1
                                          have p14484_1 := h14484c.2.1
                                          have p14484_2 := h14484c.2.2.1
                                          have p14484_3 := h14484c.2.2.2
                                          linarith only [hlam, p14484_0]
                                        · have p14484_0 := h14484c.1
                                          have p14484_1 := h14484c.2.1
                                          have p14484_2 := h14484c.2.2.1
                                          have p14484_3 := h14484c.2.2.2
                                          linarith only [h13951, h14476, h14481, h14483, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p14484_1]
                                        · have p14484_0 := h14484c.1
                                          have p14484_1 := h14484c.2.1
                                          have p14484_2 := h14484c.2.2.1
                                          have p14484_3 := h14484c.2.2.2
                                          linarith only [h1, hlam, p14484_0]
                                        · have p14484_0 := h14484c.1
                                          have p14484_1 := h14484c.2.1
                                          have p14484_2 := h14484c.2.2.1
                                          have p14484_3 := h14484c.2.2.2
                                          linarith only [h13951, hlam, p14484_0]
                                        · have p14484_0 := h14484c.1
                                          have p14484_1 := h14484c.2.1
                                          have p14484_2 := h14484c.2.2.1
                                          have p14484_3 := h14484c.2.2.2
                                          rcases p14484_3 (m.d 0 1) (by simp) with h14489 | h14489
                                          · rcases p14484_3 (m.d 1 2) (by simp) with h14490 | h14490
                                            · linarith only [h0, h14490, hlam]
                                            · linarith only [h14476, h14490, hlam]
                                          · linarith only [h14489, hlam, p14484_0]
                                        · have p14484_0 := h14484c.1
                                          have p14484_1 := h14484c.2.1
                                          have p14484_2 := h14484c.2.2.1
                                          have p14484_3 := h14484c.2.2.2
                                          linarith only [h0, hlam, p14484_0]
                                        · have p14484_0 := h14484c.1
                                          have p14484_1 := h14484c.2.1
                                          have p14484_2 := h14484c.2.2.1
                                          have p14484_3 := h14484c.2.2.2
                                          linarith only [hlam, p14484_0]
                                        · have p14484_0 := h14484c.1
                                          have p14484_1 := h14484c.2.1
                                          have p14484_2 := h14484c.2.2.1
                                          have p14484_3 := h14484c.2.2.2
                                          linarith only [h14472, hlam, p14484_0]
                                        · have p14484_0 := h14484c.1
                                          have p14484_1 := h14484c.2.1
                                          have p14484_2 := h14484c.2.2.1
                                          have p14484_3 := h14484c.2.2.2
                                          linarith only [h14474, hlam, p14484_0]
                                        · have p14484_0 := h14484c.1
                                          have p14484_1 := h14484c.2.1
                                          have p14484_2 := h14484c.2.2.1
                                          have p14484_3 := h14484c.2.2.2
                                          linarith only [h0, h13951, h14472, h14477, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p14484_1]
                                        · have p14484_0 := h14484c.1
                                          have p14484_1 := h14484c.2.1
                                          have p14484_2 := h14484c.2.2.1
                                          have p14484_3 := h14484c.2.2.2
                                          linarith only [h0, h14472, hc12, hc23, hlam, hphi, p14484_1]
                                        · have p14484_0 := h14484c.1
                                          have p14484_1 := h14484c.2.1
                                          have p14484_2 := h14484c.2.2.1
                                          have p14484_3 := h14484c.2.2.2
                                          rcases p14484_3 (m.d 0 1) (by simp) with h14500 | h14500
                                          · linarith only [h1, h14500, hlam]
                                          · linarith only [h0, h14500, hlam]
                                        · have p14484_0 := h14484c.1
                                          have p14484_1 := h14484c.2.1
                                          have p14484_2 := h14484c.2.2.1
                                          have p14484_3 := h14484c.2.2.2
                                          linarith only [hlam, p14484_0]
                                        · have p14484_0 := h14484c.1
                                          have p14484_1 := h14484c.2.1
                                          have p14484_2 := h14484c.2.2.1
                                          have p14484_3 := h14484c.2.2.2
                                          linarith only [h0, h13951, h14472, h14476, h14481, h14483, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p14484_1]
                                        · have p14484_0 := h14484c.1
                                          have p14484_1 := h14484c.2.1
                                          have p14484_2 := h14484c.2.2.1
                                          have p14484_3 := h14484c.2.2.2
                                          rcases p14484_3 (m.d 0 1) (by simp) with h14505 | h14505
                                          · linarith only [h1, h14505, hlam]
                                          · linarith only [h14463, h14505, hlam]
                                        · have p14484_0 := h14484c.1
                                          have p14484_1 := h14484c.2.1
                                          have p14484_2 := h14484c.2.2.1
                                          have p14484_3 := h14484c.2.2.2
                                          linarith only [h0, h14476, h14481, h14483, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p14484_1]
                                        · have p14484_0 := h14484c.1
                                          have p14484_1 := h14484c.2.1
                                          have p14484_2 := h14484c.2.2.1
                                          have p14484_3 := h14484c.2.2.2
                                          rcases p14484_3 (m.d 0 1) (by simp) with h14509 | h14509
                                          · linarith only [h13951, h14509, hlam]
                                          · linarith only [h0, h14509, hlam]
                                        · have p14484_0 := h14484c.1
                                          have p14484_1 := h14484c.2.1
                                          have p14484_2 := h14484c.2.2.1
                                          have p14484_3 := h14484c.2.2.2
                                          linarith only [h14477, hlam, p14484_0]
                                        · have p14484_0 := h14484c.1
                                          have p14484_1 := h14484c.2.1
                                          have p14484_2 := h14484c.2.2.1
                                          have p14484_3 := h14484c.2.2.2
                                          linarith only [hlam, p14484_0]
                                        · have p14484_0 := h14484c.1
                                          have p14484_1 := h14484c.2.1
                                          have p14484_2 := h14484c.2.2.1
                                          have p14484_3 := h14484c.2.2.2
                                          rcases p14484_3 (m.d 0 1) (by simp) with h14514 | h14514
                                          · linarith only [h13951, h14514, hlam]
                                          · linarith only [h14463, h14514, hlam]
                                        · have p14484_0 := h14484c.1
                                          have p14484_1 := h14484c.2.1
                                          have p14484_2 := h14484c.2.2.1
                                          have p14484_3 := h14484c.2.2.2
                                          linarith only [h14463, hlam, p14484_0]
                                        · have p14484_0 := h14484c.1
                                          have p14484_1 := h14484c.2.1
                                          have p14484_2 := h14484c.2.2.1
                                          have p14484_3 := h14484c.2.2.2
                                          linarith only [h14476, hlam, p14484_1]
                                        · have p14484_0 := h14484c.1
                                          have p14484_1 := h14484c.2.1
                                          have p14484_2 := h14484c.2.2.1
                                          have p14484_3 := h14484c.2.2.2
                                          linarith only [h14478, hlam, p14484_0]
                                        · have p14484_0 := h14484c.1
                                          have p14484_1 := h14484c.2.1
                                          have p14484_2 := h14484c.2.2.1
                                          have p14484_3 := h14484c.2.2.2
                                          linarith only [h14479, hlam, p14484_0]
                                        · have p14484_0 := h14484c.1
                                          have p14484_1 := h14484c.2.1
                                          have p14484_2 := h14484c.2.2.1
                                          have p14484_3 := h14484c.2.2.2
                                          linarith only [hlam, p14484_0]
                                      · linarith only [h0, h13951, h14474, h14476, h14480, h14482, h14483, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · linarith only [h0, h13951, h14474, h14476, h14479, h14482, hc15, hc25, hlam, hphi, ht01, ht0b, ht5b]
                                  · linarith only [h0, h13951, h14474, h14476, h14480, h14481, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                · linarith only [h0, h13951, h14472, h14476, h14477, h14480, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h0, h13951, h14476, h14479, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                            · linarith only [h0, h13951, h14476, h14477, h14478, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h0, h1, h14469, h14476, h14477, hc03, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h13951, h14468, h14474, h14476, hc12, hc24, hlam, hphi]
                  · linarith only [h0, h13951, h14468, h14471, hlam]
                · linarith only [h0, h1, h14468, h14470, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h14532 | h14532
                · rcases m.htr 0 4 5 (by decide) (by decide) with h14533 | h14533
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h14534 | h14534
                    · linarith only [h0, h1, h14469, h14534, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h14536 | h14536
                      · linarith only [h0, h1, h14466, h14469, h14536, hc02, hc34, hlam, hphi, ht23]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h14538 | h14538
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h14539 | h14539
                          · linarith only [h0, h1, h14469, h14534, h14538, h14539, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · linarith only [h0, h1, h14538, h14539, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h0, h13951, h14468, h14536, h14538, hc12, hc24, hlam, hphi]
                  · linarith only [h0, h1, h14468, h14469, h14533, hlam]
                · linarith only [h0, h1, h14468, h14532, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h14545 | h14545
              · rcases m.htr 0 3 5 (by decide) (by decide) with h14546 | h14546
                · rcases m.htr 0 4 5 (by decide) (by decide) with h14547 | h14547
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h14548 | h14548
                    · linarith only [h0, h1, h14464, h14548, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h14550 | h14550
                      · linarith only [h0, h14466, h14550, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h14552 | h14552
                        · linarith only [h0, h14468, h14552, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h14554 | h14554
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h14555 | h14555
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h14556 | h14556
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h14557 | h14557
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h14558 | h14558
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h14559 | h14559
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h14560 | h14560
                                      · rcases h1bigk with h14561c | h14561c | h14561c | h14561c | h14561c | h14561c | h14561c | h14561c | h14561c | h14561c | h14561c | h14561c | h14561c | h14561c | h14561c | h14561c | h14561c | h14561c | h14561c | h14561c | h14561c | h14561c | h14561c | h14561c | h14561c
                                        · have p14561_0 := h14561c.1
                                          have p14561_1 := h14561c.2.1
                                          have p14561_2 := h14561c.2.2.1
                                          have p14561_3 := h14561c.2.2.2
                                          linarith only [hlam, p14561_0]
                                        · have p14561_0 := h14561c.1
                                          have p14561_1 := h14561c.2.1
                                          have p14561_2 := h14561c.2.2.1
                                          have p14561_3 := h14561c.2.2.2
                                          linarith only [h13951, h14548, h14554, hc12, hc23, hlam, hphi, p14561_1]
                                        · have p14561_0 := h14561c.1
                                          have p14561_1 := h14561c.2.1
                                          have p14561_2 := h14561c.2.2.1
                                          have p14561_3 := h14561c.2.2.2
                                          linarith only [h1, hlam, p14561_0]
                                        · have p14561_0 := h14561c.1
                                          have p14561_1 := h14561c.2.1
                                          have p14561_2 := h14561c.2.2.1
                                          have p14561_3 := h14561c.2.2.2
                                          linarith only [h13951, hlam, p14561_0]
                                        · have p14561_0 := h14561c.1
                                          have p14561_1 := h14561c.2.1
                                          have p14561_2 := h14561c.2.2.1
                                          have p14561_3 := h14561c.2.2.2
                                          linarith only [h13951, h14548, h14552, h14554, hc12, hc23, hlam, hphi, p14561_1]
                                        · have p14561_0 := h14561c.1
                                          have p14561_1 := h14561c.2.1
                                          have p14561_2 := h14561c.2.2.1
                                          have p14561_3 := h14561c.2.2.2
                                          linarith only [h0, hlam, p14561_0]
                                        · have p14561_0 := h14561c.1
                                          have p14561_1 := h14561c.2.1
                                          have p14561_2 := h14561c.2.2.1
                                          have p14561_3 := h14561c.2.2.2
                                          linarith only [hlam, p14561_0]
                                        · have p14561_0 := h14561c.1
                                          have p14561_1 := h14561c.2.1
                                          have p14561_2 := h14561c.2.2.1
                                          have p14561_3 := h14561c.2.2.2
                                          linarith only [h14548, hlam, p14561_0]
                                        · have p14561_0 := h14561c.1
                                          have p14561_1 := h14561c.2.1
                                          have p14561_2 := h14561c.2.2.1
                                          have p14561_3 := h14561c.2.2.2
                                          linarith only [h14550, hlam, p14561_0]
                                        · have p14561_0 := h14561c.1
                                          have p14561_1 := h14561c.2.1
                                          have p14561_2 := h14561c.2.2.1
                                          have p14561_3 := h14561c.2.2.2
                                          linarith only [h14552, hlam, p14561_0]
                                        · have p14561_0 := h14561c.1
                                          have p14561_1 := h14561c.2.1
                                          have p14561_2 := h14561c.2.2.1
                                          have p14561_3 := h14561c.2.2.2
                                          linarith only [h0, h14548, hc12, hc23, hlam, hphi, p14561_1]
                                        · have p14561_0 := h14561c.1
                                          have p14561_1 := h14561c.2.1
                                          have p14561_2 := h14561c.2.2.1
                                          have p14561_3 := h14561c.2.2.2
                                          rcases p14561_3 (m.d 0 1) (by simp) with h14573 | h14573
                                          · linarith only [h1, h14573, hlam]
                                          · linarith only [h0, h14573, hlam]
                                        · have p14561_0 := h14561c.1
                                          have p14561_1 := h14561c.2.1
                                          have p14561_2 := h14561c.2.2.1
                                          have p14561_3 := h14561c.2.2.2
                                          linarith only [hlam, p14561_0]
                                        · have p14561_0 := h14561c.1
                                          have p14561_1 := h14561c.2.1
                                          have p14561_2 := h14561c.2.2.1
                                          have p14561_3 := h14561c.2.2.2
                                          linarith only [h13951, h14463, h14548, h14552, hc12, hc23, hlam, hphi, p14561_1]
                                        · have p14561_0 := h14561c.1
                                          have p14561_1 := h14561c.2.1
                                          have p14561_2 := h14561c.2.2.1
                                          have p14561_3 := h14561c.2.2.2
                                          rcases p14561_3 (m.d 0 1) (by simp) with h14578 | h14578
                                          · linarith only [h1, h14578, hlam]
                                          · linarith only [h14463, h14578, hlam]
                                        · have p14561_0 := h14561c.1
                                          have p14561_1 := h14561c.2.1
                                          have p14561_2 := h14561c.2.2.1
                                          have p14561_3 := h14561c.2.2.2
                                          linarith only [h14463, h14550, h14552, hc12, hc24, hlam, hphi, p14561_1]
                                        · have p14561_0 := h14561c.1
                                          have p14561_1 := h14561c.2.1
                                          have p14561_2 := h14561c.2.2.1
                                          have p14561_3 := h14561c.2.2.2
                                          rcases p14561_3 (m.d 0 1) (by simp) with h14582 | h14582
                                          · linarith only [h13951, h14582, hlam]
                                          · linarith only [h0, h14582, hlam]
                                        · have p14561_0 := h14561c.1
                                          have p14561_1 := h14561c.2.1
                                          have p14561_2 := h14561c.2.2.1
                                          have p14561_3 := h14561c.2.2.2
                                          linarith only [h14554, hlam, p14561_0]
                                        · have p14561_0 := h14561c.1
                                          have p14561_1 := h14561c.2.1
                                          have p14561_2 := h14561c.2.2.1
                                          have p14561_3 := h14561c.2.2.2
                                          linarith only [hlam, p14561_0]
                                        · have p14561_0 := h14561c.1
                                          have p14561_1 := h14561c.2.1
                                          have p14561_2 := h14561c.2.2.1
                                          have p14561_3 := h14561c.2.2.2
                                          rcases p14561_3 (m.d 0 1) (by simp) with h14587 | h14587
                                          · linarith only [h13951, h14587, hlam]
                                          · linarith only [h14463, h14587, hlam]
                                        · have p14561_0 := h14561c.1
                                          have p14561_1 := h14561c.2.1
                                          have p14561_2 := h14561c.2.2.1
                                          have p14561_3 := h14561c.2.2.2
                                          linarith only [h14463, hlam, p14561_0]
                                        · have p14561_0 := h14561c.1
                                          have p14561_1 := h14561c.2.1
                                          have p14561_2 := h14561c.2.2.1
                                          have p14561_3 := h14561c.2.2.2
                                          linarith only [h1, h14463, h14548, hc12, hc23, hlam, hphi, p14561_1]
                                        · have p14561_0 := h14561c.1
                                          have p14561_1 := h14561c.2.1
                                          have p14561_2 := h14561c.2.2.1
                                          have p14561_3 := h14561c.2.2.2
                                          linarith only [h14555, hlam, p14561_0]
                                        · have p14561_0 := h14561c.1
                                          have p14561_1 := h14561c.2.1
                                          have p14561_2 := h14561c.2.2.1
                                          have p14561_3 := h14561c.2.2.2
                                          linarith only [h14556, hlam, p14561_0]
                                        · have p14561_0 := h14561c.1
                                          have p14561_1 := h14561c.2.1
                                          have p14561_2 := h14561c.2.2.1
                                          have p14561_3 := h14561c.2.2.2
                                          linarith only [hlam, p14561_0]
                                      · rcases h1bigk with h14595c | h14595c | h14595c | h14595c | h14595c | h14595c | h14595c | h14595c | h14595c | h14595c | h14595c | h14595c | h14595c | h14595c | h14595c | h14595c | h14595c | h14595c | h14595c | h14595c | h14595c | h14595c | h14595c | h14595c | h14595c
                                        · have p14595_0 := h14595c.1
                                          have p14595_1 := h14595c.2.1
                                          have p14595_2 := h14595c.2.2.1
                                          have p14595_3 := h14595c.2.2.2
                                          linarith only [hlam, p14595_0]
                                        · have p14595_0 := h14595c.1
                                          have p14595_1 := h14595c.2.1
                                          have p14595_2 := h14595c.2.2.1
                                          have p14595_3 := h14595c.2.2.2
                                          linarith only [h13951, h14548, h14554, hc12, hc23, hlam, hphi, p14595_1]
                                        · have p14595_0 := h14595c.1
                                          have p14595_1 := h14595c.2.1
                                          have p14595_2 := h14595c.2.2.1
                                          have p14595_3 := h14595c.2.2.2
                                          linarith only [h1, hlam, p14595_0]
                                        · have p14595_0 := h14595c.1
                                          have p14595_1 := h14595c.2.1
                                          have p14595_2 := h14595c.2.2.1
                                          have p14595_3 := h14595c.2.2.2
                                          linarith only [h13951, hlam, p14595_0]
                                        · have p14595_0 := h14595c.1
                                          have p14595_1 := h14595c.2.1
                                          have p14595_2 := h14595c.2.2.1
                                          have p14595_3 := h14595c.2.2.2
                                          linarith only [h13951, h14548, h14552, h14554, hc12, hc23, hlam, hphi, p14595_1]
                                        · have p14595_0 := h14595c.1
                                          have p14595_1 := h14595c.2.1
                                          have p14595_2 := h14595c.2.2.1
                                          have p14595_3 := h14595c.2.2.2
                                          linarith only [h0, hlam, p14595_0]
                                        · have p14595_0 := h14595c.1
                                          have p14595_1 := h14595c.2.1
                                          have p14595_2 := h14595c.2.2.1
                                          have p14595_3 := h14595c.2.2.2
                                          linarith only [hlam, p14595_0]
                                        · have p14595_0 := h14595c.1
                                          have p14595_1 := h14595c.2.1
                                          have p14595_2 := h14595c.2.2.1
                                          have p14595_3 := h14595c.2.2.2
                                          linarith only [h14548, hlam, p14595_0]
                                        · have p14595_0 := h14595c.1
                                          have p14595_1 := h14595c.2.1
                                          have p14595_2 := h14595c.2.2.1
                                          have p14595_3 := h14595c.2.2.2
                                          linarith only [h14550, hlam, p14595_0]
                                        · have p14595_0 := h14595c.1
                                          have p14595_1 := h14595c.2.1
                                          have p14595_2 := h14595c.2.2.1
                                          have p14595_3 := h14595c.2.2.2
                                          linarith only [h14552, hlam, p14595_0]
                                        · have p14595_0 := h14595c.1
                                          have p14595_1 := h14595c.2.1
                                          have p14595_2 := h14595c.2.2.1
                                          have p14595_3 := h14595c.2.2.2
                                          linarith only [h0, h14548, hc12, hc23, hlam, hphi, p14595_1]
                                        · have p14595_0 := h14595c.1
                                          have p14595_1 := h14595c.2.1
                                          have p14595_2 := h14595c.2.2.1
                                          have p14595_3 := h14595c.2.2.2
                                          rcases p14595_3 (m.d 0 1) (by simp) with h14607 | h14607
                                          · linarith only [h1, h14607, hlam]
                                          · linarith only [h0, h14607, hlam]
                                        · have p14595_0 := h14595c.1
                                          have p14595_1 := h14595c.2.1
                                          have p14595_2 := h14595c.2.2.1
                                          have p14595_3 := h14595c.2.2.2
                                          linarith only [hlam, p14595_0]
                                        · have p14595_0 := h14595c.1
                                          have p14595_1 := h14595c.2.1
                                          have p14595_2 := h14595c.2.2.1
                                          have p14595_3 := h14595c.2.2.2
                                          linarith only [h13951, h14463, h14548, h14556, h14560, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14595_1]
                                        · have p14595_0 := h14595c.1
                                          have p14595_1 := h14595c.2.1
                                          have p14595_2 := h14595c.2.2.1
                                          have p14595_3 := h14595c.2.2.2
                                          rcases p14595_3 (m.d 0 1) (by simp) with h14612 | h14612
                                          · linarith only [h1, h14612, hlam]
                                          · linarith only [h14463, h14612, hlam]
                                        · have p14595_0 := h14595c.1
                                          have p14595_1 := h14595c.2.1
                                          have p14595_2 := h14595c.2.2.1
                                          have p14595_3 := h14595c.2.2.2
                                          linarith only [h14463, h14556, h14560, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14595_1]
                                        · have p14595_0 := h14595c.1
                                          have p14595_1 := h14595c.2.1
                                          have p14595_2 := h14595c.2.2.1
                                          have p14595_3 := h14595c.2.2.2
                                          rcases p14595_3 (m.d 0 1) (by simp) with h14616 | h14616
                                          · linarith only [h13951, h14616, hlam]
                                          · linarith only [h0, h14616, hlam]
                                        · have p14595_0 := h14595c.1
                                          have p14595_1 := h14595c.2.1
                                          have p14595_2 := h14595c.2.2.1
                                          have p14595_3 := h14595c.2.2.2
                                          linarith only [h14554, hlam, p14595_0]
                                        · have p14595_0 := h14595c.1
                                          have p14595_1 := h14595c.2.1
                                          have p14595_2 := h14595c.2.2.1
                                          have p14595_3 := h14595c.2.2.2
                                          linarith only [hlam, p14595_0]
                                        · have p14595_0 := h14595c.1
                                          have p14595_1 := h14595c.2.1
                                          have p14595_2 := h14595c.2.2.1
                                          have p14595_3 := h14595c.2.2.2
                                          rcases p14595_3 (m.d 0 1) (by simp) with h14621 | h14621
                                          · linarith only [h13951, h14621, hlam]
                                          · linarith only [h14463, h14621, hlam]
                                        · have p14595_0 := h14595c.1
                                          have p14595_1 := h14595c.2.1
                                          have p14595_2 := h14595c.2.2.1
                                          have p14595_3 := h14595c.2.2.2
                                          linarith only [h14463, hlam, p14595_0]
                                        · have p14595_0 := h14595c.1
                                          have p14595_1 := h14595c.2.1
                                          have p14595_2 := h14595c.2.2.1
                                          have p14595_3 := h14595c.2.2.2
                                          linarith only [h1, h14463, h14548, hc12, hc23, hlam, hphi, p14595_1]
                                        · have p14595_0 := h14595c.1
                                          have p14595_1 := h14595c.2.1
                                          have p14595_2 := h14595c.2.2.1
                                          have p14595_3 := h14595c.2.2.2
                                          linarith only [h14555, hlam, p14595_0]
                                        · have p14595_0 := h14595c.1
                                          have p14595_1 := h14595c.2.1
                                          have p14595_2 := h14595c.2.2.1
                                          have p14595_3 := h14595c.2.2.2
                                          linarith only [h14556, hlam, p14595_0]
                                        · have p14595_0 := h14595c.1
                                          have p14595_1 := h14595c.2.1
                                          have p14595_2 := h14595c.2.2.1
                                          have p14595_3 := h14595c.2.2.2
                                          linarith only [hlam, p14595_0]
                                    · linarith only [h0, h13951, h14550, h14559, hc12, hc45, hlam, hphi, ht23, ht34]
                                  · linarith only [h1, h14463, h14548, h14552, h14558, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h1, h14463, h14548, h14552, h14557, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h13951, h14463, h14552, h14556, hc12, hc45, hlam, hphi, ht23, ht34]
                            · linarith only [h13951, h14463, h14552, h14554, h14555, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h14463, h14545, h14552, h14554, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h13951, h14463, h14547, hlam]
                · linarith only [h1, h14463, h14546, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h14637 | h14637
                · rcases m.htr 0 4 5 (by decide) (by decide) with h14638 | h14638
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h14639 | h14639
                    · linarith only [h0, h1, h14545, h14639, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h14641 | h14641
                      · linarith only [h0, h1, h14466, h14545, h14641, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h14643 | h14643
                        · linarith only [h0, h1, h14468, h14545, h14643, hc02, hc34, hlam, hphi, ht23]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h14645 | h14645
                          · linarith only [h0, h1, h14545, h14639, h14645, hc12, hc23, hlam, hphi]
                          · linarith only [h1, h14463, h14643, h14645, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h1, h14463, h14545, h14638, hlam]
                · linarith only [h1, h14463, h14637, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h14650 | h14650
        · linarith only [h0, h1, h14650, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h14652 | h14652
          · linarith only [h0, h13951, h14652, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h14654 | h14654
            · linarith only [h0, h14463, h14654, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h14656 | h14656
              · rcases m.htr 0 3 5 (by decide) (by decide) with h14657 | h14657
                · rcases m.htr 0 4 5 (by decide) (by decide) with h14658 | h14658
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h14659 | h14659
                    · linarith only [h0, h1, h14650, h14659, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h14661 | h14661
                      · linarith only [h0, h14463, h14652, h14658, h14661, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h14663 | h14663
                        · linarith only [h0, h14463, h14654, h14663, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h14665 | h14665
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h14666 | h14666
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h14667 | h14667
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h14668 | h14668
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h14669 | h14669
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h14670 | h14670
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h14671 | h14671
                                      · rcases h1bigk with h14672c | h14672c | h14672c | h14672c | h14672c | h14672c | h14672c | h14672c | h14672c | h14672c | h14672c | h14672c | h14672c | h14672c | h14672c | h14672c | h14672c | h14672c | h14672c | h14672c | h14672c | h14672c | h14672c | h14672c | h14672c
                                        · have p14672_0 := h14672c.1
                                          have p14672_1 := h14672c.2.1
                                          have p14672_2 := h14672c.2.2.1
                                          have p14672_3 := h14672c.2.2.2
                                          linarith only [hlam, p14672_0]
                                        · have p14672_0 := h14672c.1
                                          have p14672_1 := h14672c.2.1
                                          have p14672_2 := h14672c.2.2.1
                                          have p14672_3 := h14672c.2.2.2
                                          linarith only [h14463, h14659, h14665, h14667, hc12, hc23, hlam, hphi, p14672_1]
                                        · have p14672_0 := h14672c.1
                                          have p14672_1 := h14672c.2.1
                                          have p14672_2 := h14672c.2.2.1
                                          have p14672_3 := h14672c.2.2.2
                                          linarith only [h1, hlam, p14672_0]
                                        · have p14672_0 := h14672c.1
                                          have p14672_1 := h14672c.2.1
                                          have p14672_2 := h14672c.2.2.1
                                          have p14672_3 := h14672c.2.2.2
                                          linarith only [h13951, hlam, p14672_0]
                                        · have p14672_0 := h14672c.1
                                          have p14672_1 := h14672c.2.1
                                          have p14672_2 := h14672c.2.2.1
                                          have p14672_3 := h14672c.2.2.2
                                          linarith only [h14463, hlam, p14672_0]
                                        · have p14672_0 := h14672c.1
                                          have p14672_1 := h14672c.2.1
                                          have p14672_2 := h14672c.2.2.1
                                          have p14672_3 := h14672c.2.2.2
                                          linarith only [h0, hlam, p14672_0]
                                        · have p14672_0 := h14672c.1
                                          have p14672_1 := h14672c.2.1
                                          have p14672_2 := h14672c.2.2.1
                                          have p14672_3 := h14672c.2.2.2
                                          linarith only [hlam, p14672_0]
                                        · have p14672_0 := h14672c.1
                                          have p14672_1 := h14672c.2.1
                                          have p14672_2 := h14672c.2.2.1
                                          have p14672_3 := h14672c.2.2.2
                                          linarith only [h14659, hlam, p14672_0]
                                        · have p14672_0 := h14672c.1
                                          have p14672_1 := h14672c.2.1
                                          have p14672_2 := h14672c.2.2.1
                                          have p14672_3 := h14672c.2.2.2
                                          linarith only [h14661, hlam, p14672_0]
                                        · have p14672_0 := h14672c.1
                                          have p14672_1 := h14672c.2.1
                                          have p14672_2 := h14672c.2.2.1
                                          have p14672_3 := h14672c.2.2.2
                                          linarith only [h14663, hlam, p14672_0]
                                        · have p14672_0 := h14672c.1
                                          have p14672_1 := h14672c.2.1
                                          have p14672_2 := h14672c.2.2.1
                                          have p14672_3 := h14672c.2.2.2
                                          linarith only [h0, h14659, hc12, hc23, hlam, hphi, p14672_1]
                                        · have p14672_0 := h14672c.1
                                          have p14672_1 := h14672c.2.1
                                          have p14672_2 := h14672c.2.2.1
                                          have p14672_3 := h14672c.2.2.2
                                          rcases p14672_3 (m.d 0 1) (by simp) with h14684 | h14684
                                          · linarith only [h1, h14684, hlam]
                                          · linarith only [h0, h14684, hlam]
                                        · have p14672_0 := h14672c.1
                                          have p14672_1 := h14672c.2.1
                                          have p14672_2 := h14672c.2.2.1
                                          have p14672_3 := h14672c.2.2.2
                                          linarith only [hlam, p14672_0]
                                        · have p14672_0 := h14672c.1
                                          have p14672_1 := h14672c.2.1
                                          have p14672_2 := h14672c.2.2.1
                                          have p14672_3 := h14672c.2.2.2
                                          linarith only [h0, h13951, h14659, hc12, hc23, hlam, hphi, p14672_1]
                                        · have p14672_0 := h14672c.1
                                          have p14672_1 := h14672c.2.1
                                          have p14672_2 := h14672c.2.2.1
                                          have p14672_3 := h14672c.2.2.2
                                          linarith only [h0, h14463, h14659, hc12, hc23, hlam, hphi, p14672_1]
                                        · have p14672_0 := h14672c.1
                                          have p14672_1 := h14672c.2.1
                                          have p14672_2 := h14672c.2.2.1
                                          have p14672_3 := h14672c.2.2.2
                                          linarith only [h0, h14661, hc12, hc24, hlam, hphi, p14672_1]
                                        · have p14672_0 := h14672c.1
                                          have p14672_1 := h14672c.2.1
                                          have p14672_2 := h14672c.2.2.1
                                          have p14672_3 := h14672c.2.2.2
                                          rcases p14672_3 (m.d 0 1) (by simp) with h14691 | h14691
                                          · linarith only [h13951, h14691, hlam]
                                          · linarith only [h0, h14691, hlam]
                                        · have p14672_0 := h14672c.1
                                          have p14672_1 := h14672c.2.1
                                          have p14672_2 := h14672c.2.2.1
                                          have p14672_3 := h14672c.2.2.2
                                          linarith only [h14665, hlam, p14672_0]
                                        · have p14672_0 := h14672c.1
                                          have p14672_1 := h14672c.2.1
                                          have p14672_2 := h14672c.2.2.1
                                          have p14672_3 := h14672c.2.2.2
                                          linarith only [hlam, p14672_0]
                                        · have p14672_0 := h14672c.1
                                          have p14672_1 := h14672c.2.1
                                          have p14672_2 := h14672c.2.2.1
                                          have p14672_3 := h14672c.2.2.2
                                          linarith only [h0, h14463, h14659, h14665, hc12, hc23, hlam, hphi, p14672_1]
                                        · have p14672_0 := h14672c.1
                                          have p14672_1 := h14672c.2.1
                                          have p14672_2 := h14672c.2.2.1
                                          have p14672_3 := h14672c.2.2.2
                                          linarith only [h0, h14663, hc12, hc25, hlam, hphi, p14672_1]
                                        · have p14672_0 := h14672c.1
                                          have p14672_1 := h14672c.2.1
                                          have p14672_2 := h14672c.2.2.1
                                          have p14672_3 := h14672c.2.2.2
                                          rcases p14672_3 (m.d 0 1) (by simp) with h14698 | h14698
                                          · linarith only [h14463, h14698, hlam]
                                          · linarith only [h0, h14698, hlam]
                                        · have p14672_0 := h14672c.1
                                          have p14672_1 := h14672c.2.1
                                          have p14672_2 := h14672c.2.2.1
                                          have p14672_3 := h14672c.2.2.2
                                          linarith only [h14666, hlam, p14672_0]
                                        · have p14672_0 := h14672c.1
                                          have p14672_1 := h14672c.2.1
                                          have p14672_2 := h14672c.2.2.1
                                          have p14672_3 := h14672c.2.2.2
                                          linarith only [h14667, hlam, p14672_0]
                                        · have p14672_0 := h14672c.1
                                          have p14672_1 := h14672c.2.1
                                          have p14672_2 := h14672c.2.2.1
                                          have p14672_3 := h14672c.2.2.2
                                          linarith only [hlam, p14672_0]
                                      · rcases h1bigk with h14704c | h14704c | h14704c | h14704c | h14704c | h14704c | h14704c | h14704c | h14704c | h14704c | h14704c | h14704c | h14704c | h14704c | h14704c | h14704c | h14704c | h14704c | h14704c | h14704c | h14704c | h14704c | h14704c | h14704c | h14704c
                                        · have p14704_0 := h14704c.1
                                          have p14704_1 := h14704c.2.1
                                          have p14704_2 := h14704c.2.2.1
                                          have p14704_3 := h14704c.2.2.2
                                          linarith only [hlam, p14704_0]
                                        · have p14704_0 := h14704c.1
                                          have p14704_1 := h14704c.2.1
                                          have p14704_2 := h14704c.2.2.1
                                          have p14704_3 := h14704c.2.2.2
                                          linarith only [h1, h14659, hc12, hc23, hlam, hphi, p14704_1]
                                        · have p14704_0 := h14704c.1
                                          have p14704_1 := h14704c.2.1
                                          have p14704_2 := h14704c.2.2.1
                                          have p14704_3 := h14704c.2.2.2
                                          linarith only [h1, hlam, p14704_0]
                                        · have p14704_0 := h14704c.1
                                          have p14704_1 := h14704c.2.1
                                          have p14704_2 := h14704c.2.2.1
                                          have p14704_3 := h14704c.2.2.2
                                          linarith only [h13951, hlam, p14704_0]
                                        · have p14704_0 := h14704c.1
                                          have p14704_1 := h14704c.2.1
                                          have p14704_2 := h14704c.2.2.1
                                          have p14704_3 := h14704c.2.2.2
                                          linarith only [h14463, hlam, p14704_0]
                                        · have p14704_0 := h14704c.1
                                          have p14704_1 := h14704c.2.1
                                          have p14704_2 := h14704c.2.2.1
                                          have p14704_3 := h14704c.2.2.2
                                          linarith only [h0, hlam, p14704_0]
                                        · have p14704_0 := h14704c.1
                                          have p14704_1 := h14704c.2.1
                                          have p14704_2 := h14704c.2.2.1
                                          have p14704_3 := h14704c.2.2.2
                                          linarith only [hlam, p14704_0]
                                        · have p14704_0 := h14704c.1
                                          have p14704_1 := h14704c.2.1
                                          have p14704_2 := h14704c.2.2.1
                                          have p14704_3 := h14704c.2.2.2
                                          linarith only [h14659, hlam, p14704_0]
                                        · have p14704_0 := h14704c.1
                                          have p14704_1 := h14704c.2.1
                                          have p14704_2 := h14704c.2.2.1
                                          have p14704_3 := h14704c.2.2.2
                                          linarith only [h14661, hlam, p14704_0]
                                        · have p14704_0 := h14704c.1
                                          have p14704_1 := h14704c.2.1
                                          have p14704_2 := h14704c.2.2.1
                                          have p14704_3 := h14704c.2.2.2
                                          linarith only [h14663, hlam, p14704_0]
                                        · have p14704_0 := h14704c.1
                                          have p14704_1 := h14704c.2.1
                                          have p14704_2 := h14704c.2.2.1
                                          have p14704_3 := h14704c.2.2.2
                                          linarith only [h0, h14659, hc12, hc23, hlam, hphi, p14704_1]
                                        · have p14704_0 := h14704c.1
                                          have p14704_1 := h14704c.2.1
                                          have p14704_2 := h14704c.2.2.1
                                          have p14704_3 := h14704c.2.2.2
                                          rcases p14704_3 (m.d 0 1) (by simp) with h14716 | h14716
                                          · linarith only [h1, h14716, hlam]
                                          · linarith only [h0, h14716, hlam]
                                        · have p14704_0 := h14704c.1
                                          have p14704_1 := h14704c.2.1
                                          have p14704_2 := h14704c.2.2.1
                                          have p14704_3 := h14704c.2.2.2
                                          linarith only [hlam, p14704_0]
                                        · have p14704_0 := h14704c.1
                                          have p14704_1 := h14704c.2.1
                                          have p14704_2 := h14704c.2.2.1
                                          have p14704_3 := h14704c.2.2.2
                                          linarith only [h0, h13951, h14659, hc12, hc23, hlam, hphi, p14704_1]
                                        · have p14704_0 := h14704c.1
                                          have p14704_1 := h14704c.2.1
                                          have p14704_2 := h14704c.2.2.1
                                          have p14704_3 := h14704c.2.2.2
                                          linarith only [h0, h14463, h14659, hc12, hc23, hlam, hphi, p14704_1]
                                        · have p14704_0 := h14704c.1
                                          have p14704_1 := h14704c.2.1
                                          have p14704_2 := h14704c.2.2.1
                                          have p14704_3 := h14704c.2.2.2
                                          linarith only [h0, h14661, h14668, hc12, hc23, hlam, hphi, p14704_1]
                                        · have p14704_0 := h14704c.1
                                          have p14704_1 := h14704c.2.1
                                          have p14704_2 := h14704c.2.2.1
                                          have p14704_3 := h14704c.2.2.2
                                          rcases p14704_3 (m.d 0 1) (by simp) with h14723 | h14723
                                          · linarith only [h13951, h14723, hlam]
                                          · linarith only [h0, h14723, hlam]
                                        · have p14704_0 := h14704c.1
                                          have p14704_1 := h14704c.2.1
                                          have p14704_2 := h14704c.2.2.1
                                          have p14704_3 := h14704c.2.2.2
                                          linarith only [h14665, hlam, p14704_0]
                                        · have p14704_0 := h14704c.1
                                          have p14704_1 := h14704c.2.1
                                          have p14704_2 := h14704c.2.2.1
                                          have p14704_3 := h14704c.2.2.2
                                          linarith only [hlam, p14704_0]
                                        · have p14704_0 := h14704c.1
                                          have p14704_1 := h14704c.2.1
                                          have p14704_2 := h14704c.2.2.1
                                          have p14704_3 := h14704c.2.2.2
                                          linarith only [h0, h14463, h14661, h14668, hc12, hc23, hlam, hphi, p14704_1]
                                        · have p14704_0 := h14704c.1
                                          have p14704_1 := h14704c.2.1
                                          have p14704_2 := h14704c.2.2.1
                                          have p14704_3 := h14704c.2.2.2
                                          linarith only [h0, h14663, h14668, h14670, hc12, hc23, hlam, hphi, p14704_1]
                                        · have p14704_0 := h14704c.1
                                          have p14704_1 := h14704c.2.1
                                          have p14704_2 := h14704c.2.2.1
                                          have p14704_3 := h14704c.2.2.2
                                          rcases p14704_3 (m.d 0 1) (by simp) with h14730 | h14730
                                          · linarith only [h14463, h14730, hlam]
                                          · linarith only [h0, h14730, hlam]
                                        · have p14704_0 := h14704c.1
                                          have p14704_1 := h14704c.2.1
                                          have p14704_2 := h14704c.2.2.1
                                          have p14704_3 := h14704c.2.2.2
                                          linarith only [h14666, hlam, p14704_0]
                                        · have p14704_0 := h14704c.1
                                          have p14704_1 := h14704c.2.1
                                          have p14704_2 := h14704c.2.2.1
                                          have p14704_3 := h14704c.2.2.2
                                          linarith only [h14667, hlam, p14704_0]
                                        · have p14704_0 := h14704c.1
                                          have p14704_1 := h14704c.2.1
                                          have p14704_2 := h14704c.2.2.1
                                          have p14704_3 := h14704c.2.2.2
                                          linarith only [hlam, p14704_0]
                                    · linarith only [h0, h13951, h14656, h14658, h14661, h14670, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                  · linarith only [h0, h1, h14659, h14669, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h0, h1, h14659, h14668, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h0, h13951, h14656, h14658, h14667, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                            · linarith only [h1, h14657, h14666, hlam]
                          · linarith only [h1, h14656, h14665, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h14742 | h14742
                    · linarith only [h0, h13951, h14658, h14742, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h14744 | h14744
                      · linarith only [h0, h13951, h14658, h14744, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h14746 | h14746
                        · linarith only [h0, h14654, h14746, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h14748 | h14748
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h14749 | h14749
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h14750 | h14750
                              · linarith only [h0, h13951, h14658, h14742, h14748, h14750, hc12, hc23, hlam, hphi]
                              · linarith only [h0, h13951, h14750, hc12, hc45, hlam, hphi, ht23, ht34]
                            · linarith only [h0, h1, h14749, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h0, h1, h14656, h14748, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h14755 | h14755
                  · linarith only [h14656, h14657, h14755, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h14757 | h14757
                    · linarith only [h0, h1, h14657, h14757, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h14759 | h14759
                      · linarith only [h0, h13951, h14755, h14759, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h14761 | h14761
                        · linarith only [h0, h14654, h14761, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h14763 | h14763
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h14764 | h14764
                            · linarith only [h0, h1, h14657, h14757, h14764, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1, h14764, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h0, h1, h14656, h14657, h14763, hc12, hc35, hlam, hphi, ht23]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h14768 | h14768
                · rcases m.htr 0 4 5 (by decide) (by decide) with h14769 | h14769
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h14770 | h14770
                    · linarith only [h0, h1, h14656, h14770, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h14772 | h14772
                      · linarith only [h0, h14463, h14652, h14656, h14768, h14772, hc02, hc34, hlam, hphi, ht23]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h14774 | h14774
                        · linarith only [h0, h14463, h14654, h14774, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h14776 | h14776
                          · linarith only [h0, h14463, h14656, h14768, h14770, h14776, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h14776, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h14656, h14768, h14769, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h14780 | h14780
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h14781 | h14781
                    · linarith only [h0, h1, h14768, h14781, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h14783 | h14783
                      · linarith only [h0, h1, h14652, h14768, h14783, hc02, hc35, hlam, hphi, ht23]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h14785 | h14785
                        · linarith only [h0, h1, h14654, h14785, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h14787 | h14787
                          · linarith only [h0, h1, h14656, h14781, h14787, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h14787, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h14790 | h14790
                    · linarith only [h0, h1, h14768, h14790, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h14792 | h14792
                      · linarith only [h0, h13951, h14780, h14792, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h14794 | h14794
                        · linarith only [h0, h1, h14654, h14656, h14780, h14794, hc02, hc45, hlam, hphi, ht23, ht34]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h14796 | h14796
                          · linarith only [h0, h1, h14656, h14790, h14796, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h14796, hc12, hc34, hlam, hphi, ht23]

end R2N4
