import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_59S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3542000 in
set_option maxHeartbeats 3542000 in
theorem r1l7_20_11_14_M_LR_L_I_L_I_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h970 | h970
  · rcases m.htr 0 1 4 (by decide) (by decide) with h971 | h971
    · rcases m.htr 0 2 3 (by decide) (by decide) with h972 | h972
      · rcases m.htr 0 2 4 (by decide) (by decide) with h973 | h973
        · rcases m.htr 0 3 4 (by decide) (by decide) with h974 | h974
          · rcases m.htr 0 4 5 (by decide) (by decide) with h975 | h975
            · rcases m.htr 1 2 3 (by decide) (by decide) with h976 | h976
              · rcases m.htr 1 2 4 (by decide) (by decide) with h977 | h977
                · rcases m.htr 1 3 4 (by decide) (by decide) with h978 | h978
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h979 | h979
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h980 | h980
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h981 | h981
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h982 | h982
                          · linarith only [h970, h976, h980, h982, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h0, h970, h978, h979, h982, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h0, h970, h978, h979, h981, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h0, h970, h978, h980, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h987 | h987
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h988 | h988
                        · linarith only [h973, h979, h988, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h990 | h990
                          · linarith only [h977, h979, h987, h990, hlam]
                          · rcases h4bigk with h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c
                            · have p992_0 := h992c.1
                              have p992_1 := h992c.2.1
                              have p992_2 := h992c.2.2.1
                              have p992_3 := h992c.2.2.2
                              linarith only [hlam, p992_0]
                            · have p992_0 := h992c.1
                              have p992_1 := h992c.2.1
                              have p992_2 := h992c.2.2.1
                              have p992_3 := h992c.2.2.2
                              rcases p992_3 (m.d 0 4) (by simp) with h994 | h994
                              · rcases p992_3 (m.d 1 4) (by simp) with h995 | h995
                                · linarith only [h971, h995, hlam]
                                · rcases p992_3 (m.d 2 4) (by simp) with h997 | h997
                                  · linarith only [h973, h997, hlam]
                                  · rcases p992_3 (m.d 3 4) (by simp) with h999 | h999
                                    · linarith only [h974, h999, hlam]
                                    · rcases p992_3 (m.d 4 5) (by simp) with h1001 | h1001
                                      · linarith only [h1001, h975, hlam]
                                      · linarith only [h1001, h979, hlam]
                              · linarith only [h971, h994, hlam]
                            · have p992_0 := h992c.1
                              have p992_1 := h992c.2.1
                              have p992_2 := h992c.2.2.1
                              have p992_3 := h992c.2.2.2
                              rcases p992_3 (m.d 0 4) (by simp) with h1005 | h1005
                              · rcases p992_3 (m.d 1 4) (by simp) with h1006 | h1006
                                · linarith only [h1006, h971, hlam]
                                · linarith only [h1006, h977, hlam]
                              · linarith only [h1005, h973, hlam]
                            · have p992_0 := h992c.1
                              have p992_1 := h992c.2.1
                              have p992_2 := h992c.2.2.1
                              have p992_3 := h992c.2.2.2
                              rcases p992_3 (m.d 0 4) (by simp) with h1010 | h1010
                              · rcases p992_3 (m.d 1 4) (by simp) with h1011 | h1011
                                · linarith only [h1011, h971, hlam]
                                · linarith only [h1011, h978, hlam]
                              · linarith only [h1010, h974, hlam]
                            · have p992_0 := h992c.1
                              have p992_1 := h992c.2.1
                              have p992_2 := h992c.2.2.1
                              have p992_3 := h992c.2.2.2
                              linarith only [h0, h970, h974, h977, h979, h987, hc34, hlam, hphi, ht0b, ht45, ht5b, p992_1, u0elo1]
                            · have p992_0 := h992c.1
                              have p992_1 := h992c.2.1
                              have p992_2 := h992c.2.2.1
                              have p992_3 := h992c.2.2.2
                              linarith only [h971, hlam, p992_1]
                            · have p992_0 := h992c.1
                              have p992_1 := h992c.2.1
                              have p992_2 := h992c.2.2.1
                              have p992_3 := h992c.2.2.2
                              linarith only [hlam, p992_0]
                            · have p992_0 := h992c.1
                              have p992_1 := h992c.2.1
                              have p992_2 := h992c.2.2.1
                              have p992_3 := h992c.2.2.2
                              linarith only [h979, h987, hc34, hc45, hlam, hphi, p992_1]
                            · have p992_0 := h992c.1
                              have p992_1 := h992c.2.1
                              have p992_2 := h992c.2.2.1
                              have p992_3 := h992c.2.2.2
                              linarith only [h0, h970, h978, hc34, hlam, hphi, ht0b, ht45, ht5b, p992_1, u0elo1]
                            · have p992_0 := h992c.1
                              have p992_1 := h992c.2.1
                              have p992_2 := h992c.2.2.1
                              have p992_3 := h992c.2.2.2
                              linarith only [h979, hlam, p992_0]
                            · have p992_0 := h992c.1
                              have p992_1 := h992c.2.1
                              have p992_2 := h992c.2.2.1
                              have p992_3 := h992c.2.2.2
                              linarith only [h973, hlam, p992_1]
                            · have p992_0 := h992c.1
                              have p992_1 := h992c.2.1
                              have p992_2 := h992c.2.2.1
                              have p992_3 := h992c.2.2.2
                              linarith only [h977, hlam, p992_1]
                            · have p992_0 := h992c.1
                              have p992_1 := h992c.2.1
                              have p992_2 := h992c.2.2.1
                              have p992_3 := h992c.2.2.2
                              linarith only [hlam, p992_0]
                            · have p992_0 := h992c.1
                              have p992_1 := h992c.2.1
                              have p992_2 := h992c.2.2.1
                              have p992_3 := h992c.2.2.2
                              linarith only [h973, hc34, hlam, hphi, ht0b, ht45, ht5b, p992_1, u0elo1]
                            · have p992_0 := h992c.1
                              have p992_1 := h992c.2.1
                              have p992_2 := h992c.2.2.1
                              have p992_3 := h992c.2.2.2
                              linarith only [h988, hlam, p992_0]
                            · have p992_0 := h992c.1
                              have p992_1 := h992c.2.1
                              have p992_2 := h992c.2.2.1
                              have p992_3 := h992c.2.2.2
                              linarith only [h974, hlam, p992_1]
                            · have p992_0 := h992c.1
                              have p992_1 := h992c.2.1
                              have p992_2 := h992c.2.2.1
                              have p992_3 := h992c.2.2.2
                              linarith only [h978, hlam, p992_0]
                            · have p992_0 := h992c.1
                              have p992_1 := h992c.2.1
                              have p992_2 := h992c.2.2.1
                              have p992_3 := h992c.2.2.2
                              linarith only [h987, hlam, p992_0]
                            · have p992_0 := h992c.1
                              have p992_1 := h992c.2.1
                              have p992_2 := h992c.2.2.1
                              have p992_3 := h992c.2.2.2
                              linarith only [hlam, p992_0]
                            · have p992_0 := h992c.1
                              have p992_1 := h992c.2.1
                              have p992_2 := h992c.2.2.1
                              have p992_3 := h992c.2.2.2
                              linarith only [h990, hlam, p992_0]
                            · have p992_0 := h992c.1
                              have p992_1 := h992c.2.1
                              have p992_2 := h992c.2.2.1
                              have p992_3 := h992c.2.2.2
                              linarith only [h975, hlam, p992_0]
                            · have p992_0 := h992c.1
                              have p992_1 := h992c.2.1
                              have p992_2 := h992c.2.2.1
                              have p992_3 := h992c.2.2.2
                              linarith only [h0, h970, h974, h975, hc14, hlam, hphi, ht0b, ht45, ht5b, p992_1, u0elo1]
                            · have p992_0 := h992c.1
                              have p992_1 := h992c.2.1
                              have p992_2 := h992c.2.2.1
                              have p992_3 := h992c.2.2.2
                              linarith only [h0, h970, h974, h975, h987, hc34, hlam, hphi, ht0b, ht45, ht5b, p992_1, u0elo1]
                            · have p992_0 := h992c.1
                              have p992_1 := h992c.2.1
                              have p992_2 := h992c.2.2.1
                              have p992_3 := h992c.2.2.2
                              linarith only [h0, h970, h974, h975, hc34, hlam, hphi, ht0b, ht45, ht5b, p992_1, u0elo1]
                            · have p992_0 := h992c.1
                              have p992_1 := h992c.2.1
                              have p992_2 := h992c.2.2.1
                              have p992_3 := h992c.2.2.2
                              linarith only [hlam, p992_0]
                      · linarith only [h0, h970, h978, h987, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1037 | h1037
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1038 | h1038
                      · linarith only [h1038, h976, h978, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1040 | h1040
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1041 | h1041
                          · rcases h4bigk with h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [hlam, p1042_0]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h0, h1040, h970, h974, h977, hc45, hlam, hphi, ht0b, ht5b, p1042_1, u0elo1]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h0, h1040, h970, h974, hc45, hlam, hphi, ht0b, ht5b, p1042_1, u0elo1]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h0, h970, h974, h978, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1042_1, u0elo1]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              rcases p1042_3 (m.d 0 4) (by simp) with h1047 | h1047
                              · rcases p1042_3 (m.d 1 4) (by simp) with h1048 | h1048
                                · linarith only [h1048, h971, hlam]
                                · linarith only [h1037, h1048, hlam]
                              · linarith only [h1047, hlam, p1042_0]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h971, hlam, p1042_1]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [hlam, p1042_0]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h0, h1040, h971, hc45, hlam, hphi, ht0b, ht5b, p1042_1, u0elo1]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h978, hlam, p1042_1]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h0, h970, h974, h978, hc45, hlam, hphi, ht0b, ht5b, p1042_1, u0elo1]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h973, hlam, p1042_1]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h977, hlam, p1042_1]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [hlam, p1042_0]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h1038, hlam, p1042_1]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h973, hc45, hlam, hphi, ht0b, ht5b, p1042_1, u0elo1]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h974, hlam, p1042_1]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h0, h970, h974, hc14, hlam, hphi, ht0b, ht45, ht5b, p1042_1, u0elo1]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h0, h970, h974, hc24, hlam, hphi, ht0b, ht45, ht5b, p1042_1, u0elo1]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [hlam, p1042_0]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h0, h970, h974, hc45, hlam, hphi, ht0b, ht5b, p1042_1, u0elo1]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h975, hlam, p1042_0]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h1037, hlam, p1042_0]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h1040, hlam, p1042_0]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [h1041, hlam, p1042_0]
                            · have p1042_0 := h1042c.1
                              have p1042_1 := h1042c.2.1
                              have p1042_2 := h1042c.2.2.1
                              have p1042_3 := h1042c.2.2.2
                              linarith only [hlam, p1042_0]
                          · linarith only [h0, h1040, h1041, h971, h977, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h0, h1037, h1040, h970, h974, h978, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1074 | h1074
                      · linarith only [h1074, h976, h978, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1076 | h1076
                        · linarith only [h1037, h1076, h973, h978, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1078 | h1078
                          · linarith only [h0, h1037, h1078, h970, h974, h976, h978, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h0, h1078, h970, h974, h975, h976, h978, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h977, hc24, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h0, h976, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1083 | h1083
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1084 | h1084
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1085 | h1085
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1086 | h1086
                    · linarith only [h1085, h1086, h970, h975, hlam, hphi, u0ehi8, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1088 | h1088
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1089 | h1089
                        · linarith only [h0, h1084, h1085, h1089, h970, h975, hc12, hlam, hphi, ht01, u0ehi8]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1091 | h1091
                          · linarith only [h0, h1083, h1088, h1091, h970, h975, hc12, hlam, hphi, ht01, u0ehi8]
                          · rcases h4bigk with h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c
                            · have p1093_0 := h1093c.1
                              have p1093_1 := h1093c.2.1
                              have p1093_2 := h1093c.2.2.1
                              have p1093_3 := h1093c.2.2.2
                              linarith only [hlam, p1093_0]
                            · have p1093_0 := h1093c.1
                              have p1093_1 := h1093c.2.1
                              have p1093_2 := h1093c.2.2.1
                              have p1093_3 := h1093c.2.2.2
                              linarith only [h1084, h975, hc24, hc45, hlam, hphi, p1093_1]
                            · have p1093_0 := h1093c.1
                              have p1093_1 := h1093c.2.1
                              have p1093_2 := h1093c.2.2.1
                              have p1093_3 := h1093c.2.2.2
                              linarith only [h975, hc24, hc45, hlam, hphi, p1093_1]
                            · have p1093_0 := h1093c.1
                              have p1093_1 := h1093c.2.1
                              have p1093_2 := h1093c.2.2.1
                              have p1093_3 := h1093c.2.2.2
                              linarith only [h975, hc34, hc45, hlam, hphi, p1093_1]
                            · have p1093_0 := h1093c.1
                              have p1093_1 := h1093c.2.1
                              have p1093_2 := h1093c.2.2.1
                              have p1093_3 := h1093c.2.2.2
                              linarith only [h975, hlam, p1093_0]
                            · have p1093_0 := h1093c.1
                              have p1093_1 := h1093c.2.1
                              have p1093_2 := h1093c.2.2.1
                              have p1093_3 := h1093c.2.2.2
                              linarith only [h971, hlam, p1093_1]
                            · have p1093_0 := h1093c.1
                              have p1093_1 := h1093c.2.1
                              have p1093_2 := h1093c.2.2.1
                              have p1093_3 := h1093c.2.2.2
                              linarith only [hlam, p1093_0]
                            · have p1093_0 := h1093c.1
                              have p1093_1 := h1093c.2.1
                              have p1093_2 := h1093c.2.2.1
                              have p1093_3 := h1093c.2.2.2
                              linarith only [h0, h971, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1093_1]
                            · have p1093_0 := h1093c.1
                              have p1093_1 := h1093c.2.1
                              have p1093_2 := h1093c.2.2.1
                              have p1093_3 := h1093c.2.2.2
                              linarith only [h0, h1085, h970, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1093_1]
                            · have p1093_0 := h1093c.1
                              have p1093_1 := h1093c.2.1
                              have p1093_2 := h1093c.2.2.1
                              have p1093_3 := h1093c.2.2.2
                              linarith only [h1086, hlam, p1093_0]
                            · have p1093_0 := h1093c.1
                              have p1093_1 := h1093c.2.1
                              have p1093_2 := h1093c.2.2.1
                              have p1093_3 := h1093c.2.2.2
                              linarith only [h973, hlam, p1093_1]
                            · have p1093_0 := h1093c.1
                              have p1093_1 := h1093c.2.1
                              have p1093_2 := h1093c.2.2.1
                              have p1093_3 := h1093c.2.2.2
                              linarith only [h1084, hlam, p1093_1]
                            · have p1093_0 := h1093c.1
                              have p1093_1 := h1093c.2.1
                              have p1093_2 := h1093c.2.2.1
                              have p1093_3 := h1093c.2.2.2
                              linarith only [hlam, p1093_0]
                            · have p1093_0 := h1093c.1
                              have p1093_1 := h1093c.2.1
                              have p1093_2 := h1093c.2.2.1
                              have p1093_3 := h1093c.2.2.2
                              linarith only [h973, hc34, hlam, hphi, ht0b, ht45, ht5b, p1093_1, u0elo1]
                            · have p1093_0 := h1093c.1
                              have p1093_1 := h1093c.2.1
                              have p1093_2 := h1093c.2.2.1
                              have p1093_3 := h1093c.2.2.2
                              linarith only [h1089, hlam, p1093_0]
                            · have p1093_0 := h1093c.1
                              have p1093_1 := h1093c.2.1
                              have p1093_2 := h1093c.2.2.1
                              have p1093_3 := h1093c.2.2.2
                              linarith only [h974, hlam, p1093_1]
                            · have p1093_0 := h1093c.1
                              have p1093_1 := h1093c.2.1
                              have p1093_2 := h1093c.2.2.1
                              have p1093_3 := h1093c.2.2.2
                              linarith only [h1085, hlam, p1093_0]
                            · have p1093_0 := h1093c.1
                              have p1093_1 := h1093c.2.1
                              have p1093_2 := h1093c.2.2.1
                              have p1093_3 := h1093c.2.2.2
                              linarith only [h1088, hlam, p1093_0]
                            · have p1093_0 := h1093c.1
                              have p1093_1 := h1093c.2.1
                              have p1093_2 := h1093c.2.2.1
                              have p1093_3 := h1093c.2.2.2
                              linarith only [hlam, p1093_0]
                            · have p1093_0 := h1093c.1
                              have p1093_1 := h1093c.2.1
                              have p1093_2 := h1093c.2.2.1
                              have p1093_3 := h1093c.2.2.2
                              linarith only [h1091, hlam, p1093_0]
                            · have p1093_0 := h1093c.1
                              have p1093_1 := h1093c.2.1
                              have p1093_2 := h1093c.2.2.1
                              have p1093_3 := h1093c.2.2.2
                              linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1093_1, u0ehi8]
                            · have p1093_0 := h1093c.1
                              have p1093_1 := h1093c.2.1
                              have p1093_2 := h1093c.2.2.1
                              have p1093_3 := h1093c.2.2.2
                              rcases p1093_3 (m.d 0 4) (by simp) with h1115 | h1115
                              · linarith only [h1115, h975, hlam]
                              · linarith only [h1115, h971, hlam]
                            · have p1093_0 := h1093c.1
                              have p1093_1 := h1093c.2.1
                              have p1093_2 := h1093c.2.2.1
                              have p1093_3 := h1093c.2.2.2
                              rcases p1093_3 (m.d 0 4) (by simp) with h1118 | h1118
                              · linarith only [h1118, h975, hlam]
                              · linarith only [h1118, h973, hlam]
                            · have p1093_0 := h1093c.1
                              have p1093_1 := h1093c.2.1
                              have p1093_2 := h1093c.2.2.1
                              have p1093_3 := h1093c.2.2.2
                              rcases p1093_3 (m.d 0 4) (by simp) with h1121 | h1121
                              · linarith only [h1121, h975, hlam]
                              · linarith only [h1121, h974, hlam]
                            · have p1093_0 := h1093c.1
                              have p1093_1 := h1093c.2.1
                              have p1093_2 := h1093c.2.2.1
                              have p1093_3 := h1093c.2.2.2
                              linarith only [hlam, p1093_0]
                      · linarith only [h0, h1085, h1088, h970, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1126 | h1126
                    · linarith only [h1126, h975, hc14, hlam, hphi, ht01, u0ehi8]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1128 | h1128
                      · linarith only [h1083, h1085, h1128, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1130 | h1130
                        · linarith only [h1130, h975, hc24, hlam, hphi, ht01, ht12, u0ehi8]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1132 | h1132
                          · linarith only [h1132, h974, h975, hlam, hphi, u0ehi8, u0elo2]
                          · rcases h4bigk with h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c
                            · have p1134_0 := h1134c.1
                              have p1134_1 := h1134c.2.1
                              have p1134_2 := h1134c.2.2.1
                              have p1134_3 := h1134c.2.2.2
                              linarith only [hlam, p1134_0]
                            · have p1134_0 := h1134c.1
                              have p1134_1 := h1134c.2.1
                              have p1134_2 := h1134c.2.2.1
                              have p1134_3 := h1134c.2.2.2
                              linarith only [h1084, h975, hc24, hc45, hlam, hphi, p1134_1]
                            · have p1134_0 := h1134c.1
                              have p1134_1 := h1134c.2.1
                              have p1134_2 := h1134c.2.2.1
                              have p1134_3 := h1134c.2.2.2
                              linarith only [h975, hc24, hc45, hlam, hphi, p1134_1]
                            · have p1134_0 := h1134c.1
                              have p1134_1 := h1134c.2.1
                              have p1134_2 := h1134c.2.2.1
                              have p1134_3 := h1134c.2.2.2
                              linarith only [h975, hc34, hc45, hlam, hphi, p1134_1]
                            · have p1134_0 := h1134c.1
                              have p1134_1 := h1134c.2.1
                              have p1134_2 := h1134c.2.2.1
                              have p1134_3 := h1134c.2.2.2
                              linarith only [h975, hlam, p1134_0]
                            · have p1134_0 := h1134c.1
                              have p1134_1 := h1134c.2.1
                              have p1134_2 := h1134c.2.2.1
                              have p1134_3 := h1134c.2.2.2
                              linarith only [h971, hlam, p1134_1]
                            · have p1134_0 := h1134c.1
                              have p1134_1 := h1134c.2.1
                              have p1134_2 := h1134c.2.2.1
                              have p1134_3 := h1134c.2.2.2
                              linarith only [hlam, p1134_0]
                            · have p1134_0 := h1134c.1
                              have p1134_1 := h1134c.2.1
                              have p1134_2 := h1134c.2.2.1
                              have p1134_3 := h1134c.2.2.2
                              linarith only [h0, h971, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1134_1]
                            · have p1134_0 := h1134c.1
                              have p1134_1 := h1134c.2.1
                              have p1134_2 := h1134c.2.2.1
                              have p1134_3 := h1134c.2.2.2
                              linarith only [h1085, hlam, p1134_1]
                            · have p1134_0 := h1134c.1
                              have p1134_1 := h1134c.2.1
                              have p1134_2 := h1134c.2.2.1
                              have p1134_3 := h1134c.2.2.2
                              linarith only [h1126, hlam, p1134_0]
                            · have p1134_0 := h1134c.1
                              have p1134_1 := h1134c.2.1
                              have p1134_2 := h1134c.2.2.1
                              have p1134_3 := h1134c.2.2.2
                              linarith only [h973, hlam, p1134_1]
                            · have p1134_0 := h1134c.1
                              have p1134_1 := h1134c.2.1
                              have p1134_2 := h1134c.2.2.1
                              have p1134_3 := h1134c.2.2.2
                              linarith only [h1084, hlam, p1134_1]
                            · have p1134_0 := h1134c.1
                              have p1134_1 := h1134c.2.1
                              have p1134_2 := h1134c.2.2.1
                              have p1134_3 := h1134c.2.2.2
                              linarith only [hlam, p1134_0]
                            · have p1134_0 := h1134c.1
                              have p1134_1 := h1134c.2.1
                              have p1134_2 := h1134c.2.2.1
                              have p1134_3 := h1134c.2.2.2
                              linarith only [h1128, hlam, p1134_1]
                            · have p1134_0 := h1134c.1
                              have p1134_1 := h1134c.2.1
                              have p1134_2 := h1134c.2.2.1
                              have p1134_3 := h1134c.2.2.2
                              linarith only [h1130, hlam, p1134_0]
                            · have p1134_0 := h1134c.1
                              have p1134_1 := h1134c.2.1
                              have p1134_2 := h1134c.2.2.1
                              have p1134_3 := h1134c.2.2.2
                              linarith only [h974, hlam, p1134_1]
                            · have p1134_0 := h1134c.1
                              have p1134_1 := h1134c.2.1
                              have p1134_2 := h1134c.2.2.1
                              have p1134_3 := h1134c.2.2.2
                              linarith only [h0, h970, h974, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1134_1]
                            · have p1134_0 := h1134c.1
                              have p1134_1 := h1134c.2.1
                              have p1134_2 := h1134c.2.2.1
                              have p1134_3 := h1134c.2.2.2
                              linarith only [h0, h970, h974, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1134_1]
                            · have p1134_0 := h1134c.1
                              have p1134_1 := h1134c.2.1
                              have p1134_2 := h1134c.2.2.1
                              have p1134_3 := h1134c.2.2.2
                              linarith only [hlam, p1134_0]
                            · have p1134_0 := h1134c.1
                              have p1134_1 := h1134c.2.1
                              have p1134_2 := h1134c.2.2.1
                              have p1134_3 := h1134c.2.2.2
                              linarith only [h1132, hlam, p1134_0]
                            · have p1134_0 := h1134c.1
                              have p1134_1 := h1134c.2.1
                              have p1134_2 := h1134c.2.2.1
                              have p1134_3 := h1134c.2.2.2
                              linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1134_1, u0ehi8]
                            · have p1134_0 := h1134c.1
                              have p1134_1 := h1134c.2.1
                              have p1134_2 := h1134c.2.2.1
                              have p1134_3 := h1134c.2.2.2
                              rcases p1134_3 (m.d 0 4) (by simp) with h1156 | h1156
                              · linarith only [h1156, h975, hlam]
                              · linarith only [h1156, h971, hlam]
                            · have p1134_0 := h1134c.1
                              have p1134_1 := h1134c.2.1
                              have p1134_2 := h1134c.2.2.1
                              have p1134_3 := h1134c.2.2.2
                              rcases p1134_3 (m.d 0 4) (by simp) with h1159 | h1159
                              · linarith only [h1159, h975, hlam]
                              · linarith only [h1159, h973, hlam]
                            · have p1134_0 := h1134c.1
                              have p1134_1 := h1134c.2.1
                              have p1134_2 := h1134c.2.2.1
                              have p1134_3 := h1134c.2.2.2
                              linarith only [h1083, h1085, hc23, hc45, hlam, hphi, ht34, p1134_1]
                            · have p1134_0 := h1134c.1
                              have p1134_1 := h1134c.2.1
                              have p1134_2 := h1134c.2.2.1
                              have p1134_3 := h1134c.2.2.2
                              linarith only [hlam, p1134_0]
                · linarith only [h0, h1084, hc24, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h0, h1083, h970, h974, hc23, hlam, hphi, ht01, ht12, u0ehi8]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1166 | h1166
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1167 | h1167
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1168 | h1168
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1169 | h1169
                  · linarith only [h1169, h974, hc13, hlam, hphi, ht01, u0ehi7]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1171 | h1171
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1172 | h1172
                      · linarith only [h1167, h1169, h1172, h971, h974, hlam, hphi, u0ehi7, u0elo0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1174 | h1174
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1175 | h1175
                          · rcases h4bigk with h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c | h1176c
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [hlam, p1176_0]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [h1168, h1174, hc45, hlam, hphi, ht0b, ht5b, p1176_1, u0elo3]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [h1174, h971, hc45, hlam, hphi, ht0b, ht5b, p1176_1, u0elo0]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [h974, hlam, p1176_0]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              rcases p1176_3 (m.d 0 4) (by simp) with h1181 | h1181
                              · rcases p1176_3 (m.d 1 4) (by simp) with h1182 | h1182
                                · linarith only [h1182, h971, hlam]
                                · linarith only [h1171, h1182, hlam]
                              · linarith only [h1181, hlam, p1176_0]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [h971, hlam, p1176_1]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [hlam, p1176_0]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [h0, h1174, h971, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1176_1]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [h1169, hlam, p1176_1]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [h0, h971, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1176_1]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [h973, hlam, p1176_1]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [h1168, hlam, p1176_1]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [hlam, p1176_0]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [h1172, hlam, p1176_1]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [h973, hc45, hlam, hphi, ht0b, ht5b, p1176_1, u0elo1]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p1176_1, u0ehi8]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              rcases p1176_3 (m.d 0 4) (by simp) with h1197 | h1197
                              · linarith only [h1197, h974, hlam]
                              · linarith only [h1197, h971, hlam]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              rcases p1176_3 (m.d 0 4) (by simp) with h1200 | h1200
                              · linarith only [h1200, h974, hlam]
                              · linarith only [h1200, h973, hlam]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [hlam, p1176_0]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              rcases p1176_3 (m.d 0 4) (by simp) with h1204 | h1204
                              · linarith only [h1204, h974, hlam]
                              · linarith only [h1166, h1204, hlam]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [h1166, hlam, p1176_0]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [h1171, hlam, p1176_0]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [h1174, hlam, p1176_0]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [h1175, hlam, p1176_0]
                            · have p1176_0 := h1176c.1
                              have p1176_1 := h1176c.2.1
                              have p1176_2 := h1176c.2.2.1
                              have p1176_3 := h1176c.2.2.2
                              linarith only [hlam, p1176_0]
                          · linarith only [h0, h1168, h1174, h1175, h971, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h1171, h1174, h971, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1214 | h1214
                      · linarith only [h0, h1166, h1167, h1169, h1171, h1214, h971, h974, hc12, hlam, hphi, ht01, u0ehi7]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1216 | h1216
                        · linarith only [h1167, h1169, h1171, h1216, h973, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1218 | h1218
                          · rcases h4bigk with h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c
                            · have p1219_0 := h1219c.1
                              have p1219_1 := h1219c.2.1
                              have p1219_2 := h1219c.2.2.1
                              have p1219_3 := h1219c.2.2.2
                              linarith only [hlam, p1219_0]
                            · have p1219_0 := h1219c.1
                              have p1219_1 := h1219c.2.1
                              have p1219_2 := h1219c.2.2.1
                              have p1219_3 := h1219c.2.2.2
                              rcases p1219_3 (m.d 0 4) (by simp) with h1221 | h1221
                              · rcases p1219_3 (m.d 1 4) (by simp) with h1222 | h1222
                                · linarith only [h1222, h971, hlam]
                                · rcases p1219_3 (m.d 2 4) (by simp) with h1224 | h1224
                                  · linarith only [h1224, h973, hlam]
                                  · rcases p1219_3 (m.d 3 4) (by simp) with h1226 | h1226
                                    · rcases p1219_3 (m.d 4 5) (by simp) with h1227 | h1227
                                      · linarith only [h1166, h1227, hlam]
                                      · linarith only [h1171, h1227, hlam]
                                    · linarith only [h1169, h1226, hlam]
                              · linarith only [h1221, h971, hlam]
                            · have p1219_0 := h1219c.1
                              have p1219_1 := h1219c.2.1
                              have p1219_2 := h1219c.2.2.1
                              have p1219_3 := h1219c.2.2.2
                              rcases p1219_3 (m.d 0 4) (by simp) with h1232 | h1232
                              · rcases p1219_3 (m.d 1 4) (by simp) with h1233 | h1233
                                · linarith only [h1233, h971, hlam]
                                · linarith only [h1168, h1233, hlam]
                              · linarith only [h1232, h973, hlam]
                            · have p1219_0 := h1219c.1
                              have p1219_1 := h1219c.2.1
                              have p1219_2 := h1219c.2.2.1
                              have p1219_3 := h1219c.2.2.2
                              linarith only [h974, hlam, p1219_0]
                            · have p1219_0 := h1219c.1
                              have p1219_1 := h1219c.2.1
                              have p1219_2 := h1219c.2.2.1
                              have p1219_3 := h1219c.2.2.2
                              linarith only [h0, h1167, h1169, h1171, h971, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1219_1]
                            · have p1219_0 := h1219c.1
                              have p1219_1 := h1219c.2.1
                              have p1219_2 := h1219c.2.2.1
                              have p1219_3 := h1219c.2.2.2
                              linarith only [h971, hlam, p1219_1]
                            · have p1219_0 := h1219c.1
                              have p1219_1 := h1219c.2.1
                              have p1219_2 := h1219c.2.2.1
                              have p1219_3 := h1219c.2.2.2
                              linarith only [hlam, p1219_0]
                            · have p1219_0 := h1219c.1
                              have p1219_1 := h1219c.2.1
                              have p1219_2 := h1219c.2.2.1
                              have p1219_3 := h1219c.2.2.2
                              linarith only [h1171, hc24, hc45, hlam, hphi, p1219_1]
                            · have p1219_0 := h1219c.1
                              have p1219_1 := h1219c.2.1
                              have p1219_2 := h1219c.2.2.1
                              have p1219_3 := h1219c.2.2.2
                              linarith only [h1169, hlam, p1219_1]
                            · have p1219_0 := h1219c.1
                              have p1219_1 := h1219c.2.1
                              have p1219_2 := h1219c.2.2.1
                              have p1219_3 := h1219c.2.2.2
                              linarith only [h1171, hlam, p1219_0]
                            · have p1219_0 := h1219c.1
                              have p1219_1 := h1219c.2.1
                              have p1219_2 := h1219c.2.2.1
                              have p1219_3 := h1219c.2.2.2
                              linarith only [h973, hlam, p1219_1]
                            · have p1219_0 := h1219c.1
                              have p1219_1 := h1219c.2.1
                              have p1219_2 := h1219c.2.2.1
                              have p1219_3 := h1219c.2.2.2
                              linarith only [h1168, hlam, p1219_1]
                            · have p1219_0 := h1219c.1
                              have p1219_1 := h1219c.2.1
                              have p1219_2 := h1219c.2.2.1
                              have p1219_3 := h1219c.2.2.2
                              linarith only [hlam, p1219_0]
                            · have p1219_0 := h1219c.1
                              have p1219_1 := h1219c.2.1
                              have p1219_2 := h1219c.2.2.1
                              have p1219_3 := h1219c.2.2.2
                              linarith only [h1214, hlam, p1219_1]
                            · have p1219_0 := h1219c.1
                              have p1219_1 := h1219c.2.1
                              have p1219_2 := h1219c.2.2.1
                              have p1219_3 := h1219c.2.2.2
                              linarith only [h1216, hlam, p1219_0]
                            · have p1219_0 := h1219c.1
                              have p1219_1 := h1219c.2.1
                              have p1219_2 := h1219c.2.2.1
                              have p1219_3 := h1219c.2.2.2
                              linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p1219_1, u0ehi8]
                            · have p1219_0 := h1219c.1
                              have p1219_1 := h1219c.2.1
                              have p1219_2 := h1219c.2.2.1
                              have p1219_3 := h1219c.2.2.2
                              rcases p1219_3 (m.d 0 4) (by simp) with h1250 | h1250
                              · linarith only [h1250, h974, hlam]
                              · linarith only [h1250, h971, hlam]
                            · have p1219_0 := h1219c.1
                              have p1219_1 := h1219c.2.1
                              have p1219_2 := h1219c.2.2.1
                              have p1219_3 := h1219c.2.2.2
                              rcases p1219_3 (m.d 0 4) (by simp) with h1253 | h1253
                              · linarith only [h1253, h974, hlam]
                              · linarith only [h1253, h973, hlam]
                            · have p1219_0 := h1219c.1
                              have p1219_1 := h1219c.2.1
                              have p1219_2 := h1219c.2.2.1
                              have p1219_3 := h1219c.2.2.2
                              linarith only [hlam, p1219_0]
                            · have p1219_0 := h1219c.1
                              have p1219_1 := h1219c.2.1
                              have p1219_2 := h1219c.2.2.1
                              have p1219_3 := h1219c.2.2.2
                              linarith only [h1167, h1169, h1171, hc23, hc34, hlam, hphi, p1219_1]
                            · have p1219_0 := h1219c.1
                              have p1219_1 := h1219c.2.1
                              have p1219_2 := h1219c.2.2.1
                              have p1219_3 := h1219c.2.2.2
                              linarith only [h1166, hlam, p1219_0]
                            · have p1219_0 := h1219c.1
                              have p1219_1 := h1219c.2.1
                              have p1219_2 := h1219c.2.2.1
                              have p1219_3 := h1219c.2.2.2
                              linarith only [h0, h1166, h1167, h1169, h971, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1219_1]
                            · have p1219_0 := h1219c.1
                              have p1219_1 := h1219c.2.1
                              have p1219_2 := h1219c.2.2.1
                              have p1219_3 := h1219c.2.2.2
                              linarith only [h0, h1166, h1214, h971, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1219_1]
                            · have p1219_0 := h1219c.1
                              have p1219_1 := h1219c.2.1
                              have p1219_2 := h1219c.2.2.1
                              have p1219_3 := h1219c.2.2.2
                              linarith only [h1218, hlam, p1219_0]
                            · have p1219_0 := h1219c.1
                              have p1219_1 := h1219c.2.1
                              have p1219_2 := h1219c.2.2.1
                              have p1219_3 := h1219c.2.2.2
                              linarith only [hlam, p1219_0]
                          · linarith only [h0, h1166, h1218, h971, h974, hc12, hlam, hphi, ht01, u0ehi7]
                · linarith only [h0, h1168, hc24, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h0, h1167, h971, h974, hc23, hlam, hphi, ht01, ht12, u0ehi7]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1266 | h1266
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1267 | h1267
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1268 | h1268
                  · linarith only [h1268, h970, h974, hlam, hphi, u0ehi7, u0elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1270 | h1270
                    · linarith only [h1166, h1270, h974, hc14, hlam, hphi, ht01, u0ehi7]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1272 | h1272
                      · linarith only [h0, h1266, h1268, h1272, h971, h974, hc12, hlam, hphi, ht01, u0ehi7]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1274 | h1274
                        · linarith only [h0, h1166, h1267, h1274, h971, h974, hc12, hlam, hphi, ht01, u0ehi7]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1276 | h1276
                          · linarith only [h1166, h1276, h974, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                          · linarith only [h1276, h974, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                · linarith only [h0, h1267, hc24, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h0, h1266, h971, h974, hc23, hlam, hphi, ht01, ht12, u0ehi7]
        · linarith only [h0, h971, h973, hlam]
      · linarith only [h0, h970, h972, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1283 | h1283
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1284 | h1284
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1285 | h1285
          · linarith only [h1285, h970, h971, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1287 | h1287
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1288 | h1288
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1289 | h1289
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1290 | h1290
                  · linarith only [h1285, h1290, h970, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1292 | h1292
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1293 | h1293
                      · linarith only [h1288, h1290, h1293, h970, h971, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1295 | h1295
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1296 | h1296
                          · rcases h4bigk with h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c | h1297c
                            · have p1297_0 := h1297c.1
                              have p1297_1 := h1297c.2.1
                              have p1297_2 := h1297c.2.2.1
                              have p1297_3 := h1297c.2.2.2
                              linarith only [hlam, p1297_0]
                            · have p1297_0 := h1297c.1
                              have p1297_1 := h1297c.2.1
                              have p1297_2 := h1297c.2.2.1
                              have p1297_3 := h1297c.2.2.2
                              linarith only [h971, hlam, p1297_0]
                            · have p1297_0 := h1297c.1
                              have p1297_1 := h1297c.2.1
                              have p1297_2 := h1297c.2.2.1
                              have p1297_3 := h1297c.2.2.2
                              linarith only [h1284, h1295, hc45, hlam, hphi, ht0b, ht5b, p1297_1, u0elo1]
                            · have p1297_0 := h1297c.1
                              have p1297_1 := h1297c.2.1
                              have p1297_2 := h1297c.2.2.1
                              have p1297_3 := h1297c.2.2.2
                              linarith only [h1285, hlam, p1297_0]
                            · have p1297_0 := h1297c.1
                              have p1297_1 := h1297c.2.1
                              have p1297_2 := h1297c.2.2.1
                              have p1297_3 := h1297c.2.2.2
                              rcases p1297_3 (m.d 0 4) (by simp) with h1302 | h1302
                              · rcases p1297_3 (m.d 1 4) (by simp) with h1303 | h1303
                                · rcases p1297_3 (m.d 2 4) (by simp) with h1304 | h1304
                                  · linarith only [h1284, h1304, hlam]
                                  · linarith only [h1295, h1304, hlam]
                                · linarith only [h1292, h1303, hlam]
                              · linarith only [h1302, hlam, p1297_0]
                            · have p1297_0 := h1297c.1
                              have p1297_1 := h1297c.2.1
                              have p1297_2 := h1297c.2.2.1
                              have p1297_3 := h1297c.2.2.2
                              linarith only [h1290, hc34, hlam, hphi, ht01, ht12, ht23, p1297_1, u0ehi8]
                            · have p1297_0 := h1297c.1
                              have p1297_1 := h1297c.2.1
                              have p1297_2 := h1297c.2.2.1
                              have p1297_3 := h1297c.2.2.2
                              linarith only [hlam, p1297_0]
                            · have p1297_0 := h1297c.1
                              have p1297_1 := h1297c.2.1
                              have p1297_2 := h1297c.2.2.1
                              have p1297_3 := h1297c.2.2.2
                              rcases p1297_3 (m.d 0 4) (by simp) with h1311 | h1311
                              · linarith only [h1311, h971, hlam]
                              · linarith only [h1284, h1311, hlam]
                            · have p1297_0 := h1297c.1
                              have p1297_1 := h1297c.2.1
                              have p1297_2 := h1297c.2.2.1
                              have p1297_3 := h1297c.2.2.2
                              linarith only [h1290, hlam, p1297_1]
                            · have p1297_0 := h1297c.1
                              have p1297_1 := h1297c.2.1
                              have p1297_2 := h1297c.2.2.1
                              have p1297_3 := h1297c.2.2.2
                              rcases p1297_3 (m.d 0 4) (by simp) with h1315 | h1315
                              · linarith only [h1315, h971, hlam]
                              · linarith only [h1287, h1315, hlam]
                            · have p1297_0 := h1297c.1
                              have p1297_1 := h1297c.2.1
                              have p1297_2 := h1297c.2.2.1
                              have p1297_3 := h1297c.2.2.2
                              linarith only [h1284, hlam, p1297_1]
                            · have p1297_0 := h1297c.1
                              have p1297_1 := h1297c.2.1
                              have p1297_2 := h1297c.2.2.1
                              have p1297_3 := h1297c.2.2.2
                              linarith only [h1289, hlam, p1297_1]
                            · have p1297_0 := h1297c.1
                              have p1297_1 := h1297c.2.1
                              have p1297_2 := h1297c.2.2.1
                              have p1297_3 := h1297c.2.2.2
                              linarith only [hlam, p1297_0]
                            · have p1297_0 := h1297c.1
                              have p1297_1 := h1297c.2.1
                              have p1297_2 := h1297c.2.2.1
                              have p1297_3 := h1297c.2.2.2
                              linarith only [h1293, hlam, p1297_1]
                            · have p1297_0 := h1297c.1
                              have p1297_1 := h1297c.2.1
                              have p1297_2 := h1297c.2.2.1
                              have p1297_3 := h1297c.2.2.2
                              linarith only [h1284, hc45, hlam, hphi, ht0b, ht5b, p1297_1, u0elo1]
                            · have p1297_0 := h1297c.1
                              have p1297_1 := h1297c.2.1
                              have p1297_2 := h1297c.2.2.1
                              have p1297_3 := h1297c.2.2.2
                              linarith only [h970, h971, hc13, hc34, hlam, hphi, p1297_1]
                            · have p1297_0 := h1297c.1
                              have p1297_1 := h1297c.2.1
                              have p1297_2 := h1297c.2.2.1
                              have p1297_3 := h1297c.2.2.2
                              linarith only [h970, h971, hc34, hlam, hphi, ht01, ht12, ht23, p1297_1, u0ehi7]
                            · have p1297_0 := h1297c.1
                              have p1297_1 := h1297c.2.1
                              have p1297_2 := h1297c.2.2.1
                              have p1297_3 := h1297c.2.2.2
                              rcases p1297_3 (m.d 0 4) (by simp) with h1325 | h1325
                              · linarith only [h1285, h1325, hlam]
                              · linarith only [h1284, h1325, hlam]
                            · have p1297_0 := h1297c.1
                              have p1297_1 := h1297c.2.1
                              have p1297_2 := h1297c.2.2.1
                              have p1297_3 := h1297c.2.2.2
                              linarith only [hlam, p1297_0]
                            · have p1297_0 := h1297c.1
                              have p1297_1 := h1297c.2.1
                              have p1297_2 := h1297c.2.2.1
                              have p1297_3 := h1297c.2.2.2
                              rcases p1297_3 (m.d 0 4) (by simp) with h1329 | h1329
                              · linarith only [h1285, h1329, hlam]
                              · linarith only [h1287, h1329, hlam]
                            · have p1297_0 := h1297c.1
                              have p1297_1 := h1297c.2.1
                              have p1297_2 := h1297c.2.2.1
                              have p1297_3 := h1297c.2.2.2
                              linarith only [h1287, hlam, p1297_0]
                            · have p1297_0 := h1297c.1
                              have p1297_1 := h1297c.2.1
                              have p1297_2 := h1297c.2.2.1
                              have p1297_3 := h1297c.2.2.2
                              linarith only [h1292, hlam, p1297_0]
                            · have p1297_0 := h1297c.1
                              have p1297_1 := h1297c.2.1
                              have p1297_2 := h1297c.2.2.1
                              have p1297_3 := h1297c.2.2.2
                              linarith only [h1295, hlam, p1297_0]
                            · have p1297_0 := h1297c.1
                              have p1297_1 := h1297c.2.1
                              have p1297_2 := h1297c.2.2.1
                              have p1297_3 := h1297c.2.2.2
                              linarith only [h1296, hlam, p1297_0]
                            · have p1297_0 := h1297c.1
                              have p1297_1 := h1297c.2.1
                              have p1297_2 := h1297c.2.2.1
                              have p1297_3 := h1297c.2.2.2
                              linarith only [hlam, p1297_0]
                          · linarith only [h1284, h1295, h1296, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1338 | h1338
                          · rcases h4bigk with h1339c | h1339c | h1339c | h1339c | h1339c | h1339c | h1339c | h1339c | h1339c | h1339c | h1339c | h1339c | h1339c | h1339c | h1339c | h1339c | h1339c | h1339c | h1339c | h1339c | h1339c | h1339c | h1339c | h1339c | h1339c
                            · have p1339_0 := h1339c.1
                              have p1339_1 := h1339c.2.1
                              have p1339_2 := h1339c.2.2.1
                              have p1339_3 := h1339c.2.2.2
                              linarith only [hlam, p1339_0]
                            · have p1339_0 := h1339c.1
                              have p1339_1 := h1339c.2.1
                              have p1339_2 := h1339c.2.2.1
                              have p1339_3 := h1339c.2.2.2
                              linarith only [h971, hlam, p1339_0]
                            · have p1339_0 := h1339c.1
                              have p1339_1 := h1339c.2.1
                              have p1339_2 := h1339c.2.2.1
                              have p1339_3 := h1339c.2.2.2
                              rcases p1339_3 (m.d 0 4) (by simp) with h1342 | h1342
                              · rcases p1339_3 (m.d 1 4) (by simp) with h1343 | h1343
                                · rcases p1339_3 (m.d 2 4) (by simp) with h1344 | h1344
                                  · linarith only [h1284, h1344, hlam]
                                  · rcases p1339_3 (m.d 3 4) (by simp) with h1346 | h1346
                                    · rcases p1339_3 (m.d 4 5) (by simp) with h1347 | h1347
                                      · linarith only [h1287, h1347, hlam]
                                      · linarith only [h1295, h1347, hlam]
                                    · linarith only [h1293, h1346, hlam]
                                · linarith only [h1289, h1343, hlam]
                              · linarith only [h1284, h1342, hlam]
                            · have p1339_0 := h1339c.1
                              have p1339_1 := h1339c.2.1
                              have p1339_2 := h1339c.2.2.1
                              have p1339_3 := h1339c.2.2.2
                              linarith only [h1285, hlam, p1339_0]
                            · have p1339_0 := h1339c.1
                              have p1339_1 := h1339c.2.1
                              have p1339_2 := h1339c.2.2.1
                              have p1339_3 := h1339c.2.2.2
                              linarith only [h1293, h1295, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1339_1, u0elo3]
                            · have p1339_0 := h1339c.1
                              have p1339_1 := h1339c.2.1
                              have p1339_2 := h1339c.2.2.1
                              have p1339_3 := h1339c.2.2.2
                              linarith only [h1290, hc34, hlam, hphi, ht01, ht12, ht23, p1339_1, u0ehi8]
                            · have p1339_0 := h1339c.1
                              have p1339_1 := h1339c.2.1
                              have p1339_2 := h1339c.2.2.1
                              have p1339_3 := h1339c.2.2.2
                              linarith only [hlam, p1339_0]
                            · have p1339_0 := h1339c.1
                              have p1339_1 := h1339c.2.1
                              have p1339_2 := h1339c.2.2.1
                              have p1339_3 := h1339c.2.2.2
                              rcases p1339_3 (m.d 0 4) (by simp) with h1357 | h1357
                              · linarith only [h1357, h971, hlam]
                              · linarith only [h1284, h1357, hlam]
                            · have p1339_0 := h1339c.1
                              have p1339_1 := h1339c.2.1
                              have p1339_2 := h1339c.2.2.1
                              have p1339_3 := h1339c.2.2.2
                              linarith only [h1290, hlam, p1339_1]
                            · have p1339_0 := h1339c.1
                              have p1339_1 := h1339c.2.1
                              have p1339_2 := h1339c.2.2.1
                              have p1339_3 := h1339c.2.2.2
                              linarith only [h1290, h1293, h1295, hc23, hc34, hlam, hphi, p1339_1]
                            · have p1339_0 := h1339c.1
                              have p1339_1 := h1339c.2.1
                              have p1339_2 := h1339c.2.2.1
                              have p1339_3 := h1339c.2.2.2
                              linarith only [h1284, hlam, p1339_1]
                            · have p1339_0 := h1339c.1
                              have p1339_1 := h1339c.2.1
                              have p1339_2 := h1339c.2.2.1
                              have p1339_3 := h1339c.2.2.2
                              linarith only [h1289, hlam, p1339_1]
                            · have p1339_0 := h1339c.1
                              have p1339_1 := h1339c.2.1
                              have p1339_2 := h1339c.2.2.1
                              have p1339_3 := h1339c.2.2.2
                              linarith only [hlam, p1339_0]
                            · have p1339_0 := h1339c.1
                              have p1339_1 := h1339c.2.1
                              have p1339_2 := h1339c.2.2.1
                              have p1339_3 := h1339c.2.2.2
                              linarith only [h1293, hlam, p1339_1]
                            · have p1339_0 := h1339c.1
                              have p1339_1 := h1339c.2.1
                              have p1339_2 := h1339c.2.2.1
                              have p1339_3 := h1339c.2.2.2
                              linarith only [h1295, hlam, p1339_0]
                            · have p1339_0 := h1339c.1
                              have p1339_1 := h1339c.2.1
                              have p1339_2 := h1339c.2.2.1
                              have p1339_3 := h1339c.2.2.2
                              linarith only [h1287, h1293, h1295, hc23, hc34, hlam, hphi, p1339_1]
                            · have p1339_0 := h1339c.1
                              have p1339_1 := h1339c.2.1
                              have p1339_2 := h1339c.2.2.1
                              have p1339_3 := h1339c.2.2.2
                              linarith only [h971, hc01, hc34, hlam, hphi, ht12, ht23, p1339_1]
                            · have p1339_0 := h1339c.1
                              have p1339_1 := h1339c.2.1
                              have p1339_2 := h1339c.2.2.1
                              have p1339_3 := h1339c.2.2.2
                              rcases p1339_3 (m.d 0 4) (by simp) with h1369 | h1369
                              · linarith only [h1285, h1369, hlam]
                              · linarith only [h1284, h1369, hlam]
                            · have p1339_0 := h1339c.1
                              have p1339_1 := h1339c.2.1
                              have p1339_2 := h1339c.2.2.1
                              have p1339_3 := h1339c.2.2.2
                              linarith only [hlam, p1339_0]
                            · have p1339_0 := h1339c.1
                              have p1339_1 := h1339c.2.1
                              have p1339_2 := h1339c.2.2.1
                              have p1339_3 := h1339c.2.2.2
                              linarith only [h1293, h1295, hc23, hc34, hlam, hphi, p1339_1]
                            · have p1339_0 := h1339c.1
                              have p1339_1 := h1339c.2.1
                              have p1339_2 := h1339c.2.2.1
                              have p1339_3 := h1339c.2.2.2
                              linarith only [h1287, hlam, p1339_0]
                            · have p1339_0 := h1339c.1
                              have p1339_1 := h1339c.2.1
                              have p1339_2 := h1339c.2.2.1
                              have p1339_3 := h1339c.2.2.2
                              linarith only [h1292, hlam, p1339_0]
                            · have p1339_0 := h1339c.1
                              have p1339_1 := h1339c.2.1
                              have p1339_2 := h1339c.2.2.1
                              have p1339_3 := h1339c.2.2.2
                              linarith only [h1287, h1293, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1339_1, u0elo3]
                            · have p1339_0 := h1339c.1
                              have p1339_1 := h1339c.2.1
                              have p1339_2 := h1339c.2.2.1
                              have p1339_3 := h1339c.2.2.2
                              linarith only [h1338, hlam, p1339_0]
                            · have p1339_0 := h1339c.1
                              have p1339_1 := h1339c.2.1
                              have p1339_2 := h1339c.2.2.1
                              have p1339_3 := h1339c.2.2.2
                              linarith only [hlam, p1339_0]
                          · linarith only [h1284, h1285, h1287, h1338, hlam, hphi, u0ehi7, u0elo1]
                    · linarith only [h1284, h1287, h1292, h970, h971, hlam, hphi, u0ehi7, u0elo1]
                · linarith only [h0, h1289, h970, hc24, hlam, hphi, ht01, ht12, u0ehi7]
              · linarith only [h0, h1288, h970, hc23, hlam, hphi, ht01, ht12, u0ehi7]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1383 | h1383
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1384 | h1384
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1385 | h1385
                  · linarith only [h1287, h1385, h970, h971, hc34, hc45, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1387 | h1387
                    · linarith only [h1287, h1385, h1387, h970, h971, hc13, hc34, hlam, hphi]
                    · linarith only [h1387, h970, h971, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                · linarith only [h0, h1284, h1384, h970, hlam, hphi, u0ehi7, u0elo1]
              · linarith only [h0, h1383, h970, hc23, hlam, hphi, ht01, ht12, u0ehi7]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1392 | h1392
          · linarith only [h0, h1284, h1392, h970, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1394 | h1394
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1395 | h1395
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1396 | h1396
                · linarith only [h0, h1284, h1396, h970, hc12, hlam, hphi, ht01, u0ehi7]
                · linarith only [h0, h1396, h970, hc24, hlam, hphi, ht01, ht12, u0ehi7]
              · linarith only [h0, h1395, h970, hc23, hlam, hphi, ht01, ht12, u0ehi7]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1400 | h1400
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1401 | h1401
                · linarith only [h0, h1284, h1401, h970, hc12, hlam, hphi, ht01, u0ehi7]
                · linarith only [h0, h1401, h970, hc24, hlam, hphi, ht01, ht12, u0ehi7]
              · linarith only [h0, h1400, h970, hc23, hlam, hphi, ht01, ht12, u0ehi7]
      · linarith only [h0, h1283, h970, hlam]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1406 | h1406
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1407 | h1407
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1408 | h1408
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1409 | h1409
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1410 | h1410
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1411 | h1411
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1412 | h1412
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1413 | h1413
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1414 | h1414
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1415 | h1415
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1416 | h1416
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1417 | h1417
                          · linarith only [h1407, h1415, h1417, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                          · linarith only [h1406, h1407, h1414, h1417, h970, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h1406, h1407, h1414, h1416, h970, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1421 | h1421
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1422 | h1422
                          · rcases h4bigk with h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c | h1423c
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [hlam, p1423_0]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h1406, h1407, h1413, h1415, h970, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1423_1, u0elo1]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h1406, h1407, h1421, h970, hc45, hlam, hphi, ht0b, ht5b, p1423_1, u0elo1]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h1406, h1407, h1415, h970, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1423_1, u0elo1]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              rcases p1423_3 (m.d 0 4) (by simp) with h1428 | h1428
                              · rcases p1423_3 (m.d 1 4) (by simp) with h1429 | h1429
                                · linarith only [h1406, h1429, hlam]
                                · linarith only [h1414, h1429, hlam]
                              · linarith only [h1428, hlam, p1423_0]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h1406, hlam, p1423_1]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [hlam, p1423_0]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h1406, h1407, h1421, h970, hc45, hlam, hphi, ht0b, ht5b, p1423_1, u0elo1]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h1406, h1407, h1415, h970, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1423_1, u0elo1]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h1406, h1407, h970, hc45, hlam, hphi, ht0b, ht5b, p1423_1, u0elo1]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h1408, hlam, p1423_1]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h1412, hlam, p1423_1]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [hlam, p1423_0]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h1415, hlam, p1423_1]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h1408, hc45, hlam, hphi, ht0b, ht5b, p1423_1, u0elo1]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h1409, hlam, p1423_1]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h1413, hlam, p1423_0]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h1407, h1409, hc24, hlam, hphi, ht0b, ht45, ht5b, p1423_1, u0elo1]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [hlam, p1423_0]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h1406, h1407, h1413, h970, hc45, hlam, hphi, ht0b, ht5b, p1423_1, u0elo1]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h1410, hlam, p1423_0]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h1414, hlam, p1423_0]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h1421, hlam, p1423_0]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [h1422, hlam, p1423_0]
                            · have p1423_0 := h1423c.1
                              have p1423_1 := h1423c.2.1
                              have p1423_2 := h1423c.2.2.1
                              have p1423_3 := h1423c.2.2.2
                              linarith only [hlam, p1423_0]
                          · linarith only [h1408, h1421, h1422, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h1406, h1407, h1414, h1421, h970, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1455 | h1455
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1456 | h1456
                        · linarith only [h1408, h1414, h1456, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1458 | h1458
                          · linarith only [h1412, h1414, h1455, h1458, hlam]
                          · rcases h4bigk with h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c | h1460c
                            · have p1460_0 := h1460c.1
                              have p1460_1 := h1460c.2.1
                              have p1460_2 := h1460c.2.2.1
                              have p1460_3 := h1460c.2.2.2
                              linarith only [hlam, p1460_0]
                            · have p1460_0 := h1460c.1
                              have p1460_1 := h1460c.2.1
                              have p1460_2 := h1460c.2.2.1
                              have p1460_3 := h1460c.2.2.2
                              rcases p1460_3 (m.d 0 4) (by simp) with h1462 | h1462
                              · rcases p1460_3 (m.d 1 4) (by simp) with h1463 | h1463
                                · linarith only [h1406, h1463, hlam]
                                · rcases p1460_3 (m.d 2 4) (by simp) with h1465 | h1465
                                  · linarith only [h1408, h1465, hlam]
                                  · rcases p1460_3 (m.d 3 4) (by simp) with h1467 | h1467
                                    · linarith only [h1409, h1467, hlam]
                                    · rcases p1460_3 (m.d 4 5) (by simp) with h1469 | h1469
                                      · linarith only [h1410, h1469, hlam]
                                      · linarith only [h1414, h1469, hlam]
                              · linarith only [h1406, h1462, hlam]
                            · have p1460_0 := h1460c.1
                              have p1460_1 := h1460c.2.1
                              have p1460_2 := h1460c.2.2.1
                              have p1460_3 := h1460c.2.2.2
                              rcases p1460_3 (m.d 0 4) (by simp) with h1473 | h1473
                              · rcases p1460_3 (m.d 1 4) (by simp) with h1474 | h1474
                                · linarith only [h1406, h1474, hlam]
                                · linarith only [h1412, h1474, hlam]
                              · linarith only [h1408, h1473, hlam]
                            · have p1460_0 := h1460c.1
                              have p1460_1 := h1460c.2.1
                              have p1460_2 := h1460c.2.2.1
                              have p1460_3 := h1460c.2.2.2
                              rcases p1460_3 (m.d 0 4) (by simp) with h1478 | h1478
                              · rcases p1460_3 (m.d 1 4) (by simp) with h1479 | h1479
                                · linarith only [h1406, h1479, hlam]
                                · linarith only [h1413, h1479, hlam]
                              · linarith only [h1409, h1478, hlam]
                            · have p1460_0 := h1460c.1
                              have p1460_1 := h1460c.2.1
                              have p1460_2 := h1460c.2.2.1
                              have p1460_3 := h1460c.2.2.2
                              linarith only [h1406, h1407, h1412, h1414, h1455, h970, hc34, hlam, hphi, ht0b, ht45, ht5b, p1460_1, u0elo1]
                            · have p1460_0 := h1460c.1
                              have p1460_1 := h1460c.2.1
                              have p1460_2 := h1460c.2.2.1
                              have p1460_3 := h1460c.2.2.2
                              linarith only [h1406, hlam, p1460_1]
                            · have p1460_0 := h1460c.1
                              have p1460_1 := h1460c.2.1
                              have p1460_2 := h1460c.2.2.1
                              have p1460_3 := h1460c.2.2.2
                              linarith only [hlam, p1460_0]
                            · have p1460_0 := h1460c.1
                              have p1460_1 := h1460c.2.1
                              have p1460_2 := h1460c.2.2.1
                              have p1460_3 := h1460c.2.2.2
                              linarith only [h1414, h1455, hc34, hc45, hlam, hphi, p1460_1]
                            · have p1460_0 := h1460c.1
                              have p1460_1 := h1460c.2.1
                              have p1460_2 := h1460c.2.2.1
                              have p1460_3 := h1460c.2.2.2
                              linarith only [h1406, h1407, h970, hc34, hlam, hphi, ht0b, ht45, ht5b, p1460_1, u0elo1]
                            · have p1460_0 := h1460c.1
                              have p1460_1 := h1460c.2.1
                              have p1460_2 := h1460c.2.2.1
                              have p1460_3 := h1460c.2.2.2
                              linarith only [h1414, hlam, p1460_0]
                            · have p1460_0 := h1460c.1
                              have p1460_1 := h1460c.2.1
                              have p1460_2 := h1460c.2.2.1
                              have p1460_3 := h1460c.2.2.2
                              linarith only [h1408, hlam, p1460_1]
                            · have p1460_0 := h1460c.1
                              have p1460_1 := h1460c.2.1
                              have p1460_2 := h1460c.2.2.1
                              have p1460_3 := h1460c.2.2.2
                              linarith only [h1412, hlam, p1460_1]
                            · have p1460_0 := h1460c.1
                              have p1460_1 := h1460c.2.1
                              have p1460_2 := h1460c.2.2.1
                              have p1460_3 := h1460c.2.2.2
                              linarith only [hlam, p1460_0]
                            · have p1460_0 := h1460c.1
                              have p1460_1 := h1460c.2.1
                              have p1460_2 := h1460c.2.2.1
                              have p1460_3 := h1460c.2.2.2
                              linarith only [h1408, hc34, hlam, hphi, ht0b, ht45, ht5b, p1460_1, u0elo1]
                            · have p1460_0 := h1460c.1
                              have p1460_1 := h1460c.2.1
                              have p1460_2 := h1460c.2.2.1
                              have p1460_3 := h1460c.2.2.2
                              linarith only [h1456, hlam, p1460_0]
                            · have p1460_0 := h1460c.1
                              have p1460_1 := h1460c.2.1
                              have p1460_2 := h1460c.2.2.1
                              have p1460_3 := h1460c.2.2.2
                              linarith only [h1409, hlam, p1460_1]
                            · have p1460_0 := h1460c.1
                              have p1460_1 := h1460c.2.1
                              have p1460_2 := h1460c.2.2.1
                              have p1460_3 := h1460c.2.2.2
                              linarith only [h1413, hlam, p1460_0]
                            · have p1460_0 := h1460c.1
                              have p1460_1 := h1460c.2.1
                              have p1460_2 := h1460c.2.2.1
                              have p1460_3 := h1460c.2.2.2
                              linarith only [h1455, hlam, p1460_0]
                            · have p1460_0 := h1460c.1
                              have p1460_1 := h1460c.2.1
                              have p1460_2 := h1460c.2.2.1
                              have p1460_3 := h1460c.2.2.2
                              linarith only [hlam, p1460_0]
                            · have p1460_0 := h1460c.1
                              have p1460_1 := h1460c.2.1
                              have p1460_2 := h1460c.2.2.1
                              have p1460_3 := h1460c.2.2.2
                              linarith only [h1458, hlam, p1460_0]
                            · have p1460_0 := h1460c.1
                              have p1460_1 := h1460c.2.1
                              have p1460_2 := h1460c.2.2.1
                              have p1460_3 := h1460c.2.2.2
                              linarith only [h1410, hlam, p1460_0]
                            · have p1460_0 := h1460c.1
                              have p1460_1 := h1460c.2.1
                              have p1460_2 := h1460c.2.2.1
                              have p1460_3 := h1460c.2.2.2
                              linarith only [h1406, h1407, h1410, h970, hc14, hlam, hphi, ht0b, ht45, ht5b, p1460_1, u0elo1]
                            · have p1460_0 := h1460c.1
                              have p1460_1 := h1460c.2.1
                              have p1460_2 := h1460c.2.2.1
                              have p1460_3 := h1460c.2.2.2
                              linarith only [h1406, h1407, h1410, h1455, h970, hc34, hlam, hphi, ht0b, ht45, ht5b, p1460_1, u0elo1]
                            · have p1460_0 := h1460c.1
                              have p1460_1 := h1460c.2.1
                              have p1460_2 := h1460c.2.2.1
                              have p1460_3 := h1460c.2.2.2
                              linarith only [h1406, h1407, h1410, h970, hc34, hlam, hphi, ht0b, ht45, ht5b, p1460_1, u0elo1]
                            · have p1460_0 := h1460c.1
                              have p1460_1 := h1460c.2.1
                              have p1460_2 := h1460c.2.2.1
                              have p1460_3 := h1460c.2.2.2
                              linarith only [hlam, p1460_0]
                      · linarith only [h1406, h1407, h1410, h1413, h1414, h1455, h970, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h1413, h970, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                · linarith only [h1406, h1410, h1411, h1412, h970, hc24, hlam, hphi, ht01, ht12, u0ehi9]
              · linarith only [h0, h1406, h1410, h1411, hc23, hlam, hphi, ht01, ht12, u0ehi9]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1508 | h1508
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1509 | h1509
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1510 | h1510
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1511 | h1511
                    · linarith only [h1406, h1410, h1511, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1513 | h1513
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1514 | h1514
                        · linarith only [h1406, h1407, h1410, h1509, h1514, h970, hlam, hphi, u0ehi8, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1516 | h1516
                          · linarith only [h1407, h1410, h1513, h1516, hlam, hphi, u0ehi8, u0elo1]
                          · rcases h4bigk with h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c | h1518c
                            · have p1518_0 := h1518c.1
                              have p1518_1 := h1518c.2.1
                              have p1518_2 := h1518c.2.2.1
                              have p1518_3 := h1518c.2.2.2
                              linarith only [hlam, p1518_0]
                            · have p1518_0 := h1518c.1
                              have p1518_1 := h1518c.2.1
                              have p1518_2 := h1518c.2.2.1
                              have p1518_3 := h1518c.2.2.2
                              linarith only [h1410, hc14, hc45, hlam, hphi, p1518_1]
                            · have p1518_0 := h1518c.1
                              have p1518_1 := h1518c.2.1
                              have p1518_2 := h1518c.2.2.1
                              have p1518_3 := h1518c.2.2.2
                              linarith only [h1410, hc24, hc45, hlam, hphi, p1518_1]
                            · have p1518_0 := h1518c.1
                              have p1518_1 := h1518c.2.1
                              have p1518_2 := h1518c.2.2.1
                              have p1518_3 := h1518c.2.2.2
                              linarith only [h1410, hc34, hc45, hlam, hphi, p1518_1]
                            · have p1518_0 := h1518c.1
                              have p1518_1 := h1518c.2.1
                              have p1518_2 := h1518c.2.2.1
                              have p1518_3 := h1518c.2.2.2
                              linarith only [h1410, hlam, p1518_0]
                            · have p1518_0 := h1518c.1
                              have p1518_1 := h1518c.2.1
                              have p1518_2 := h1518c.2.2.1
                              have p1518_3 := h1518c.2.2.2
                              linarith only [h1406, hlam, p1518_1]
                            · have p1518_0 := h1518c.1
                              have p1518_1 := h1518c.2.1
                              have p1518_2 := h1518c.2.2.1
                              have p1518_3 := h1518c.2.2.2
                              linarith only [hlam, p1518_0]
                            · have p1518_0 := h1518c.1
                              have p1518_1 := h1518c.2.1
                              have p1518_2 := h1518c.2.2.1
                              have p1518_3 := h1518c.2.2.2
                              linarith only [h1406, h1407, h970, hc24, hlam, hphi, ht0b, ht45, ht5b, p1518_1, u0elo1]
                            · have p1518_0 := h1518c.1
                              have p1518_1 := h1518c.2.1
                              have p1518_2 := h1518c.2.2.1
                              have p1518_3 := h1518c.2.2.2
                              linarith only [h1406, h1407, h970, hc34, hlam, hphi, ht0b, ht45, ht5b, p1518_1, u0elo1]
                            · have p1518_0 := h1518c.1
                              have p1518_1 := h1518c.2.1
                              have p1518_2 := h1518c.2.2.1
                              have p1518_3 := h1518c.2.2.2
                              linarith only [h1511, hlam, p1518_0]
                            · have p1518_0 := h1518c.1
                              have p1518_1 := h1518c.2.1
                              have p1518_2 := h1518c.2.2.1
                              have p1518_3 := h1518c.2.2.2
                              linarith only [h1408, hlam, p1518_1]
                            · have p1518_0 := h1518c.1
                              have p1518_1 := h1518c.2.1
                              have p1518_2 := h1518c.2.2.1
                              have p1518_3 := h1518c.2.2.2
                              linarith only [h1509, hlam, p1518_1]
                            · have p1518_0 := h1518c.1
                              have p1518_1 := h1518c.2.1
                              have p1518_2 := h1518c.2.2.1
                              have p1518_3 := h1518c.2.2.2
                              linarith only [hlam, p1518_0]
                            · have p1518_0 := h1518c.1
                              have p1518_1 := h1518c.2.1
                              have p1518_2 := h1518c.2.2.1
                              have p1518_3 := h1518c.2.2.2
                              linarith only [h1408, hc34, hlam, hphi, ht0b, ht45, ht5b, p1518_1, u0elo1]
                            · have p1518_0 := h1518c.1
                              have p1518_1 := h1518c.2.1
                              have p1518_2 := h1518c.2.2.1
                              have p1518_3 := h1518c.2.2.2
                              linarith only [h1514, hlam, p1518_0]
                            · have p1518_0 := h1518c.1
                              have p1518_1 := h1518c.2.1
                              have p1518_2 := h1518c.2.2.1
                              have p1518_3 := h1518c.2.2.2
                              linarith only [h1409, hlam, p1518_1]
                            · have p1518_0 := h1518c.1
                              have p1518_1 := h1518c.2.1
                              have p1518_2 := h1518c.2.2.1
                              have p1518_3 := h1518c.2.2.2
                              linarith only [h1510, hlam, p1518_0]
                            · have p1518_0 := h1518c.1
                              have p1518_1 := h1518c.2.1
                              have p1518_2 := h1518c.2.2.1
                              have p1518_3 := h1518c.2.2.2
                              linarith only [h1513, hlam, p1518_0]
                            · have p1518_0 := h1518c.1
                              have p1518_1 := h1518c.2.1
                              have p1518_2 := h1518c.2.2.1
                              have p1518_3 := h1518c.2.2.2
                              linarith only [hlam, p1518_0]
                            · have p1518_0 := h1518c.1
                              have p1518_1 := h1518c.2.1
                              have p1518_2 := h1518c.2.2.1
                              have p1518_3 := h1518c.2.2.2
                              linarith only [h1516, hlam, p1518_0]
                            · have p1518_0 := h1518c.1
                              have p1518_1 := h1518c.2.1
                              have p1518_2 := h1518c.2.2.1
                              have p1518_3 := h1518c.2.2.2
                              linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1518_1, u0ehi8]
                            · have p1518_0 := h1518c.1
                              have p1518_1 := h1518c.2.1
                              have p1518_2 := h1518c.2.2.1
                              have p1518_3 := h1518c.2.2.2
                              rcases p1518_3 (m.d 0 4) (by simp) with h1540 | h1540
                              · linarith only [h1410, h1540, hlam]
                              · linarith only [h1406, h1540, hlam]
                            · have p1518_0 := h1518c.1
                              have p1518_1 := h1518c.2.1
                              have p1518_2 := h1518c.2.2.1
                              have p1518_3 := h1518c.2.2.2
                              rcases p1518_3 (m.d 0 4) (by simp) with h1543 | h1543
                              · linarith only [h1410, h1543, hlam]
                              · linarith only [h1408, h1543, hlam]
                            · have p1518_0 := h1518c.1
                              have p1518_1 := h1518c.2.1
                              have p1518_2 := h1518c.2.2.1
                              have p1518_3 := h1518c.2.2.2
                              rcases p1518_3 (m.d 0 4) (by simp) with h1546 | h1546
                              · linarith only [h1410, h1546, hlam]
                              · linarith only [h1409, h1546, hlam]
                            · have p1518_0 := h1518c.1
                              have p1518_1 := h1518c.2.1
                              have p1518_2 := h1518c.2.2.1
                              have p1518_3 := h1518c.2.2.2
                              linarith only [hlam, p1518_0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1550 | h1550
                        · linarith only [h1406, h1407, h1410, h1510, h1513, h1550, h970, hlam, hphi, u0ehi8, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1552 | h1552
                          · linarith only [h1406, h1407, h1410, h1510, h1552, h970, hlam, hphi, u0ehi8, u0elo1]
                          · rcases h4bigk with h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c | h1554c
                            · have p1554_0 := h1554c.1
                              have p1554_1 := h1554c.2.1
                              have p1554_2 := h1554c.2.2.1
                              have p1554_3 := h1554c.2.2.2
                              linarith only [hlam, p1554_0]
                            · have p1554_0 := h1554c.1
                              have p1554_1 := h1554c.2.1
                              have p1554_2 := h1554c.2.2.1
                              have p1554_3 := h1554c.2.2.2
                              linarith only [h1510, h1513, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1554_1, u0elo3]
                            · have p1554_0 := h1554c.1
                              have p1554_1 := h1554c.2.1
                              have p1554_2 := h1554c.2.2.1
                              have p1554_3 := h1554c.2.2.2
                              linarith only [h1410, hc24, hc45, hlam, hphi, p1554_1]
                            · have p1554_0 := h1554c.1
                              have p1554_1 := h1554c.2.1
                              have p1554_2 := h1554c.2.2.1
                              have p1554_3 := h1554c.2.2.2
                              linarith only [h1410, h1513, hc23, hc45, hlam, hphi, ht34, p1554_1]
                            · have p1554_0 := h1554c.1
                              have p1554_1 := h1554c.2.1
                              have p1554_2 := h1554c.2.2.1
                              have p1554_3 := h1554c.2.2.2
                              linarith only [h1410, hlam, p1554_0]
                            · have p1554_0 := h1554c.1
                              have p1554_1 := h1554c.2.1
                              have p1554_2 := h1554c.2.2.1
                              have p1554_3 := h1554c.2.2.2
                              linarith only [h1406, hlam, p1554_1]
                            · have p1554_0 := h1554c.1
                              have p1554_1 := h1554c.2.1
                              have p1554_2 := h1554c.2.2.1
                              have p1554_3 := h1554c.2.2.2
                              linarith only [hlam, p1554_0]
                            · have p1554_0 := h1554c.1
                              have p1554_1 := h1554c.2.1
                              have p1554_2 := h1554c.2.2.1
                              have p1554_3 := h1554c.2.2.2
                              linarith only [h1406, hc24, hlam, hphi, ht0b, ht45, ht5b, p1554_1, u0elo0]
                            · have p1554_0 := h1554c.1
                              have p1554_1 := h1554c.2.1
                              have p1554_2 := h1554c.2.2.1
                              have p1554_3 := h1554c.2.2.2
                              linarith only [h1406, h1407, h1513, h970, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1554_1, u0elo1]
                            · have p1554_0 := h1554c.1
                              have p1554_1 := h1554c.2.1
                              have p1554_2 := h1554c.2.2.1
                              have p1554_3 := h1554c.2.2.2
                              linarith only [h1511, hlam, p1554_0]
                            · have p1554_0 := h1554c.1
                              have p1554_1 := h1554c.2.1
                              have p1554_2 := h1554c.2.2.1
                              have p1554_3 := h1554c.2.2.2
                              linarith only [h1408, hlam, p1554_1]
                            · have p1554_0 := h1554c.1
                              have p1554_1 := h1554c.2.1
                              have p1554_2 := h1554c.2.2.1
                              have p1554_3 := h1554c.2.2.2
                              linarith only [h1509, hlam, p1554_1]
                            · have p1554_0 := h1554c.1
                              have p1554_1 := h1554c.2.1
                              have p1554_2 := h1554c.2.2.1
                              have p1554_3 := h1554c.2.2.2
                              linarith only [hlam, p1554_0]
                            · have p1554_0 := h1554c.1
                              have p1554_1 := h1554c.2.1
                              have p1554_2 := h1554c.2.2.1
                              have p1554_3 := h1554c.2.2.2
                              linarith only [h1513, hlam, p1554_1]
                            · have p1554_0 := h1554c.1
                              have p1554_1 := h1554c.2.1
                              have p1554_2 := h1554c.2.2.1
                              have p1554_3 := h1554c.2.2.2
                              linarith only [h1550, hlam, p1554_0]
                            · have p1554_0 := h1554c.1
                              have p1554_1 := h1554c.2.1
                              have p1554_2 := h1554c.2.2.1
                              have p1554_3 := h1554c.2.2.2
                              linarith only [h1409, hlam, p1554_1]
                            · have p1554_0 := h1554c.1
                              have p1554_1 := h1554c.2.1
                              have p1554_2 := h1554c.2.2.1
                              have p1554_3 := h1554c.2.2.2
                              linarith only [h1510, hlam, p1554_0]
                            · have p1554_0 := h1554c.1
                              have p1554_1 := h1554c.2.1
                              have p1554_2 := h1554c.2.2.1
                              have p1554_3 := h1554c.2.2.2
                              linarith only [h1407, h1409, hc24, hlam, hphi, ht0b, ht45, ht5b, p1554_1, u0elo1]
                            · have p1554_0 := h1554c.1
                              have p1554_1 := h1554c.2.1
                              have p1554_2 := h1554c.2.2.1
                              have p1554_3 := h1554c.2.2.2
                              linarith only [hlam, p1554_0]
                            · have p1554_0 := h1554c.1
                              have p1554_1 := h1554c.2.1
                              have p1554_2 := h1554c.2.2.1
                              have p1554_3 := h1554c.2.2.2
                              linarith only [h1552, hlam, p1554_0]
                            · have p1554_0 := h1554c.1
                              have p1554_1 := h1554c.2.1
                              have p1554_2 := h1554c.2.2.1
                              have p1554_3 := h1554c.2.2.2
                              linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1554_1, u0ehi8]
                            · have p1554_0 := h1554c.1
                              have p1554_1 := h1554c.2.1
                              have p1554_2 := h1554c.2.2.1
                              have p1554_3 := h1554c.2.2.2
                              linarith only [h1510, h1513, hc23, hc45, hlam, hphi, ht34, p1554_1]
                            · have p1554_0 := h1554c.1
                              have p1554_1 := h1554c.2.1
                              have p1554_2 := h1554c.2.2.1
                              have p1554_3 := h1554c.2.2.2
                              rcases p1554_3 (m.d 0 4) (by simp) with h1577 | h1577
                              · linarith only [h1410, h1577, hlam]
                              · linarith only [h1408, h1577, hlam]
                            · have p1554_0 := h1554c.1
                              have p1554_1 := h1554c.2.1
                              have p1554_2 := h1554c.2.2.1
                              have p1554_3 := h1554c.2.2.2
                              linarith only [h1513, hc23, hc45, hlam, hphi, ht34, p1554_1]
                            · have p1554_0 := h1554c.1
                              have p1554_1 := h1554c.2.1
                              have p1554_2 := h1554c.2.2.1
                              have p1554_3 := h1554c.2.2.2
                              linarith only [hlam, p1554_0]
                  · linarith only [h1510, h970, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                · linarith only [h1406, h1508, h1509, h970, hc24, hlam, hphi, ht01, ht12, u0ehi8]
              · linarith only [h0, h1406, h1508, hc23, hlam, hphi, ht01, ht12, u0ehi8]
          · linarith only [h1406, h1409, h970, hlam]
        · linarith only [h0, h1406, h1408, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1587 | h1587
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1588 | h1588
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1589 | h1589
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1590 | h1590
              · linarith only [h0, h1407, h1590, hc12, hlam, hphi, ht01, u0ehi5]
              · linarith only [h0, h1406, h1589, h1590, hc23, hlam, hphi, ht01, ht12, u0ehi9]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1593 | h1593
              · linarith only [h0, h1407, h1593, hc12, hlam, hphi, ht01, u0ehi5]
              · linarith only [h0, h1406, h1593, hc23, hlam, hphi, ht01, ht12, u0ehi8]
          · linarith only [h1406, h1588, h970, hlam]
        · linarith only [h0, h1406, h1587, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1598 | h1598
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1599 | h1599
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1600 | h1600
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1601 | h1601
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1602 | h1602
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1603 | h1603
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1604 | h1604
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1605 | h1605
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1606 | h1606
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1607 | h1607
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1608 | h1608
                          · linarith only [h1598, h1606, h1608, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                          · linarith only [h1598, h1606, h1607, h1608, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1611 | h1611
                          · linarith only [h1598, h1600, h1607, h1611, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases h4bigk with h1613c | h1613c | h1613c | h1613c | h1613c | h1613c | h1613c | h1613c | h1613c | h1613c | h1613c | h1613c | h1613c | h1613c | h1613c | h1613c | h1613c | h1613c | h1613c | h1613c | h1613c | h1613c | h1613c | h1613c | h1613c
                            · have p1613_0 := h1613c.1
                              have p1613_1 := h1613c.2.1
                              have p1613_2 := h1613c.2.2.1
                              have p1613_3 := h1613c.2.2.2
                              linarith only [hlam, p1613_0]
                            · have p1613_0 := h1613c.1
                              have p1613_1 := h1613c.2.1
                              have p1613_2 := h1613c.2.2.1
                              have p1613_3 := h1613c.2.2.2
                              linarith only [h1406, hlam, p1613_0]
                            · have p1613_0 := h1613c.1
                              have p1613_1 := h1613c.2.1
                              have p1613_2 := h1613c.2.2.1
                              have p1613_3 := h1613c.2.2.2
                              rcases p1613_3 (m.d 0 4) (by simp) with h1616 | h1616
                              · rcases p1613_3 (m.d 1 4) (by simp) with h1617 | h1617
                                · rcases p1613_3 (m.d 2 4) (by simp) with h1618 | h1618
                                  · linarith only [h1599, h1618, hlam]
                                  · rcases p1613_3 (m.d 3 4) (by simp) with h1620 | h1620
                                    · linarith only [h1600, h1620, hlam]
                                    · rcases p1613_3 (m.d 4 5) (by simp) with h1622 | h1622
                                      · linarith only [h1601, h1622, hlam]
                                      · linarith only [h1607, h1622, hlam]
                                · linarith only [h1603, h1617, hlam]
                              · linarith only [h1599, h1616, hlam]
                            · have p1613_0 := h1613c.1
                              have p1613_1 := h1613c.2.1
                              have p1613_2 := h1613c.2.2.1
                              have p1613_3 := h1613c.2.2.2
                              rcases p1613_3 (m.d 0 4) (by simp) with h1627 | h1627
                              · rcases p1613_3 (m.d 1 4) (by simp) with h1628 | h1628
                                · rcases p1613_3 (m.d 2 4) (by simp) with h1629 | h1629
                                  · linarith only [h1599, h1629, hlam]
                                  · linarith only [h1606, h1629, hlam]
                                · linarith only [h1604, h1628, hlam]
                              · linarith only [h1600, h1627, hlam]
                            · have p1613_0 := h1613c.1
                              have p1613_1 := h1613c.2.1
                              have p1613_2 := h1613c.2.2.1
                              have p1613_3 := h1613c.2.2.2
                              linarith only [h1598, h1600, h1606, h1607, hc34, hlam, hphi, ht0b, ht45, ht5b, p1613_1, u0elo1]
                            · have p1613_0 := h1613c.1
                              have p1613_1 := h1613c.2.1
                              have p1613_2 := h1613c.2.2.1
                              have p1613_3 := h1613c.2.2.2
                              linarith only [h1406, h1602, h1604, hc12, hlam, hphi, ht01, p1613_1, u0ehi5]
                            · have p1613_0 := h1613c.1
                              have p1613_1 := h1613c.2.1
                              have p1613_2 := h1613c.2.2.1
                              have p1613_3 := h1613c.2.2.2
                              linarith only [hlam, p1613_0]
                            · have p1613_0 := h1613c.1
                              have p1613_1 := h1613c.2.1
                              have p1613_2 := h1613c.2.2.1
                              have p1613_3 := h1613c.2.2.2
                              rcases p1613_3 (m.d 0 4) (by simp) with h1637 | h1637
                              · linarith only [h1406, h1637, hlam]
                              · linarith only [h1599, h1637, hlam]
                            · have p1613_0 := h1613c.1
                              have p1613_1 := h1613c.2.1
                              have p1613_2 := h1613c.2.2.1
                              have p1613_3 := h1613c.2.2.2
                              rcases p1613_3 (m.d 0 4) (by simp) with h1640 | h1640
                              · linarith only [h1406, h1640, hlam]
                              · linarith only [h1600, h1640, hlam]
                            · have p1613_0 := h1613c.1
                              have p1613_1 := h1613c.2.1
                              have p1613_2 := h1613c.2.2.1
                              have p1613_3 := h1613c.2.2.2
                              rcases p1613_3 (m.d 0 4) (by simp) with h1643 | h1643
                              · linarith only [h1406, h1643, hlam]
                              · linarith only [h1601, h1643, hlam]
                            · have p1613_0 := h1613c.1
                              have p1613_1 := h1613c.2.1
                              have p1613_2 := h1613c.2.2.1
                              have p1613_3 := h1613c.2.2.2
                              linarith only [h1599, hlam, p1613_1]
                            · have p1613_0 := h1613c.1
                              have p1613_1 := h1613c.2.1
                              have p1613_2 := h1613c.2.2.1
                              have p1613_3 := h1613c.2.2.2
                              linarith only [h1603, hlam, p1613_1]
                            · have p1613_0 := h1613c.1
                              have p1613_1 := h1613c.2.1
                              have p1613_2 := h1613c.2.2.1
                              have p1613_3 := h1613c.2.2.2
                              linarith only [hlam, p1613_0]
                            · have p1613_0 := h1613c.1
                              have p1613_1 := h1613c.2.1
                              have p1613_2 := h1613c.2.2.1
                              have p1613_3 := h1613c.2.2.2
                              linarith only [h1601, h1607, hc34, hlam, hphi, ht0b, ht45, ht5b, p1613_1, u0elo3]
                            · have p1613_0 := h1613c.1
                              have p1613_1 := h1613c.2.1
                              have p1613_2 := h1613c.2.2.1
                              have p1613_3 := h1613c.2.2.2
                              linarith only [h1607, hlam, p1613_0]
                            · have p1613_0 := h1613c.1
                              have p1613_1 := h1613c.2.1
                              have p1613_2 := h1613c.2.2.1
                              have p1613_3 := h1613c.2.2.2
                              linarith only [h1600, hlam, p1613_1]
                            · have p1613_0 := h1613c.1
                              have p1613_1 := h1613c.2.1
                              have p1613_2 := h1613c.2.2.1
                              have p1613_3 := h1613c.2.2.2
                              linarith only [h1604, hlam, p1613_0]
                            · have p1613_0 := h1613c.1
                              have p1613_1 := h1613c.2.1
                              have p1613_2 := h1613c.2.2.1
                              have p1613_3 := h1613c.2.2.2
                              linarith only [h1606, hlam, p1613_0]
                            · have p1613_0 := h1613c.1
                              have p1613_1 := h1613c.2.1
                              have p1613_2 := h1613c.2.2.1
                              have p1613_3 := h1613c.2.2.2
                              linarith only [hlam, p1613_0]
                            · have p1613_0 := h1613c.1
                              have p1613_1 := h1613c.2.1
                              have p1613_2 := h1613c.2.2.1
                              have p1613_3 := h1613c.2.2.2
                              linarith only [h1611, hlam, p1613_0]
                            · have p1613_0 := h1613c.1
                              have p1613_1 := h1613c.2.1
                              have p1613_2 := h1613c.2.2.1
                              have p1613_3 := h1613c.2.2.2
                              linarith only [h1601, hlam, p1613_0]
                            · have p1613_0 := h1613c.1
                              have p1613_1 := h1613c.2.1
                              have p1613_2 := h1613c.2.2.1
                              have p1613_3 := h1613c.2.2.2
                              linarith only [h1605, hlam, p1613_0]
                            · have p1613_0 := h1613c.1
                              have p1613_1 := h1613c.2.1
                              have p1613_2 := h1613c.2.2.1
                              have p1613_3 := h1613c.2.2.2
                              linarith only [h1601, hc24, hlam, hphi, ht0b, ht45, ht5b, p1613_1, u0elo3]
                            · have p1613_0 := h1613c.1
                              have p1613_1 := h1613c.2.1
                              have p1613_2 := h1613c.2.2.1
                              have p1613_3 := h1613c.2.2.2
                              linarith only [h1598, h1600, h1601, hc34, hlam, hphi, ht0b, ht45, ht5b, p1613_1, u0elo1]
                            · have p1613_0 := h1613c.1
                              have p1613_1 := h1613c.2.1
                              have p1613_2 := h1613c.2.2.1
                              have p1613_3 := h1613c.2.2.2
                              linarith only [hlam, p1613_0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1661 | h1661
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1662 | h1662
                          · rcases h4bigk with h1663c | h1663c | h1663c | h1663c | h1663c | h1663c | h1663c | h1663c | h1663c | h1663c | h1663c | h1663c | h1663c | h1663c | h1663c | h1663c | h1663c | h1663c | h1663c | h1663c | h1663c | h1663c | h1663c | h1663c | h1663c
                            · have p1663_0 := h1663c.1
                              have p1663_1 := h1663c.2.1
                              have p1663_2 := h1663c.2.2.1
                              have p1663_3 := h1663c.2.2.2
                              linarith only [hlam, p1663_0]
                            · have p1663_0 := h1663c.1
                              have p1663_1 := h1663c.2.1
                              have p1663_2 := h1663c.2.2.1
                              have p1663_3 := h1663c.2.2.2
                              linarith only [h1406, hlam, p1663_0]
                            · have p1663_0 := h1663c.1
                              have p1663_1 := h1663c.2.1
                              have p1663_2 := h1663c.2.2.1
                              have p1663_3 := h1663c.2.2.2
                              linarith only [h1598, h1600, h1661, hc45, hlam, hphi, ht0b, ht5b, p1663_1, u0elo1]
                            · have p1663_0 := h1663c.1
                              have p1663_1 := h1663c.2.1
                              have p1663_2 := h1663c.2.2.1
                              have p1663_3 := h1663c.2.2.2
                              linarith only [h1598, h1600, h1606, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1663_1, u0elo1]
                            · have p1663_0 := h1663c.1
                              have p1663_1 := h1663c.2.1
                              have p1663_2 := h1663c.2.2.1
                              have p1663_3 := h1663c.2.2.2
                              rcases p1663_3 (m.d 0 4) (by simp) with h1668 | h1668
                              · rcases p1663_3 (m.d 1 4) (by simp) with h1669 | h1669
                                · rcases p1663_3 (m.d 2 4) (by simp) with h1670 | h1670
                                  · linarith only [h1599, h1670, hlam]
                                  · linarith only [h1661, h1670, hlam]
                                · linarith only [h1605, h1669, hlam]
                              · linarith only [h1668, hlam, p1663_0]
                            · have p1663_0 := h1663c.1
                              have p1663_1 := h1663c.2.1
                              have p1663_2 := h1663c.2.2.1
                              have p1663_3 := h1663c.2.2.2
                              linarith only [h1602, h1604, hc12, hlam, hphi, ht01, p1663_1, u0ehi8]
                            · have p1663_0 := h1663c.1
                              have p1663_1 := h1663c.2.1
                              have p1663_2 := h1663c.2.2.1
                              have p1663_3 := h1663c.2.2.2
                              linarith only [hlam, p1663_0]
                            · have p1663_0 := h1663c.1
                              have p1663_1 := h1663c.2.1
                              have p1663_2 := h1663c.2.2.1
                              have p1663_3 := h1663c.2.2.2
                              rcases p1663_3 (m.d 0 4) (by simp) with h1677 | h1677
                              · linarith only [h1406, h1677, hlam]
                              · linarith only [h1599, h1677, hlam]
                            · have p1663_0 := h1663c.1
                              have p1663_1 := h1663c.2.1
                              have p1663_2 := h1663c.2.2.1
                              have p1663_3 := h1663c.2.2.2
                              rcases p1663_3 (m.d 0 4) (by simp) with h1680 | h1680
                              · linarith only [h1406, h1680, hlam]
                              · linarith only [h1600, h1680, hlam]
                            · have p1663_0 := h1663c.1
                              have p1663_1 := h1663c.2.1
                              have p1663_2 := h1663c.2.2.1
                              have p1663_3 := h1663c.2.2.2
                              rcases p1663_3 (m.d 0 4) (by simp) with h1683 | h1683
                              · linarith only [h1406, h1683, hlam]
                              · linarith only [h1601, h1683, hlam]
                            · have p1663_0 := h1663c.1
                              have p1663_1 := h1663c.2.1
                              have p1663_2 := h1663c.2.2.1
                              have p1663_3 := h1663c.2.2.2
                              linarith only [h1599, hlam, p1663_1]
                            · have p1663_0 := h1663c.1
                              have p1663_1 := h1663c.2.1
                              have p1663_2 := h1663c.2.2.1
                              have p1663_3 := h1663c.2.2.2
                              linarith only [h1603, hlam, p1663_1]
                            · have p1663_0 := h1663c.1
                              have p1663_1 := h1663c.2.1
                              have p1663_2 := h1663c.2.2.1
                              have p1663_3 := h1663c.2.2.2
                              linarith only [hlam, p1663_0]
                            · have p1663_0 := h1663c.1
                              have p1663_1 := h1663c.2.1
                              have p1663_2 := h1663c.2.2.1
                              have p1663_3 := h1663c.2.2.2
                              linarith only [h1606, hlam, p1663_1]
                            · have p1663_0 := h1663c.1
                              have p1663_1 := h1663c.2.1
                              have p1663_2 := h1663c.2.2.1
                              have p1663_3 := h1663c.2.2.2
                              linarith only [h1599, hc45, hlam, hphi, ht0b, ht5b, p1663_1, u0elo1]
                            · have p1663_0 := h1663c.1
                              have p1663_1 := h1663c.2.1
                              have p1663_2 := h1663c.2.2.1
                              have p1663_3 := h1663c.2.2.2
                              linarith only [h1600, hlam, p1663_1]
                            · have p1663_0 := h1663c.1
                              have p1663_1 := h1663c.2.1
                              have p1663_2 := h1663c.2.2.1
                              have p1663_3 := h1663c.2.2.2
                              linarith only [h1604, hlam, p1663_0]
                            · have p1663_0 := h1663c.1
                              have p1663_1 := h1663c.2.1
                              have p1663_2 := h1663c.2.2.1
                              have p1663_3 := h1663c.2.2.2
                              linarith only [h1598, h1600, hc24, hlam, hphi, ht0b, ht45, ht5b, p1663_1, u0elo1]
                            · have p1663_0 := h1663c.1
                              have p1663_1 := h1663c.2.1
                              have p1663_2 := h1663c.2.2.1
                              have p1663_3 := h1663c.2.2.2
                              linarith only [hlam, p1663_0]
                            · have p1663_0 := h1663c.1
                              have p1663_1 := h1663c.2.1
                              have p1663_2 := h1663c.2.2.1
                              have p1663_3 := h1663c.2.2.2
                              linarith only [h1598, h1600, hc45, hlam, hphi, ht0b, ht5b, p1663_1, u0elo1]
                            · have p1663_0 := h1663c.1
                              have p1663_1 := h1663c.2.1
                              have p1663_2 := h1663c.2.2.1
                              have p1663_3 := h1663c.2.2.2
                              linarith only [h1601, hlam, p1663_0]
                            · have p1663_0 := h1663c.1
                              have p1663_1 := h1663c.2.1
                              have p1663_2 := h1663c.2.2.1
                              have p1663_3 := h1663c.2.2.2
                              linarith only [h1605, hlam, p1663_0]
                            · have p1663_0 := h1663c.1
                              have p1663_1 := h1663c.2.1
                              have p1663_2 := h1663c.2.2.1
                              have p1663_3 := h1663c.2.2.2
                              linarith only [h1661, hlam, p1663_0]
                            · have p1663_0 := h1663c.1
                              have p1663_1 := h1663c.2.1
                              have p1663_2 := h1663c.2.2.1
                              have p1663_3 := h1663c.2.2.2
                              linarith only [h1662, hlam, p1663_0]
                            · have p1663_0 := h1663c.1
                              have p1663_1 := h1663c.2.1
                              have p1663_2 := h1663c.2.2.1
                              have p1663_3 := h1663c.2.2.2
                              linarith only [hlam, p1663_0]
                          · linarith only [h1599, h1661, h1662, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1702 | h1702
                          · linarith only [h1598, h1600, h1606, h1661, h1702, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h1601, h1606, h1702, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h1406, h1598, h1600, h1601, h1605, hlam, hphi, u0ehi5, u0elo1]
                  · linarith only [h1604, h970, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                · linarith only [h0, h1603, hc24, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h0, h1602, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1709 | h1709
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1710 | h1710
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1711 | h1711
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1712 | h1712
                    · linarith only [h1601, h1709, h1711, h1712, hc12, hlam, hphi, ht01, u0ehi8]
                    · linarith only [h1406, h1712, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5]
                  · linarith only [h1598, h1600, h1711, h970, hlam, hphi, u0ehi5, u0elo1]
                · linarith only [h0, h1599, h1710, hlam, hphi, u0ehi5, u0elo1]
              · linarith only [h0, h1598, h1709, hlam, hphi, u0ehi5, u0elo1]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1718 | h1718
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1719 | h1719
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1720 | h1720
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1721 | h1721
                  · linarith only [h1600, h1719, h1721, h970, hc12, hlam, hphi, ht01, u0ehi5]
                  · linarith only [h1721, h970, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                · linarith only [h0, h1599, h1720, hlam, hphi, u0ehi5, u0elo1]
              · linarith only [h0, h1598, h1719, hlam, hphi, u0ehi5, u0elo1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1726 | h1726
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1727 | h1727
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1728 | h1728
                  · linarith only [h1600, h1726, h1728, h970, hc12, hlam, hphi, ht01, u0ehi5]
                  · linarith only [h1728, h970, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                · linarith only [h0, h1599, h1727, hlam, hphi, u0ehi5, u0elo1]
              · linarith only [h0, h1598, h1726, hlam, hphi, u0ehi5, u0elo1]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1733 | h1733
          · linarith only [h1598, h1599, h1733, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1735 | h1735
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1736 | h1736
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1737 | h1737
                · linarith only [h1599, h1737, hc12, hlam, hphi, ht01, u0ehi6]
                · linarith only [h0, h1737, hc24, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h0, h1598, h1599, h1736, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1741 | h1741
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1742 | h1742
                · linarith only [h1599, h1742, hc12, hlam, hphi, ht01, u0ehi6]
                · linarith only [h0, h1742, hc24, hlam, hphi, ht01, ht12, u0ehi5]
              · linarith only [h0, h1598, h1741, hlam, hphi, u0ehi5, u0elo1]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1746 | h1746
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1747 | h1747
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1748 | h1748
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1749 | h1749
              · linarith only [h1598, h1749, hc12, hlam, hphi, ht01, u0ehi6]
              · linarith only [h0, h1749, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1752 | h1752
              · linarith only [h1598, h1752, hc12, hlam, hphi, ht01, u0ehi6]
              · linarith only [h0, h1752, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · linarith only [h1598, h1746, h1747, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1756 | h1756
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1757 | h1757
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1758 | h1758
              · linarith only [h0, h1598, h1758, hc12, hlam, hphi, ht01, u0ehi5]
              · linarith only [h0, h1758, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1761 | h1761
              · linarith only [h0, h1598, h1761, hc12, hlam, hphi, ht01, u0ehi5]
              · linarith only [h0, h1761, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1764 | h1764
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1765 | h1765
              · linarith only [h0, h1598, h1765, hc12, hlam, hphi, ht01, u0ehi5]
              · linarith only [h0, h1765, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1768 | h1768
              · linarith only [h0, h1598, h1768, hc12, hlam, hphi, ht01, u0ehi5]
              · linarith only [h0, h1768, hc23, hlam, hphi, ht01, ht12, u0ehi5]

set_option maxHeartbeats 3542000 in
set_option maxHeartbeats 3542000 in
theorem r1l7_20_11_14_M_LR_L_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_11_14_M_LR_L_I_L_I_x0 m hb0 hb1 hb4 h0
  · exact r1l7_20_11_14_M_LR_L_I_L_I_x1 m hb0 hb1 hb4 h0

end R2N4
