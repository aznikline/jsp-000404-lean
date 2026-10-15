import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_77S10

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_21_14_M_LI_L_R_x1 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4ehi := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h192 | h192
  · rcases m.htr 0 1 4 (by decide) (by decide) with h193 | h193
    · linarith only [h0, h193, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h195 | h195
      · rcases m.htr 1 2 3 (by decide) (by decide) with h196 | h196
        · rcases m.htr 1 2 4 (by decide) (by decide) with h197 | h197
          · rcases m.htr 1 3 4 (by decide) (by decide) with h198 | h198
            · linarith only [h192, h193, h197, h198, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h200 | h200
              · linarith only [h193, h195, h197, h200, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi4]
              · linarith only [h192, h193, h200, hc13, hc45, hlam, hphi, ht34]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h203 | h203
            · linarith only [h192, h203, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h205 | h205
              · linarith only [h0, h195, h197, h205, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3, u4ehi4]
              · linarith only [h0, h192, h196, h197, h205, hc23, hc45, hlam, hphi, ht34]
        · linarith only [h0, h192, h196, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h209 | h209
        · rcases m.htr 1 2 4 (by decide) (by decide) with h210 | h210
          · rcases m.htr 1 3 4 (by decide) (by decide) with h211 | h211
            · linarith only [h192, h195, h211, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4, u4ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h213 | h213
              · rcases h1bigk with h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c | h214c
                · have p214_0 := h214c.1
                  have p214_1 := h214c.2.1
                  have p214_2 := h214c.2.2.1
                  have p214_3 := h214c.2.2.2
                  linarith only [hlam, p214_0]
                · have p214_0 := h214c.1
                  have p214_1 := h214c.2.1
                  have p214_2 := h214c.2.2.1
                  have p214_3 := h214c.2.2.2
                  linarith only [h0, hlam, p214_0]
                · have p214_0 := h214c.1
                  have p214_1 := h214c.2.1
                  have p214_2 := h214c.2.2.1
                  have p214_3 := h214c.2.2.2
                  linarith only [h195, h209, h210, h213, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p214_1, u1elo1]
                · have p214_0 := h214c.1
                  have p214_1 := h214c.2.1
                  have p214_2 := h214c.2.2.1
                  have p214_3 := h214c.2.2.2
                  linarith only [h193, hlam, p214_0]
                · have p214_0 := h214c.1
                  have p214_1 := h214c.2.1
                  have p214_2 := h214c.2.2.1
                  have p214_3 := h214c.2.2.2
                  linarith only [h195, hlam, p214_0]
                · have p214_0 := h214c.1
                  have p214_1 := h214c.2.1
                  have p214_2 := h214c.2.2.1
                  have p214_3 := h214c.2.2.2
                  linarith only [hc01, hlam, hphi, p214_1, u1elo1]
                · have p214_0 := h214c.1
                  have p214_1 := h214c.2.1
                  have p214_2 := h214c.2.2.1
                  have p214_3 := h214c.2.2.2
                  linarith only [hlam, p214_0]
                · have p214_0 := h214c.1
                  have p214_1 := h214c.2.1
                  have p214_2 := h214c.2.2.1
                  have p214_3 := h214c.2.2.2
                  rcases p214_3 (m.d 0 1) (by simp) with h222 | h222
                  · linarith only [h0, h222, hlam]
                  · linarith only [h192, h222, hlam]
                · have p214_0 := h214c.1
                  have p214_1 := h214c.2.1
                  have p214_2 := h214c.2.2.1
                  have p214_3 := h214c.2.2.2
                  linarith only [hlam, hphi, ht01, ht0b, ht45, ht5b, p214_1, u1elo1, u4ehi1]
                · have p214_0 := h214c.1
                  have p214_1 := h214c.2.1
                  have p214_2 := h214c.2.2.1
                  have p214_3 := h214c.2.2.2
                  linarith only [h192, h195, h209, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p214_1, u1elo1]
                · have p214_0 := h214c.1
                  have p214_1 := h214c.2.1
                  have p214_2 := h214c.2.2.1
                  have p214_3 := h214c.2.2.2
                  linarith only [h192, hlam, p214_0]
                · have p214_0 := h214c.1
                  have p214_1 := h214c.2.1
                  have p214_2 := h214c.2.2.1
                  have p214_3 := h214c.2.2.2
                  linarith only [h209, hlam, p214_0]
                · have p214_0 := h214c.1
                  have p214_1 := h214c.2.1
                  have p214_2 := h214c.2.2.1
                  have p214_3 := h214c.2.2.2
                  linarith only [hlam, p214_0]
                · have p214_0 := h214c.1
                  have p214_1 := h214c.2.1
                  have p214_2 := h214c.2.2.1
                  have p214_3 := h214c.2.2.2
                  linarith only [h211, hlam, p214_0]
                · have p214_0 := h214c.1
                  have p214_1 := h214c.2.1
                  have p214_2 := h214c.2.2.1
                  have p214_3 := h214c.2.2.2
                  linarith only [h192, h195, hlam, p214_1]
                · have p214_0 := h214c.1
                  have p214_1 := h214c.2.1
                  have p214_2 := h214c.2.2.1
                  have p214_3 := h214c.2.2.2
                  linarith only [h192, h209, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p214_1, u1elo3]
                · have p214_0 := h214c.1
                  have p214_1 := h214c.2.1
                  have p214_2 := h214c.2.2.1
                  have p214_3 := h214c.2.2.2
                  linarith only [h210, hlam, p214_0]
                · have p214_0 := h214c.1
                  have p214_1 := h214c.2.1
                  have p214_2 := h214c.2.2.1
                  have p214_3 := h214c.2.2.2
                  rcases p214_3 (m.d 0 1) (by simp) with h234 | h234
                  · linarith only [h193, h234, hlam]
                  · linarith only [h192, h234, hlam]
                · have p214_0 := h214c.1
                  have p214_1 := h214c.2.1
                  have p214_2 := h214c.2.2.1
                  have p214_3 := h214c.2.2.2
                  linarith only [hlam, p214_0]
                · have p214_0 := h214c.1
                  have p214_1 := h214c.2.1
                  have p214_2 := h214c.2.2.1
                  have p214_3 := h214c.2.2.2
                  linarith only [h192, h195, h209, h210, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p214_1, u1elo1]
                · have p214_0 := h214c.1
                  have p214_1 := h214c.2.1
                  have p214_2 := h214c.2.2.1
                  have p214_3 := h214c.2.2.2
                  linarith only [h192, h209, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p214_1, u1elo4]
                · have p214_0 := h214c.1
                  have p214_1 := h214c.2.1
                  have p214_2 := h214c.2.2.1
                  have p214_3 := h214c.2.2.2
                  linarith only [h210, h213, hlam, p214_1]
                · have p214_0 := h214c.1
                  have p214_1 := h214c.2.1
                  have p214_2 := h214c.2.2.1
                  have p214_3 := h214c.2.2.2
                  rcases p214_3 (m.d 0 1) (by simp) with h241 | h241
                  · linarith only [h195, h241, hlam]
                  · linarith only [h192, h241, hlam]
                · have p214_0 := h214c.1
                  have p214_1 := h214c.2.1
                  have p214_2 := h214c.2.2.1
                  have p214_3 := h214c.2.2.2
                  linarith only [h213, hlam, p214_0]
                · have p214_0 := h214c.1
                  have p214_1 := h214c.2.1
                  have p214_2 := h214c.2.2.1
                  have p214_3 := h214c.2.2.2
                  linarith only [hlam, p214_0]
              · linarith only [h192, h193, h209, h213, hc23, hc45, hlam, hphi, ht34]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h247 | h247
            · linarith only [h192, h247, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0, u4ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h249 | h249
              · rcases h1bigk with h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c
                · have p250_0 := h250c.1
                  have p250_1 := h250c.2.1
                  have p250_2 := h250c.2.2.1
                  have p250_3 := h250c.2.2.2
                  linarith only [hlam, p250_0]
                · have p250_0 := h250c.1
                  have p250_1 := h250c.2.1
                  have p250_2 := h250c.2.2.1
                  have p250_3 := h250c.2.2.2
                  linarith only [h0, hlam, p250_0]
                · have p250_0 := h250c.1
                  have p250_1 := h250c.2.1
                  have p250_2 := h250c.2.2.1
                  have p250_3 := h250c.2.2.2
                  linarith only [h0, h210, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p250_1]
                · have p250_0 := h250c.1
                  have p250_1 := h250c.2.1
                  have p250_2 := h250c.2.2.1
                  have p250_3 := h250c.2.2.2
                  linarith only [h193, hlam, p250_0]
                · have p250_0 := h250c.1
                  have p250_1 := h250c.2.1
                  have p250_2 := h250c.2.2.1
                  have p250_3 := h250c.2.2.2
                  linarith only [h195, hlam, p250_0]
                · have p250_0 := h250c.1
                  have p250_1 := h250c.2.1
                  have p250_2 := h250c.2.2.1
                  have p250_3 := h250c.2.2.2
                  linarith only [h210, hc01, hc24, hlam, hphi, ht12, p250_1]
                · have p250_0 := h250c.1
                  have p250_1 := h250c.2.1
                  have p250_2 := h250c.2.2.1
                  have p250_3 := h250c.2.2.2
                  linarith only [hlam, p250_0]
                · have p250_0 := h250c.1
                  have p250_1 := h250c.2.1
                  have p250_2 := h250c.2.2.1
                  have p250_3 := h250c.2.2.2
                  rcases p250_3 (m.d 0 1) (by simp) with h258 | h258
                  · linarith only [h0, h258, hlam]
                  · linarith only [h192, h258, hlam]
                · have p250_0 := h250c.1
                  have p250_1 := h250c.2.1
                  have p250_2 := h250c.2.2.1
                  have p250_3 := h250c.2.2.2
                  linarith only [h210, hlam, p250_1]
                · have p250_0 := h250c.1
                  have p250_1 := h250c.2.1
                  have p250_2 := h250c.2.2.1
                  have p250_3 := h250c.2.2.2
                  linarith only [h192, h195, h209, h210, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p250_1]
                · have p250_0 := h250c.1
                  have p250_1 := h250c.2.1
                  have p250_2 := h250c.2.2.1
                  have p250_3 := h250c.2.2.2
                  linarith only [h192, hlam, p250_0]
                · have p250_0 := h250c.1
                  have p250_1 := h250c.2.1
                  have p250_2 := h250c.2.2.1
                  have p250_3 := h250c.2.2.2
                  linarith only [h209, hlam, p250_0]
                · have p250_0 := h250c.1
                  have p250_1 := h250c.2.1
                  have p250_2 := h250c.2.2.1
                  have p250_3 := h250c.2.2.2
                  linarith only [hlam, p250_0]
                · have p250_0 := h250c.1
                  have p250_1 := h250c.2.1
                  have p250_2 := h250c.2.2.1
                  have p250_3 := h250c.2.2.2
                  linarith only [h247, hlam, p250_0]
                · have p250_0 := h250c.1
                  have p250_1 := h250c.2.1
                  have p250_2 := h250c.2.2.1
                  have p250_3 := h250c.2.2.2
                  linarith only [h192, h195, hlam, p250_1]
                · have p250_0 := h250c.1
                  have p250_1 := h250c.2.1
                  have p250_2 := h250c.2.2.1
                  have p250_3 := h250c.2.2.2
                  linarith only [h192, h209, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p250_1, u1elo3]
                · have p250_0 := h250c.1
                  have p250_1 := h250c.2.1
                  have p250_2 := h250c.2.2.1
                  have p250_3 := h250c.2.2.2
                  linarith only [h0, h192, h209, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p250_1, u1elo3]
                · have p250_0 := h250c.1
                  have p250_1 := h250c.2.1
                  have p250_2 := h250c.2.2.1
                  have p250_3 := h250c.2.2.2
                  rcases p250_3 (m.d 0 1) (by simp) with h270 | h270
                  · linarith only [h193, h270, hlam]
                  · linarith only [h192, h270, hlam]
                · have p250_0 := h250c.1
                  have p250_1 := h250c.2.1
                  have p250_2 := h250c.2.2.1
                  have p250_3 := h250c.2.2.2
                  linarith only [hlam, p250_0]
                · have p250_0 := h250c.1
                  have p250_1 := h250c.2.1
                  have p250_2 := h250c.2.2.1
                  have p250_3 := h250c.2.2.2
                  linarith only [h192, h195, h209, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p250_1, u1elo3]
                · have p250_0 := h250c.1
                  have p250_1 := h250c.2.1
                  have p250_2 := h250c.2.2.1
                  have p250_3 := h250c.2.2.2
                  linarith only [h192, h209, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p250_1, u1elo4]
                · have p250_0 := h250c.1
                  have p250_1 := h250c.2.1
                  have p250_2 := h250c.2.2.1
                  have p250_3 := h250c.2.2.2
                  linarith only [h0, h192, h209, h249, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p250_1, u1elo3]
                · have p250_0 := h250c.1
                  have p250_1 := h250c.2.1
                  have p250_2 := h250c.2.2.1
                  have p250_3 := h250c.2.2.2
                  rcases p250_3 (m.d 0 1) (by simp) with h277 | h277
                  · linarith only [h195, h277, hlam]
                  · linarith only [h192, h277, hlam]
                · have p250_0 := h250c.1
                  have p250_1 := h250c.2.1
                  have p250_2 := h250c.2.2.1
                  have p250_3 := h250c.2.2.2
                  linarith only [h249, hlam, p250_0]
                · have p250_0 := h250c.1
                  have p250_1 := h250c.2.1
                  have p250_2 := h250c.2.2.1
                  have p250_3 := h250c.2.2.2
                  linarith only [hlam, p250_0]
              · linarith only [h192, h193, h209, h249, hc23, hc45, hlam, hphi, ht34]
        · linarith only [h0, h192, h209, hlam]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h284 | h284
    · linarith only [h0, h284, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h286 | h286
      · rcases m.htr 1 2 3 (by decide) (by decide) with h287 | h287
        · rcases m.htr 1 2 4 (by decide) (by decide) with h288 | h288
          · rcases m.htr 1 3 4 (by decide) (by decide) with h289 | h289
            · rcases m.htr 1 4 5 (by decide) (by decide) with h290 | h290
              · linarith only [h284, h286, h287, h289, h290, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi4]
              · linarith only [h284, h286, h290, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h293 | h293
              · linarith only [h0, h286, h293, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi4]
              · linarith only [h192, h286, h289, h293, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h296 | h296
            · linarith only [h287, h288, h296, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h298 | h298
              · linarith only [h192, h286, h287, h288, h298, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · linarith only [h192, h286, h287, h288, h298, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h301 | h301
          · rcases m.htr 1 3 4 (by decide) (by decide) with h302 | h302
            · rcases m.htr 1 4 5 (by decide) (by decide) with h303 | h303
              · linarith only [h284, h286, h301, h303, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi4]
              · linarith only [h284, h286, h303, hlam]
            · linarith only [h287, h301, h302, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h307 | h307
            · rcases m.htr 1 4 5 (by decide) (by decide) with h308 | h308
              · linarith only [h0, h286, h301, h307, h308, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2, u4ehi4]
              · linarith only [h0, h286, h301, h308, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h311 | h311
              · linarith only [h0, h286, h311, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1, u4ehi4]
              · linarith only [h0, h286, h287, h307, h311, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h314 | h314
        · rcases m.htr 1 2 4 (by decide) (by decide) with h315 | h315
          · rcases m.htr 1 3 4 (by decide) (by decide) with h316 | h316
            · rcases m.htr 1 4 5 (by decide) (by decide) with h317 | h317
              · rcases h1bigk with h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c
                · have p318_0 := h318c.1
                  have p318_1 := h318c.2.1
                  have p318_2 := h318c.2.2.1
                  have p318_3 := h318c.2.2.2
                  linarith only [hlam, p318_0]
                · have p318_0 := h318c.1
                  have p318_1 := h318c.2.1
                  have p318_2 := h318c.2.2.1
                  have p318_3 := h318c.2.2.2
                  linarith only [h0, hlam, p318_0]
                · have p318_0 := h318c.1
                  have p318_1 := h318c.2.1
                  have p318_2 := h318c.2.2.1
                  have p318_3 := h318c.2.2.2
                  linarith only [h192, hlam, p318_0]
                · have p318_0 := h318c.1
                  have p318_1 := h318c.2.1
                  have p318_2 := h318c.2.2.1
                  have p318_3 := h318c.2.2.2
                  linarith only [h284, hlam, p318_0]
                · have p318_0 := h318c.1
                  have p318_1 := h318c.2.1
                  have p318_2 := h318c.2.2.1
                  have p318_3 := h318c.2.2.2
                  linarith only [h286, hlam, p318_0]
                · have p318_0 := h318c.1
                  have p318_1 := h318c.2.1
                  have p318_2 := h318c.2.2.1
                  have p318_3 := h318c.2.2.2
                  linarith only [hc01, hlam, hphi, p318_1, u1elo1]
                · have p318_0 := h318c.1
                  have p318_1 := h318c.2.1
                  have p318_2 := h318c.2.2.1
                  have p318_3 := h318c.2.2.2
                  linarith only [hlam, p318_0]
                · have p318_0 := h318c.1
                  have p318_1 := h318c.2.1
                  have p318_2 := h318c.2.2.1
                  have p318_3 := h318c.2.2.2
                  linarith only [h316, h317, hlam, hphi, ht01, ht0b, ht45, ht5b, p318_1, u1elo1, u4ehi4]
                · have p318_0 := h318c.1
                  have p318_1 := h318c.2.1
                  have p318_2 := h318c.2.2.1
                  have p318_3 := h318c.2.2.2
                  linarith only [h317, hlam, hphi, ht01, ht0b, ht45, ht5b, p318_1, u1elo1, u4ehi4]
                · have p318_0 := h318c.1
                  have p318_1 := h318c.2.1
                  have p318_2 := h318c.2.2.1
                  have p318_3 := h318c.2.2.2
                  linarith only [h286, hc01, hlam, hphi, p318_1, u1elo1]
                · have p318_0 := h318c.1
                  have p318_1 := h318c.2.1
                  have p318_2 := h318c.2.2.1
                  have p318_3 := h318c.2.2.2
                  linarith only [hc01, hlam, hphi, p318_1, u1elo2]
                · have p318_0 := h318c.1
                  have p318_1 := h318c.2.1
                  have p318_2 := h318c.2.2.1
                  have p318_3 := h318c.2.2.2
                  linarith only [h314, hlam, p318_0]
                · have p318_0 := h318c.1
                  have p318_1 := h318c.2.1
                  have p318_2 := h318c.2.2.1
                  have p318_3 := h318c.2.2.2
                  linarith only [hlam, p318_0]
                · have p318_0 := h318c.1
                  have p318_1 := h318c.2.1
                  have p318_2 := h318c.2.2.1
                  have p318_3 := h318c.2.2.2
                  linarith only [h314, h317, hlam, hphi, ht01, ht0b, ht45, ht5b, p318_1, u1elo1, u4ehi4]
                · have p318_0 := h318c.1
                  have p318_1 := h318c.2.1
                  have p318_2 := h318c.2.2.1
                  have p318_3 := h318c.2.2.2
                  linarith only [h286, h314, hc01, hlam, hphi, p318_1, u1elo1]
                · have p318_0 := h318c.1
                  have p318_1 := h318c.2.1
                  have p318_2 := h318c.2.2.1
                  have p318_3 := h318c.2.2.2
                  linarith only [hc01, hlam, hphi, p318_1, u1elo3]
                · have p318_0 := h318c.1
                  have p318_1 := h318c.2.1
                  have p318_2 := h318c.2.2.1
                  have p318_3 := h318c.2.2.2
                  linarith only [h315, hlam, p318_0]
                · have p318_0 := h318c.1
                  have p318_1 := h318c.2.1
                  have p318_2 := h318c.2.2.1
                  have p318_3 := h318c.2.2.2
                  linarith only [h316, hlam, p318_1]
                · have p318_0 := h318c.1
                  have p318_1 := h318c.2.1
                  have p318_2 := h318c.2.2.1
                  have p318_3 := h318c.2.2.2
                  linarith only [hlam, p318_0]
                · have p318_0 := h318c.1
                  have p318_1 := h318c.2.1
                  have p318_2 := h318c.2.2.1
                  have p318_3 := h318c.2.2.2
                  linarith only [h286, h314, h316, hc01, hlam, hphi, p318_1, u1elo1]
                · have p318_0 := h318c.1
                  have p318_1 := h318c.2.1
                  have p318_2 := h318c.2.2.1
                  have p318_3 := h318c.2.2.2
                  linarith only [hc01, hlam, hphi, p318_1, u1elo4]
                · have p318_0 := h318c.1
                  have p318_1 := h318c.2.1
                  have p318_2 := h318c.2.2.1
                  have p318_3 := h318c.2.2.2
                  linarith only [h314, h316, h317, hlam, p318_1]
                · have p318_0 := h318c.1
                  have p318_1 := h318c.2.1
                  have p318_2 := h318c.2.2.1
                  have p318_3 := h318c.2.2.2
                  linarith only [h316, h317, hlam, p318_1]
                · have p318_0 := h318c.1
                  have p318_1 := h318c.2.1
                  have p318_2 := h318c.2.2.1
                  have p318_3 := h318c.2.2.2
                  linarith only [h317, hlam, p318_0]
                · have p318_0 := h318c.1
                  have p318_1 := h318c.2.1
                  have p318_2 := h318c.2.2.1
                  have p318_3 := h318c.2.2.2
                  linarith only [hlam, p318_0]
              · rcases h1bigk with h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c
                · have p344_0 := h344c.1
                  have p344_1 := h344c.2.1
                  have p344_2 := h344c.2.2.1
                  have p344_3 := h344c.2.2.2
                  linarith only [hlam, p344_0]
                · have p344_0 := h344c.1
                  have p344_1 := h344c.2.1
                  have p344_2 := h344c.2.2.1
                  have p344_3 := h344c.2.2.2
                  linarith only [h0, hlam, p344_0]
                · have p344_0 := h344c.1
                  have p344_1 := h344c.2.1
                  have p344_2 := h344c.2.2.1
                  have p344_3 := h344c.2.2.2
                  linarith only [h192, hlam, p344_0]
                · have p344_0 := h344c.1
                  have p344_1 := h344c.2.1
                  have p344_2 := h344c.2.2.1
                  have p344_3 := h344c.2.2.2
                  linarith only [h284, hlam, p344_0]
                · have p344_0 := h344c.1
                  have p344_1 := h344c.2.1
                  have p344_2 := h344c.2.2.1
                  have p344_3 := h344c.2.2.2
                  linarith only [h286, hlam, p344_0]
                · have p344_0 := h344c.1
                  have p344_1 := h344c.2.1
                  have p344_2 := h344c.2.2.1
                  have p344_3 := h344c.2.2.2
                  linarith only [hc01, hlam, hphi, p344_1, u1elo1]
                · have p344_0 := h344c.1
                  have p344_1 := h344c.2.1
                  have p344_2 := h344c.2.2.1
                  have p344_3 := h344c.2.2.2
                  linarith only [hlam, p344_0]
                · have p344_0 := h344c.1
                  have p344_1 := h344c.2.1
                  have p344_2 := h344c.2.2.1
                  have p344_3 := h344c.2.2.2
                  linarith only [h316, hlam, hphi, ht01, ht0b, ht45, ht5b, p344_1, u1elo1, u4ehi3]
                · have p344_0 := h344c.1
                  have p344_1 := h344c.2.1
                  have p344_2 := h344c.2.2.1
                  have p344_3 := h344c.2.2.2
                  linarith only [hlam, hphi, ht01, ht0b, ht45, ht5b, p344_1, u1elo1, u4ehi1]
                · have p344_0 := h344c.1
                  have p344_1 := h344c.2.1
                  have p344_2 := h344c.2.2.1
                  have p344_3 := h344c.2.2.2
                  linarith only [h284, h317, hc01, hlam, hphi, p344_1, u1elo1]
                · have p344_0 := h344c.1
                  have p344_1 := h344c.2.1
                  have p344_2 := h344c.2.2.1
                  have p344_3 := h344c.2.2.2
                  linarith only [hc01, hlam, hphi, p344_1, u1elo2]
                · have p344_0 := h344c.1
                  have p344_1 := h344c.2.1
                  have p344_2 := h344c.2.2.1
                  have p344_3 := h344c.2.2.2
                  linarith only [h314, hlam, p344_0]
                · have p344_0 := h344c.1
                  have p344_1 := h344c.2.1
                  have p344_2 := h344c.2.2.1
                  have p344_3 := h344c.2.2.2
                  linarith only [hlam, p344_0]
                · have p344_0 := h344c.1
                  have p344_1 := h344c.2.1
                  have p344_2 := h344c.2.2.1
                  have p344_3 := h344c.2.2.2
                  linarith only [h284, h314, hc01, hlam, hphi, p344_1, u1elo1]
                · have p344_0 := h344c.1
                  have p344_1 := h344c.2.1
                  have p344_2 := h344c.2.2.1
                  have p344_3 := h344c.2.2.2
                  linarith only [h284, h314, h317, hc01, hlam, hphi, p344_1, u1elo1]
                · have p344_0 := h344c.1
                  have p344_1 := h344c.2.1
                  have p344_2 := h344c.2.2.1
                  have p344_3 := h344c.2.2.2
                  linarith only [hc01, hlam, hphi, p344_1, u1elo3]
                · have p344_0 := h344c.1
                  have p344_1 := h344c.2.1
                  have p344_2 := h344c.2.2.1
                  have p344_3 := h344c.2.2.2
                  linarith only [h315, hlam, p344_0]
                · have p344_0 := h344c.1
                  have p344_1 := h344c.2.1
                  have p344_2 := h344c.2.2.1
                  have p344_3 := h344c.2.2.2
                  linarith only [h316, hlam, p344_1]
                · have p344_0 := h344c.1
                  have p344_1 := h344c.2.1
                  have p344_2 := h344c.2.2.1
                  have p344_3 := h344c.2.2.2
                  linarith only [hlam, p344_0]
                · have p344_0 := h344c.1
                  have p344_1 := h344c.2.1
                  have p344_2 := h344c.2.2.1
                  have p344_3 := h344c.2.2.2
                  linarith only [h317, hlam, p344_1]
                · have p344_0 := h344c.1
                  have p344_1 := h344c.2.1
                  have p344_2 := h344c.2.2.1
                  have p344_3 := h344c.2.2.2
                  linarith only [hc01, hlam, hphi, p344_1, u1elo4]
                · have p344_0 := h344c.1
                  have p344_1 := h344c.2.1
                  have p344_2 := h344c.2.2.1
                  have p344_3 := h344c.2.2.2
                  linarith only [h314, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p344_1, u1elo4]
                · have p344_0 := h344c.1
                  have p344_1 := h344c.2.1
                  have p344_2 := h344c.2.2.1
                  have p344_3 := h344c.2.2.2
                  linarith only [h316, hlam, hphi, ht01, ht0b, ht45, ht5b, p344_1, u1elo4, u4ehi3]
                · have p344_0 := h344c.1
                  have p344_1 := h344c.2.1
                  have p344_2 := h344c.2.2.1
                  have p344_3 := h344c.2.2.2
                  linarith only [hlam, hphi, ht01, ht0b, ht45, ht5b, p344_1, u1elo4, u4ehi1]
                · have p344_0 := h344c.1
                  have p344_1 := h344c.2.1
                  have p344_2 := h344c.2.2.1
                  have p344_3 := h344c.2.2.2
                  linarith only [hlam, p344_0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h370 | h370
              · rcases h1bigk with h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c | h371c
                · have p371_0 := h371c.1
                  have p371_1 := h371c.2.1
                  have p371_2 := h371c.2.2.1
                  have p371_3 := h371c.2.2.2
                  linarith only [hlam, p371_0]
                · have p371_0 := h371c.1
                  have p371_1 := h371c.2.1
                  have p371_2 := h371c.2.2.1
                  have p371_3 := h371c.2.2.2
                  linarith only [h0, hlam, p371_0]
                · have p371_0 := h371c.1
                  have p371_1 := h371c.2.1
                  have p371_2 := h371c.2.2.1
                  have p371_3 := h371c.2.2.2
                  linarith only [h192, hlam, p371_0]
                · have p371_0 := h371c.1
                  have p371_1 := h371c.2.1
                  have p371_2 := h371c.2.2.1
                  have p371_3 := h371c.2.2.2
                  linarith only [h284, hlam, p371_0]
                · have p371_0 := h371c.1
                  have p371_1 := h371c.2.1
                  have p371_2 := h371c.2.2.1
                  have p371_3 := h371c.2.2.2
                  linarith only [h286, hlam, p371_0]
                · have p371_0 := h371c.1
                  have p371_1 := h371c.2.1
                  have p371_2 := h371c.2.2.1
                  have p371_3 := h371c.2.2.2
                  linarith only [hc01, hlam, hphi, p371_1, u1elo1]
                · have p371_0 := h371c.1
                  have p371_1 := h371c.2.1
                  have p371_2 := h371c.2.2.1
                  have p371_3 := h371c.2.2.2
                  linarith only [hlam, p371_0]
                · have p371_0 := h371c.1
                  have p371_1 := h371c.2.1
                  have p371_2 := h371c.2.2.1
                  have p371_3 := h371c.2.2.2
                  linarith only [h192, hc01, hlam, hphi, p371_1, u1elo1]
                · have p371_0 := h371c.1
                  have p371_1 := h371c.2.1
                  have p371_2 := h371c.2.2.1
                  have p371_3 := h371c.2.2.2
                  linarith only [hlam, hphi, ht01, ht0b, ht45, ht5b, p371_1, u1elo1, u4ehi1]
                · have p371_0 := h371c.1
                  have p371_1 := h371c.2.1
                  have p371_2 := h371c.2.2.1
                  have p371_3 := h371c.2.2.2
                  linarith only [h286, hc01, hlam, hphi, p371_1, u1elo1]
                · have p371_0 := h371c.1
                  have p371_1 := h371c.2.1
                  have p371_2 := h371c.2.2.1
                  have p371_3 := h371c.2.2.2
                  linarith only [hc01, hlam, hphi, p371_1, u1elo2]
                · have p371_0 := h371c.1
                  have p371_1 := h371c.2.1
                  have p371_2 := h371c.2.2.1
                  have p371_3 := h371c.2.2.2
                  linarith only [h314, hlam, p371_0]
                · have p371_0 := h371c.1
                  have p371_1 := h371c.2.1
                  have p371_2 := h371c.2.2.1
                  have p371_3 := h371c.2.2.2
                  linarith only [hlam, p371_0]
                · have p371_0 := h371c.1
                  have p371_1 := h371c.2.1
                  have p371_2 := h371c.2.2.1
                  have p371_3 := h371c.2.2.2
                  linarith only [h316, hlam, p371_0]
                · have p371_0 := h371c.1
                  have p371_1 := h371c.2.1
                  have p371_2 := h371c.2.2.1
                  have p371_3 := h371c.2.2.2
                  linarith only [h286, h316, hc01, hc34, hlam, hphi, ht12, ht23, p371_1]
                · have p371_0 := h371c.1
                  have p371_1 := h371c.2.1
                  have p371_2 := h371c.2.2.1
                  have p371_3 := h371c.2.2.2
                  linarith only [hc01, hlam, hphi, p371_1, u1elo3]
                · have p371_0 := h371c.1
                  have p371_1 := h371c.2.1
                  have p371_2 := h371c.2.2.1
                  have p371_3 := h371c.2.2.2
                  linarith only [h315, hlam, p371_0]
                · have p371_0 := h371c.1
                  have p371_1 := h371c.2.1
                  have p371_2 := h371c.2.2.1
                  have p371_3 := h371c.2.2.2
                  linarith only [h192, h315, hc01, hlam, hphi, p371_1, u1elo1]
                · have p371_0 := h371c.1
                  have p371_1 := h371c.2.1
                  have p371_2 := h371c.2.2.1
                  have p371_3 := h371c.2.2.2
                  linarith only [hlam, p371_0]
                · have p371_0 := h371c.1
                  have p371_1 := h371c.2.1
                  have p371_2 := h371c.2.2.1
                  have p371_3 := h371c.2.2.2
                  linarith only [h286, h315, hc01, hlam, hphi, p371_1, u1elo1]
                · have p371_0 := h371c.1
                  have p371_1 := h371c.2.1
                  have p371_2 := h371c.2.2.1
                  have p371_3 := h371c.2.2.2
                  linarith only [hc01, hlam, hphi, p371_1, u1elo4]
                · have p371_0 := h371c.1
                  have p371_1 := h371c.2.1
                  have p371_2 := h371c.2.2.1
                  have p371_3 := h371c.2.2.2
                  linarith only [h315, h370, hlam, p371_1]
                · have p371_0 := h371c.1
                  have p371_1 := h371c.2.1
                  have p371_2 := h371c.2.2.1
                  have p371_3 := h371c.2.2.2
                  linarith only [h192, h315, h370, hc01, hlam, hphi, p371_1, u1elo1]
                · have p371_0 := h371c.1
                  have p371_1 := h371c.2.1
                  have p371_2 := h371c.2.2.1
                  have p371_3 := h371c.2.2.2
                  linarith only [h370, hlam, p371_0]
                · have p371_0 := h371c.1
                  have p371_1 := h371c.2.1
                  have p371_2 := h371c.2.2.1
                  have p371_3 := h371c.2.2.2
                  linarith only [hlam, p371_0]
              · rcases h1bigk with h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c | h397c
                · have p397_0 := h397c.1
                  have p397_1 := h397c.2.1
                  have p397_2 := h397c.2.2.1
                  have p397_3 := h397c.2.2.2
                  linarith only [hlam, p397_0]
                · have p397_0 := h397c.1
                  have p397_1 := h397c.2.1
                  have p397_2 := h397c.2.2.1
                  have p397_3 := h397c.2.2.2
                  linarith only [h0, hlam, p397_0]
                · have p397_0 := h397c.1
                  have p397_1 := h397c.2.1
                  have p397_2 := h397c.2.2.1
                  have p397_3 := h397c.2.2.2
                  linarith only [h192, hlam, p397_0]
                · have p397_0 := h397c.1
                  have p397_1 := h397c.2.1
                  have p397_2 := h397c.2.2.1
                  have p397_3 := h397c.2.2.2
                  linarith only [h284, hlam, p397_0]
                · have p397_0 := h397c.1
                  have p397_1 := h397c.2.1
                  have p397_2 := h397c.2.2.1
                  have p397_3 := h397c.2.2.2
                  linarith only [h286, hlam, p397_0]
                · have p397_0 := h397c.1
                  have p397_1 := h397c.2.1
                  have p397_2 := h397c.2.2.1
                  have p397_3 := h397c.2.2.2
                  linarith only [hc01, hlam, hphi, p397_1, u1elo1]
                · have p397_0 := h397c.1
                  have p397_1 := h397c.2.1
                  have p397_2 := h397c.2.2.1
                  have p397_3 := h397c.2.2.2
                  linarith only [hlam, p397_0]
                · have p397_0 := h397c.1
                  have p397_1 := h397c.2.1
                  have p397_2 := h397c.2.2.1
                  have p397_3 := h397c.2.2.2
                  linarith only [h192, hc01, hlam, hphi, p397_1, u1elo1]
                · have p397_0 := h397c.1
                  have p397_1 := h397c.2.1
                  have p397_2 := h397c.2.2.1
                  have p397_3 := h397c.2.2.2
                  linarith only [hlam, hphi, ht01, ht0b, ht45, ht5b, p397_1, u1elo1, u4ehi1]
                · have p397_0 := h397c.1
                  have p397_1 := h397c.2.1
                  have p397_2 := h397c.2.2.1
                  have p397_3 := h397c.2.2.2
                  linarith only [h286, hc01, hlam, hphi, p397_1, u1elo1]
                · have p397_0 := h397c.1
                  have p397_1 := h397c.2.1
                  have p397_2 := h397c.2.2.1
                  have p397_3 := h397c.2.2.2
                  linarith only [hc01, hlam, hphi, p397_1, u1elo2]
                · have p397_0 := h397c.1
                  have p397_1 := h397c.2.1
                  have p397_2 := h397c.2.2.1
                  have p397_3 := h397c.2.2.2
                  linarith only [h314, hlam, p397_0]
                · have p397_0 := h397c.1
                  have p397_1 := h397c.2.1
                  have p397_2 := h397c.2.2.1
                  have p397_3 := h397c.2.2.2
                  linarith only [hlam, p397_0]
                · have p397_0 := h397c.1
                  have p397_1 := h397c.2.1
                  have p397_2 := h397c.2.2.1
                  have p397_3 := h397c.2.2.2
                  linarith only [h316, hlam, p397_0]
                · have p397_0 := h397c.1
                  have p397_1 := h397c.2.1
                  have p397_2 := h397c.2.2.1
                  have p397_3 := h397c.2.2.2
                  linarith only [h316, h370, hlam, p397_1]
                · have p397_0 := h397c.1
                  have p397_1 := h397c.2.1
                  have p397_2 := h397c.2.2.1
                  have p397_3 := h397c.2.2.2
                  linarith only [h370, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p397_1]
                · have p397_0 := h397c.1
                  have p397_1 := h397c.2.1
                  have p397_2 := h397c.2.2.1
                  have p397_3 := h397c.2.2.2
                  linarith only [h315, hlam, p397_0]
                · have p397_0 := h397c.1
                  have p397_1 := h397c.2.1
                  have p397_2 := h397c.2.2.1
                  have p397_3 := h397c.2.2.2
                  linarith only [h192, h370, hc03, hc45, hlam, hphi, ht34, p397_1]
                · have p397_0 := h397c.1
                  have p397_1 := h397c.2.1
                  have p397_2 := h397c.2.2.1
                  have p397_3 := h397c.2.2.2
                  linarith only [hlam, p397_0]
                · have p397_0 := h397c.1
                  have p397_1 := h397c.2.1
                  have p397_2 := h397c.2.2.1
                  have p397_3 := h397c.2.2.2
                  linarith only [h370, hlam, p397_1]
                · have p397_0 := h397c.1
                  have p397_1 := h397c.2.1
                  have p397_2 := h397c.2.2.1
                  have p397_3 := h397c.2.2.2
                  linarith only [hc01, hlam, hphi, p397_1, u1elo4]
                · have p397_0 := h397c.1
                  have p397_1 := h397c.2.1
                  have p397_2 := h397c.2.2.1
                  have p397_3 := h397c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, p397_1, u1elo4]
                · have p397_0 := h397c.1
                  have p397_1 := h397c.2.1
                  have p397_2 := h397c.2.2.1
                  have p397_3 := h397c.2.2.2
                  linarith only [h192, hc01, hlam, hphi, p397_1, u1elo4]
                · have p397_0 := h397c.1
                  have p397_1 := h397c.2.1
                  have p397_2 := h397c.2.2.1
                  have p397_3 := h397c.2.2.2
                  linarith only [hlam, hphi, ht01, ht0b, ht45, ht5b, p397_1, u1elo4, u4ehi1]
                · have p397_0 := h397c.1
                  have p397_1 := h397c.2.1
                  have p397_2 := h397c.2.2.1
                  have p397_3 := h397c.2.2.2
                  linarith only [hlam, p397_0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h423 | h423
            · linarith only [h314, h315, h423, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h425 | h425
              · rcases h1bigk with h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h0, hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h192, hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h284, hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h286, hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [hc01, hlam, hphi, p426_1, u1elo1]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h192, h315, hc01, hlam, hphi, p426_1, u1elo3]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h315, hlam, p426_1]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h286, h315, hc01, hlam, hphi, p426_1, u1elo3]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [hc01, hlam, hphi, p426_1, u1elo2]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h314, hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h423, hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h286, h423, hc01, hc34, hlam, hphi, ht12, ht23, p426_1]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [hc01, hlam, hphi, p426_1, u1elo3]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, p426_1, u1elo3]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h192, hc01, hlam, hphi, p426_1, u1elo3]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h286, hc01, hlam, hphi, p426_1, u1elo3]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [hc01, hlam, hphi, p426_1, u1elo4]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h192, h314, h425, hc01, hlam, hphi, p426_1, u1elo3]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h192, h425, hc01, hlam, hphi, p426_1, u1elo3]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [h425, hlam, p426_0]
                · have p426_0 := h426c.1
                  have p426_1 := h426c.2.1
                  have p426_2 := h426c.2.2.1
                  have p426_3 := h426c.2.2.2
                  linarith only [hlam, p426_0]
              · rcases h1bigk with h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [hlam, p452_0]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h0, hlam, p452_0]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h192, hlam, p452_0]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h284, hlam, p452_0]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h286, hlam, p452_0]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [hc01, hlam, hphi, p452_1, u1elo1]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [hlam, p452_0]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h192, h315, hc01, hc24, hlam, hphi, ht12, p452_1]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h315, hlam, p452_1]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h286, h315, h425, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p452_1]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [hc01, hlam, hphi, p452_1, u1elo2]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h314, hlam, p452_0]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [hlam, p452_0]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h423, hlam, p452_0]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h314, h315, h425, hlam, p452_1]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h425, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p452_1]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h0, h425, hc02, hc45, hlam, hphi, ht23, ht34, p452_1]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h192, h425, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p452_1]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [hlam, p452_0]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h425, hlam, p452_1]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [hc01, hlam, hphi, p452_1, u1elo4]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h192, h314, hc01, hlam, hphi, p452_1, u1elo4]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [h192, hc01, hlam, hphi, p452_1, u1elo4]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [hlam, hphi, ht01, ht0b, ht45, ht5b, p452_1, u1elo4, u4ehi1]
                · have p452_0 := h452c.1
                  have p452_1 := h452c.2.1
                  have p452_2 := h452c.2.2.1
                  have p452_3 := h452c.2.2.2
                  linarith only [hlam, p452_0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h478 | h478
          · rcases m.htr 1 3 4 (by decide) (by decide) with h479 | h479
            · rcases m.htr 1 4 5 (by decide) (by decide) with h480 | h480
              · rcases h1bigk with h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c
                · have p481_0 := h481c.1
                  have p481_1 := h481c.2.1
                  have p481_2 := h481c.2.2.1
                  have p481_3 := h481c.2.2.2
                  linarith only [hlam, p481_0]
                · have p481_0 := h481c.1
                  have p481_1 := h481c.2.1
                  have p481_2 := h481c.2.2.1
                  have p481_3 := h481c.2.2.2
                  linarith only [h0, hlam, p481_0]
                · have p481_0 := h481c.1
                  have p481_1 := h481c.2.1
                  have p481_2 := h481c.2.2.1
                  have p481_3 := h481c.2.2.2
                  linarith only [h192, hlam, p481_0]
                · have p481_0 := h481c.1
                  have p481_1 := h481c.2.1
                  have p481_2 := h481c.2.2.1
                  have p481_3 := h481c.2.2.2
                  linarith only [h284, hlam, p481_0]
                · have p481_0 := h481c.1
                  have p481_1 := h481c.2.1
                  have p481_2 := h481c.2.2.1
                  have p481_3 := h481c.2.2.2
                  linarith only [h286, hlam, p481_0]
                · have p481_0 := h481c.1
                  have p481_1 := h481c.2.1
                  have p481_2 := h481c.2.2.1
                  have p481_3 := h481c.2.2.2
                  linarith only [hc01, hlam, hphi, p481_1, u1elo1]
                · have p481_0 := h481c.1
                  have p481_1 := h481c.2.1
                  have p481_2 := h481c.2.2.1
                  have p481_3 := h481c.2.2.2
                  linarith only [hlam, p481_0]
                · have p481_0 := h481c.1
                  have p481_1 := h481c.2.1
                  have p481_2 := h481c.2.2.1
                  have p481_3 := h481c.2.2.2
                  linarith only [h314, hlam, p481_1]
                · have p481_0 := h481c.1
                  have p481_1 := h481c.2.1
                  have p481_2 := h481c.2.2.1
                  have p481_3 := h481c.2.2.2
                  linarith only [h314, h480, hlam, hphi, ht01, ht0b, ht45, ht5b, p481_1, u1elo2, u4ehi4]
                · have p481_0 := h481c.1
                  have p481_1 := h481c.2.1
                  have p481_2 := h481c.2.2.1
                  have p481_3 := h481c.2.2.2
                  linarith only [h286, h314, hc01, hlam, hphi, p481_1, u1elo2]
                · have p481_0 := h481c.1
                  have p481_1 := h481c.2.1
                  have p481_2 := h481c.2.2.1
                  have p481_3 := h481c.2.2.2
                  linarith only [hc01, hlam, hphi, p481_1, u1elo2]
                · have p481_0 := h481c.1
                  have p481_1 := h481c.2.1
                  have p481_2 := h481c.2.2.1
                  have p481_3 := h481c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, p481_1, u1elo2]
                · have p481_0 := h481c.1
                  have p481_1 := h481c.2.1
                  have p481_2 := h481c.2.2.1
                  have p481_3 := h481c.2.2.2
                  linarith only [hlam, p481_0]
                · have p481_0 := h481c.1
                  have p481_1 := h481c.2.1
                  have p481_2 := h481c.2.2.1
                  have p481_3 := h481c.2.2.2
                  linarith only [h480, hlam, hphi, ht01, ht0b, ht45, ht5b, p481_1, u1elo2, u4ehi4]
                · have p481_0 := h481c.1
                  have p481_1 := h481c.2.1
                  have p481_2 := h481c.2.2.1
                  have p481_3 := h481c.2.2.2
                  linarith only [h286, hc01, hlam, hphi, p481_1, u1elo2]
                · have p481_0 := h481c.1
                  have p481_1 := h481c.2.1
                  have p481_2 := h481c.2.2.1
                  have p481_3 := h481c.2.2.2
                  linarith only [h478, hc01, hlam, hphi, p481_1, u1elo1]
                · have p481_0 := h481c.1
                  have p481_1 := h481c.2.1
                  have p481_2 := h481c.2.2.1
                  have p481_3 := h481c.2.2.2
                  linarith only [h478, hlam, p481_0]
                · have p481_0 := h481c.1
                  have p481_1 := h481c.2.1
                  have p481_2 := h481c.2.2.1
                  have p481_3 := h481c.2.2.2
                  linarith only [h479, hlam, p481_1]
                · have p481_0 := h481c.1
                  have p481_1 := h481c.2.1
                  have p481_2 := h481c.2.2.1
                  have p481_3 := h481c.2.2.2
                  linarith only [hlam, p481_0]
                · have p481_0 := h481c.1
                  have p481_1 := h481c.2.1
                  have p481_2 := h481c.2.2.1
                  have p481_3 := h481c.2.2.2
                  linarith only [h286, h314, h478, hc01, hc23, hlam, hphi, ht12, p481_1]
                · have p481_0 := h481c.1
                  have p481_1 := h481c.2.1
                  have p481_2 := h481c.2.2.1
                  have p481_3 := h481c.2.2.2
                  linarith only [hc01, hlam, hphi, p481_1, u1elo4]
                · have p481_0 := h481c.1
                  have p481_1 := h481c.2.1
                  have p481_2 := h481c.2.2.1
                  have p481_3 := h481c.2.2.2
                  linarith only [h478, h480, hlam, p481_1]
                · have p481_0 := h481c.1
                  have p481_1 := h481c.2.1
                  have p481_2 := h481c.2.2.1
                  have p481_3 := h481c.2.2.2
                  linarith only [h314, h478, h479, h480, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p481_1, u4ehi3]
                · have p481_0 := h481c.1
                  have p481_1 := h481c.2.1
                  have p481_2 := h481c.2.2.1
                  have p481_3 := h481c.2.2.2
                  linarith only [h480, hlam, p481_0]
                · have p481_0 := h481c.1
                  have p481_1 := h481c.2.1
                  have p481_2 := h481c.2.2.1
                  have p481_3 := h481c.2.2.2
                  linarith only [hlam, p481_0]
              · rcases h1bigk with h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c | h507c
                · have p507_0 := h507c.1
                  have p507_1 := h507c.2.1
                  have p507_2 := h507c.2.2.1
                  have p507_3 := h507c.2.2.2
                  linarith only [hlam, p507_0]
                · have p507_0 := h507c.1
                  have p507_1 := h507c.2.1
                  have p507_2 := h507c.2.2.1
                  have p507_3 := h507c.2.2.2
                  linarith only [h0, hlam, p507_0]
                · have p507_0 := h507c.1
                  have p507_1 := h507c.2.1
                  have p507_2 := h507c.2.2.1
                  have p507_3 := h507c.2.2.2
                  linarith only [h192, hlam, p507_0]
                · have p507_0 := h507c.1
                  have p507_1 := h507c.2.1
                  have p507_2 := h507c.2.2.1
                  have p507_3 := h507c.2.2.2
                  linarith only [h284, hlam, p507_0]
                · have p507_0 := h507c.1
                  have p507_1 := h507c.2.1
                  have p507_2 := h507c.2.2.1
                  have p507_3 := h507c.2.2.2
                  linarith only [h286, hlam, p507_0]
                · have p507_0 := h507c.1
                  have p507_1 := h507c.2.1
                  have p507_2 := h507c.2.2.1
                  have p507_3 := h507c.2.2.2
                  linarith only [h314, hc01, hc23, hlam, hphi, ht12, p507_1]
                · have p507_0 := h507c.1
                  have p507_1 := h507c.2.1
                  have p507_2 := h507c.2.2.1
                  have p507_3 := h507c.2.2.2
                  linarith only [hlam, p507_0]
                · have p507_0 := h507c.1
                  have p507_1 := h507c.2.1
                  have p507_2 := h507c.2.2.1
                  have p507_3 := h507c.2.2.2
                  linarith only [h314, hlam, p507_1]
                · have p507_0 := h507c.1
                  have p507_1 := h507c.2.1
                  have p507_2 := h507c.2.2.1
                  have p507_3 := h507c.2.2.2
                  linarith only [h314, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p507_1, u4ehi1]
                · have p507_0 := h507c.1
                  have p507_1 := h507c.2.1
                  have p507_2 := h507c.2.2.1
                  have p507_3 := h507c.2.2.2
                  linarith only [h286, h314, hc01, hc23, hlam, hphi, ht12, p507_1]
                · have p507_0 := h507c.1
                  have p507_1 := h507c.2.1
                  have p507_2 := h507c.2.2.1
                  have p507_3 := h507c.2.2.2
                  linarith only [hc01, hlam, hphi, p507_1, u1elo2]
                · have p507_0 := h507c.1
                  have p507_1 := h507c.2.1
                  have p507_2 := h507c.2.2.1
                  have p507_3 := h507c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, p507_1, u1elo2]
                · have p507_0 := h507c.1
                  have p507_1 := h507c.2.1
                  have p507_2 := h507c.2.2.1
                  have p507_3 := h507c.2.2.2
                  linarith only [hlam, p507_0]
                · have p507_0 := h507c.1
                  have p507_1 := h507c.2.1
                  have p507_2 := h507c.2.2.1
                  have p507_3 := h507c.2.2.2
                  linarith only [h284, hc01, hlam, hphi, p507_1, u1elo2]
                · have p507_0 := h507c.1
                  have p507_1 := h507c.2.1
                  have p507_2 := h507c.2.2.1
                  have p507_3 := h507c.2.2.2
                  linarith only [h284, h480, hc01, hlam, hphi, p507_1, u1elo2]
                · have p507_0 := h507c.1
                  have p507_1 := h507c.2.1
                  have p507_2 := h507c.2.2.1
                  have p507_3 := h507c.2.2.2
                  linarith only [hc01, hlam, hphi, p507_1, u1elo3]
                · have p507_0 := h507c.1
                  have p507_1 := h507c.2.1
                  have p507_2 := h507c.2.2.1
                  have p507_3 := h507c.2.2.2
                  linarith only [h478, hlam, p507_0]
                · have p507_0 := h507c.1
                  have p507_1 := h507c.2.1
                  have p507_2 := h507c.2.2.1
                  have p507_3 := h507c.2.2.2
                  linarith only [h479, hlam, p507_1]
                · have p507_0 := h507c.1
                  have p507_1 := h507c.2.1
                  have p507_2 := h507c.2.2.1
                  have p507_3 := h507c.2.2.2
                  linarith only [hlam, p507_0]
                · have p507_0 := h507c.1
                  have p507_1 := h507c.2.1
                  have p507_2 := h507c.2.2.1
                  have p507_3 := h507c.2.2.2
                  linarith only [h480, hlam, p507_1]
                · have p507_0 := h507c.1
                  have p507_1 := h507c.2.1
                  have p507_2 := h507c.2.2.1
                  have p507_3 := h507c.2.2.2
                  linarith only [hc01, hlam, hphi, p507_1, u1elo4]
                · have p507_0 := h507c.1
                  have p507_1 := h507c.2.1
                  have p507_2 := h507c.2.2.1
                  have p507_3 := h507c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, p507_1, u1elo4]
                · have p507_0 := h507c.1
                  have p507_1 := h507c.2.1
                  have p507_2 := h507c.2.2.1
                  have p507_3 := h507c.2.2.2
                  linarith only [h192, hc01, hlam, hphi, p507_1, u1elo4]
                · have p507_0 := h507c.1
                  have p507_1 := h507c.2.1
                  have p507_2 := h507c.2.2.1
                  have p507_3 := h507c.2.2.2
                  linarith only [hlam, hphi, ht01, ht0b, ht45, ht5b, p507_1, u1elo4, u4ehi1]
                · have p507_0 := h507c.1
                  have p507_1 := h507c.2.1
                  have p507_2 := h507c.2.2.1
                  have p507_3 := h507c.2.2.2
                  linarith only [hlam, p507_0]
            · linarith only [h314, h478, h479, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h534 | h534
            · rcases m.htr 1 4 5 (by decide) (by decide) with h535 | h535
              · rcases h1bigk with h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c | h536c
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [hlam, p536_0]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [h0, hlam, p536_0]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [h192, hlam, p536_0]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [h284, hlam, p536_0]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [h286, hlam, p536_0]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [hc01, hlam, hphi, p536_1, u1elo1]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [hlam, p536_0]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [h314, hlam, p536_1]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [h478, hlam, p536_1]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [h286, h478, h534, hc01, hlam, hphi, p536_1, u1elo2]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [hc01, hlam, hphi, p536_1, u1elo2]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, p536_1, u1elo2]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [hlam, p536_0]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [hlam, hphi, ht01, ht0b, ht45, ht5b, p536_1, u1elo2, u4ehi1]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [h286, hc01, hlam, hphi, p536_1, u1elo2]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [hc01, hlam, hphi, p536_1, u1elo3]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, p536_1, u1elo3]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [h534, hlam, p536_1]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [hlam, p536_0]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [h286, h534, hc01, hlam, hphi, p536_1, u1elo2]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [hc01, hlam, hphi, p536_1, u1elo4]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [h0, h534, h535, hc01, hlam, hphi, p536_1, u1elo2]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [h534, h535, hlam, p536_1]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [h535, hlam, p536_0]
                · have p536_0 := h536c.1
                  have p536_1 := h536c.2.1
                  have p536_2 := h536c.2.2.1
                  have p536_3 := h536c.2.2.2
                  linarith only [hlam, p536_0]
              · rcases h1bigk with h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c | h562c
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [hlam, p562_0]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h0, hlam, p562_0]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h192, hlam, p562_0]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h284, hlam, p562_0]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h286, hlam, p562_0]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [hc01, hlam, hphi, p562_1, u1elo1]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [hlam, p562_0]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h314, hlam, p562_1]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h478, hlam, p562_1]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h286, h478, h535, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p562_1]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [hc01, hlam, hphi, p562_1, u1elo2]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, p562_1, u1elo2]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [hlam, p562_0]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [hlam, hphi, ht01, ht0b, ht45, ht5b, p562_1, u1elo2, u4ehi1]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h0, h478, h535, hc01, hlam, hphi, p562_1, u1elo2]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [hc01, hlam, hphi, p562_1, u1elo3]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h0, h535, hc01, hlam, hphi, p562_1, u1elo4]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h534, hlam, p562_1]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [hlam, p562_0]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h535, hlam, p562_1]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [hc01, hlam, hphi, p562_1, u1elo4]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, p562_1, u1elo4]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [h534, hlam, hphi, ht01, ht0b, ht45, ht5b, p562_1, u1elo4, u4ehi3]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [hlam, hphi, ht01, ht0b, ht45, ht5b, p562_1, u1elo4, u4ehi1]
                · have p562_0 := h562c.1
                  have p562_1 := h562c.2.1
                  have p562_2 := h562c.2.2.1
                  have p562_3 := h562c.2.2.2
                  linarith only [hlam, p562_0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h588 | h588
              · rcases h1bigk with h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c | h589c
                · have p589_0 := h589c.1
                  have p589_1 := h589c.2.1
                  have p589_2 := h589c.2.2.1
                  have p589_3 := h589c.2.2.2
                  linarith only [hlam, p589_0]
                · have p589_0 := h589c.1
                  have p589_1 := h589c.2.1
                  have p589_2 := h589c.2.2.1
                  have p589_3 := h589c.2.2.2
                  linarith only [h0, hlam, p589_0]
                · have p589_0 := h589c.1
                  have p589_1 := h589c.2.1
                  have p589_2 := h589c.2.2.1
                  have p589_3 := h589c.2.2.2
                  linarith only [h192, hlam, p589_0]
                · have p589_0 := h589c.1
                  have p589_1 := h589c.2.1
                  have p589_2 := h589c.2.2.1
                  have p589_3 := h589c.2.2.2
                  linarith only [h284, hlam, p589_0]
                · have p589_0 := h589c.1
                  have p589_1 := h589c.2.1
                  have p589_2 := h589c.2.2.1
                  have p589_3 := h589c.2.2.2
                  linarith only [h286, hlam, p589_0]
                · have p589_0 := h589c.1
                  have p589_1 := h589c.2.1
                  have p589_2 := h589c.2.2.1
                  have p589_3 := h589c.2.2.2
                  linarith only [hc01, hlam, hphi, p589_1, u1elo1]
                · have p589_0 := h589c.1
                  have p589_1 := h589c.2.1
                  have p589_2 := h589c.2.2.1
                  have p589_3 := h589c.2.2.2
                  linarith only [hlam, p589_0]
                · have p589_0 := h589c.1
                  have p589_1 := h589c.2.1
                  have p589_2 := h589c.2.2.1
                  have p589_3 := h589c.2.2.2
                  linarith only [h314, hlam, p589_1]
                · have p589_0 := h589c.1
                  have p589_1 := h589c.2.1
                  have p589_2 := h589c.2.2.1
                  have p589_3 := h589c.2.2.2
                  linarith only [h478, hlam, p589_1]
                · have p589_0 := h589c.1
                  have p589_1 := h589c.2.1
                  have p589_2 := h589c.2.2.1
                  have p589_3 := h589c.2.2.2
                  linarith only [h286, hc01, hlam, hphi, p589_1, u1elo1]
                · have p589_0 := h589c.1
                  have p589_1 := h589c.2.1
                  have p589_2 := h589c.2.2.1
                  have p589_3 := h589c.2.2.2
                  linarith only [h534, hc01, hc34, hlam, hphi, ht12, ht23, p589_1]
                · have p589_0 := h589c.1
                  have p589_1 := h589c.2.1
                  have p589_2 := h589c.2.2.1
                  have p589_3 := h589c.2.2.2
                  linarith only [h534, hc12, hc34, hlam, hphi, ht23, p589_1]
                · have p589_0 := h589c.1
                  have p589_1 := h589c.2.1
                  have p589_2 := h589c.2.2.1
                  have p589_3 := h589c.2.2.2
                  linarith only [hlam, p589_0]
                · have p589_0 := h589c.1
                  have p589_1 := h589c.2.1
                  have p589_2 := h589c.2.2.1
                  have p589_3 := h589c.2.2.2
                  linarith only [h534, hlam, p589_0]
                · have p589_0 := h589c.1
                  have p589_1 := h589c.2.1
                  have p589_2 := h589c.2.2.1
                  have p589_3 := h589c.2.2.2
                  linarith only [h286, h534, hc01, hc34, hlam, hphi, ht12, ht23, p589_1]
                · have p589_0 := h589c.1
                  have p589_1 := h589c.2.1
                  have p589_2 := h589c.2.2.1
                  have p589_3 := h589c.2.2.2
                  linarith only [hc01, hlam, hphi, p589_1, u1elo3]
                · have p589_0 := h589c.1
                  have p589_1 := h589c.2.1
                  have p589_2 := h589c.2.2.1
                  have p589_3 := h589c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, p589_1, u1elo3]
                · have p589_0 := h589c.1
                  have p589_1 := h589c.2.1
                  have p589_2 := h589c.2.2.1
                  have p589_3 := h589c.2.2.2
                  linarith only [h192, hc01, hlam, hphi, p589_1, u1elo3]
                · have p589_0 := h589c.1
                  have p589_1 := h589c.2.1
                  have p589_2 := h589c.2.2.1
                  have p589_3 := h589c.2.2.2
                  linarith only [hlam, p589_0]
                · have p589_0 := h589c.1
                  have p589_1 := h589c.2.1
                  have p589_2 := h589c.2.2.1
                  have p589_3 := h589c.2.2.2
                  linarith only [h286, hc01, hlam, hphi, p589_1, u1elo3]
                · have p589_0 := h589c.1
                  have p589_1 := h589c.2.1
                  have p589_2 := h589c.2.2.1
                  have p589_3 := h589c.2.2.2
                  linarith only [hc01, hlam, hphi, p589_1, u1elo4]
                · have p589_0 := h589c.1
                  have p589_1 := h589c.2.1
                  have p589_2 := h589c.2.2.1
                  have p589_3 := h589c.2.2.2
                  linarith only [h0, h588, hc01, hlam, hphi, p589_1, u1elo3]
                · have p589_0 := h589c.1
                  have p589_1 := h589c.2.1
                  have p589_2 := h589c.2.2.1
                  have p589_3 := h589c.2.2.2
                  linarith only [h0, h314, h588, hc01, hlam, hphi, p589_1, u1elo3]
                · have p589_0 := h589c.1
                  have p589_1 := h589c.2.1
                  have p589_2 := h589c.2.2.1
                  have p589_3 := h589c.2.2.2
                  linarith only [h588, hlam, p589_0]
                · have p589_0 := h589c.1
                  have p589_1 := h589c.2.1
                  have p589_2 := h589c.2.2.1
                  have p589_3 := h589c.2.2.2
                  linarith only [hlam, p589_0]
              · rcases h1bigk with h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c | h615c
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [hlam, p615_0]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [h0, hlam, p615_0]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [h192, hlam, p615_0]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [h284, hlam, p615_0]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [h286, hlam, p615_0]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [hc01, hlam, hphi, p615_1, u1elo1]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [hlam, p615_0]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [h314, hlam, p615_1]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [h478, hlam, p615_1]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [h286, h314, h534, h588, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p615_1]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [h534, h588, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p615_1]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [h534, h588, hc12, hc45, hlam, hphi, ht23, ht34, p615_1]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [hlam, p615_0]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [h534, hlam, p615_0]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [h534, h588, hlam, p615_1]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [h588, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p615_1]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [h0, h588, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p615_1]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [h588, hc13, hc45, hlam, hphi, ht34, p615_1]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [hlam, p615_0]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [h588, hlam, p615_1]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [hc01, hlam, hphi, p615_1, u1elo4]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [h0, hc01, hlam, hphi, p615_1, u1elo4]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [h0, h314, hc01, hlam, hphi, p615_1, u1elo4]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [hlam, hphi, ht01, ht0b, ht45, ht5b, p615_1, u1elo4, u4ehi1]
                · have p615_0 := h615c.1
                  have p615_1 := h615c.2.1
                  have p615_2 := h615c.2.2.1
                  have p615_3 := h615c.2.2.2
                  linarith only [hlam, p615_0]

theorem r1l7_21_14_M_LI_L_R (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h4ehi := hb4.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_21_14_M_LI_L_R_x0 m hb1 hb4 h0
  · exact r1l7_21_14_M_LI_L_R_x1 m hb1 hb4 h0

end R2N4
