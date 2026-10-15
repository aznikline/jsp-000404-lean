import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_3S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 17338000 in
set_option maxHeartbeats 17338000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s4 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_11_13_25_L_I_L_I_H_I_s5 m hb1 hb3 hb5 h0 h1 h2 h3 h4 h5
  · rcases m.htr 0 2 5 (by decide) (by decide) with h8201 | h8201
    · rcases m.htr 0 3 4 (by decide) (by decide) with h8202 | h8202
      · linarith only [h4, h5, h8202, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h8204 | h8204
        · rcases m.htr 0 4 5 (by decide) (by decide) with h8205 | h8205
          · rcases m.htr 1 2 3 (by decide) (by decide) with h8206 | h8206
            · rcases m.htr 1 2 4 (by decide) (by decide) with h8207 | h8207
              · linarith only [h0, h5, h8207, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h8209 | h8209
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8210 | h8210
                  · linarith only [h1, h8202, h8210, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h8212 | h8212
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h8213 | h8213
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8214 | h8214
                        · linarith only [h0, h5, h8202, h8206, h8214, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h8216 | h8216
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h8217 | h8217
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h8218 | h8218
                              · rcases h1bigk with h8219c | h8219c | h8219c | h8219c | h8219c | h8219c | h8219c | h8219c | h8219c | h8219c | h8219c | h8219c | h8219c | h8219c | h8219c | h8219c | h8219c | h8219c | h8219c | h8219c | h8219c | h8219c | h8219c | h8219c | h8219c
                                · have p8219_0 := h8219c.1
                                  have p8219_1 := h8219c.2.1
                                  have p8219_2 := h8219c.2.2.1
                                  have p8219_3 := h8219c.2.2.2
                                  linarith only [hlam, p8219_0]
                                · have p8219_0 := h8219c.1
                                  have p8219_1 := h8219c.2.1
                                  have p8219_2 := h8219c.2.2.1
                                  have p8219_3 := h8219c.2.2.2
                                  linarith only [h8206, h8216, h8218, hc01, hc45, hlam, hphi, ht0b, ht5b, p8219_1]
                                · have p8219_0 := h8219c.1
                                  have p8219_1 := h8219c.2.1
                                  have p8219_2 := h8219c.2.2.1
                                  have p8219_3 := h8219c.2.2.2
                                  rcases p8219_3 (m.d 0 1) (by simp) with h8222 | h8222
                                  · rcases p8219_3 (m.d 1 2) (by simp) with h8223 | h8223
                                    · linarith only [h0, h8223, hlam]
                                    · linarith only [h8206, h8223, hlam]
                                  · linarith only [h8222, hlam, p8219_0]
                                · have p8219_0 := h8219c.1
                                  have p8219_1 := h8219c.2.1
                                  have p8219_2 := h8219c.2.2.1
                                  have p8219_3 := h8219c.2.2.2
                                  linarith only [h8206, h8207, h8216, h8218, hc01, hc45, hlam, hphi, ht0b, ht5b, p8219_1]
                                · have p8219_0 := h8219c.1
                                  have p8219_1 := h8219c.2.1
                                  have p8219_2 := h8219c.2.2.1
                                  have p8219_3 := h8219c.2.2.2
                                  rcases p8219_3 (m.d 0 1) (by simp) with h8228 | h8228
                                  · rcases p8219_3 (m.d 1 2) (by simp) with h8229 | h8229
                                    · linarith only [h0, h8229, hlam]
                                    · linarith only [h8209, h8229, hlam]
                                  · linarith only [h8228, hlam, p8219_0]
                                · have p8219_0 := h8219c.1
                                  have p8219_1 := h8219c.2.1
                                  have p8219_2 := h8219c.2.2.1
                                  have p8219_3 := h8219c.2.2.2
                                  linarith only [h0, hlam, p8219_0]
                                · have p8219_0 := h8219c.1
                                  have p8219_1 := h8219c.2.1
                                  have p8219_2 := h8219c.2.2.1
                                  have p8219_3 := h8219c.2.2.2
                                  linarith only [hlam, p8219_0]
                                · have p8219_0 := h8219c.1
                                  have p8219_1 := h8219c.2.1
                                  have p8219_2 := h8219c.2.2.1
                                  have p8219_3 := h8219c.2.2.2
                                  linarith only [h0, h8206, h8216, h8218, hc01, hc45, hlam, hphi, ht0b, ht5b, p8219_1]
                                · have p8219_0 := h8219c.1
                                  have p8219_1 := h8219c.2.1
                                  have p8219_2 := h8219c.2.2.1
                                  have p8219_3 := h8219c.2.2.2
                                  linarith only [h8207, hlam, p8219_0]
                                · have p8219_0 := h8219c.1
                                  have p8219_1 := h8219c.2.1
                                  have p8219_2 := h8219c.2.2.1
                                  have p8219_3 := h8219c.2.2.2
                                  rcases p8219_3 (m.d 0 1) (by simp) with h8237 | h8237
                                  · rcases p8219_3 (m.d 1 2) (by simp) with h8238 | h8238
                                    · rcases p8219_3 (m.d 1 3) (by simp) with h8239 | h8239
                                      · linarith only [h8206, h8239, hlam]
                                      · linarith only [h8212, h8239, hlam]
                                    · linarith only [h8209, h8238, hlam]
                                  · linarith only [h3, h8237, hlam]
                                · have p8219_0 := h8219c.1
                                  have p8219_1 := h8219c.2.1
                                  have p8219_2 := h8219c.2.2.1
                                  have p8219_3 := h8219c.2.2.2
                                  linarith only [h1, hlam, p8219_0]
                                · have p8219_0 := h8219c.1
                                  have p8219_1 := h8219c.2.1
                                  have p8219_2 := h8219c.2.2.1
                                  have p8219_3 := h8219c.2.2.2
                                  linarith only [h8206, hlam, p8219_1]
                                · have p8219_0 := h8219c.1
                                  have p8219_1 := h8219c.2.1
                                  have p8219_2 := h8219c.2.2.1
                                  have p8219_3 := h8219c.2.2.2
                                  linarith only [hlam, p8219_0]
                                · have p8219_0 := h8219c.1
                                  have p8219_1 := h8219c.2.1
                                  have p8219_2 := h8219c.2.2.1
                                  have p8219_3 := h8219c.2.2.2
                                  linarith only [h8210, hlam, p8219_1]
                                · have p8219_0 := h8219c.1
                                  have p8219_1 := h8219c.2.1
                                  have p8219_2 := h8219c.2.2.1
                                  have p8219_3 := h8219c.2.2.2
                                  rcases p8219_3 (m.d 0 1) (by simp) with h8248 | h8248
                                  · rcases p8219_3 (m.d 1 2) (by simp) with h8249 | h8249
                                    · rcases p8219_3 (m.d 1 3) (by simp) with h8250 | h8250
                                      · rcases p8219_3 (m.d 1 4) (by simp) with h8251 | h8251
                                        · rcases p8219_3 (m.d 1 5) (by simp) with h8252 | h8252
                                          · linarith only [h8212, h8252, hlam]
                                          · rcases h3bigk with h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c | h8254c
                                            · have p8254_0 := h8254c.1
                                              have p8254_1 := h8254c.2.1
                                              have p8254_2 := h8254c.2.2.1
                                              have p8254_3 := h8254c.2.2.2
                                              linarith only [hlam, p8254_0]
                                            · have p8254_0 := h8254c.1
                                              have p8254_1 := h8254c.2.1
                                              have p8254_2 := h8254c.2.2.1
                                              have p8254_3 := h8254c.2.2.2
                                              linarith only [h8209, h8216, h8218, hc03, hc45, hlam, hphi, ht0b, ht5b, p8219_1, p8254_1]
                                            · have p8254_0 := h8254c.1
                                              have p8254_1 := h8254c.2.1
                                              have p8254_2 := h8254c.2.2.1
                                              have p8254_3 := h8254c.2.2.2
                                              linarith only [h4, h5, h8214, h8216, h8218, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8254_1]
                                            · have p8254_0 := h8254c.1
                                              have p8254_1 := h8254c.2.1
                                              have p8254_2 := h8254c.2.2.1
                                              have p8254_3 := h8254c.2.2.2
                                              linarith only [h8202, hlam, p8254_0]
                                            · have p8254_0 := h8254c.1
                                              have p8254_1 := h8254c.2.1
                                              have p8254_2 := h8254c.2.2.1
                                              have p8254_3 := h8254c.2.2.2
                                              rcases p8254_3 (m.d 0 3) (by simp) with h8259 | h8259
                                              · rcases p8254_3 (m.d 1 3) (by simp) with h8260 | h8260
                                                · linarith only [h1, h8260, hlam]
                                                · linarith only [h8212, h8260, hlam]
                                              · linarith only [h8259, hlam, p8254_0]
                                            · have p8254_0 := h8254c.1
                                              have p8254_1 := h8254c.2.1
                                              have p8254_2 := h8254c.2.2.1
                                              have p8254_3 := h8254c.2.2.2
                                              linarith only [h1, hlam, p8254_0]
                                            · have p8254_0 := h8254c.1
                                              have p8254_1 := h8254c.2.1
                                              have p8254_2 := h8254c.2.2.1
                                              have p8254_3 := h8254c.2.2.2
                                              linarith only [hlam, p8254_0]
                                            · have p8254_0 := h8254c.1
                                              have p8254_1 := h8254c.2.1
                                              have p8254_2 := h8254c.2.2.1
                                              have p8254_3 := h8254c.2.2.2
                                              linarith only [h1, h8216, h8218, hc01, hc45, hlam, hphi, ht0b, ht5b, p8254_1]
                                            · have p8254_0 := h8254c.1
                                              have p8254_1 := h8254c.2.1
                                              have p8254_2 := h8254c.2.2.1
                                              have p8254_3 := h8254c.2.2.2
                                              linarith only [h8210, hlam, p8254_0]
                                            · have p8254_0 := h8254c.1
                                              have p8254_1 := h8254c.2.1
                                              have p8254_2 := h8254c.2.2.1
                                              have p8254_3 := h8254c.2.2.2
                                              rcases p8254_3 (m.d 0 3) (by simp) with h8268 | h8268
                                              · rcases p8254_3 (m.d 1 3) (by simp) with h8269 | h8269
                                                · rcases p8254_3 (m.d 2 3) (by simp) with h8270 | h8270
                                                  · linarith only [h8206, h8270, hlam]
                                                  · linarith only [h8216, h8270, hlam]
                                                · linarith only [h8269, hlam, p8254_0]
                                              · linarith only [h8204, h8268, hlam]
                                            · have p8254_0 := h8254c.1
                                              have p8254_1 := h8254c.2.1
                                              have p8254_2 := h8254c.2.2.1
                                              have p8254_3 := h8254c.2.2.2
                                              linarith only [h4, hlam, p8254_0]
                                            · have p8254_0 := h8254c.1
                                              have p8254_1 := h8254c.2.1
                                              have p8254_2 := h8254c.2.2.1
                                              have p8254_3 := h8254c.2.2.2
                                              linarith only [h8206, hlam, p8254_0]
                                            · have p8254_0 := h8254c.1
                                              have p8254_1 := h8254c.2.1
                                              have p8254_2 := h8254c.2.2.1
                                              have p8254_3 := h8254c.2.2.2
                                              linarith only [hlam, p8254_0]
                                            · have p8254_0 := h8254c.1
                                              have p8254_1 := h8254c.2.1
                                              have p8254_2 := h8254c.2.2.1
                                              have p8254_3 := h8254c.2.2.2
                                              linarith only [h8214, hlam, p8254_0]
                                            · have p8254_0 := h8254c.1
                                              have p8254_1 := h8254c.2.1
                                              have p8254_2 := h8254c.2.2.1
                                              have p8254_3 := h8254c.2.2.2
                                              linarith only [h4, h5, h8214, h8218, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8254_1]
                                            · have p8254_0 := h8254c.1
                                              have p8254_1 := h8254c.2.1
                                              have p8254_2 := h8254c.2.2.1
                                              have p8254_3 := h8254c.2.2.2
                                              linarith only [h1, h8209, h8216, h8218, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8219_1, p8254_1]
                                            · have p8254_0 := h8254c.1
                                              have p8254_1 := h8254c.2.1
                                              have p8254_2 := h8254c.2.2.1
                                              have p8254_3 := h8254c.2.2.2
                                              linarith only [h8209, h8216, h8218, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8219_1, p8254_1]
                                            · have p8254_0 := h8254c.1
                                              have p8254_1 := h8254c.2.1
                                              have p8254_2 := h8254c.2.2.1
                                              have p8254_3 := h8254c.2.2.2
                                              rcases p8254_3 (m.d 0 3) (by simp) with h8282 | h8282
                                              · linarith only [h8202, h8282, hlam]
                                              · linarith only [h4, h8282, hlam]
                                            · have p8254_0 := h8254c.1
                                              have p8254_1 := h8254c.2.1
                                              have p8254_2 := h8254c.2.2.1
                                              have p8254_3 := h8254c.2.2.2
                                              linarith only [hlam, p8254_0]
                                            · have p8254_0 := h8254c.1
                                              have p8254_1 := h8254c.2.1
                                              have p8254_2 := h8254c.2.2.1
                                              have p8254_3 := h8254c.2.2.2
                                              linarith only [h1, h4, h5, h8209, h8214, h8216, hlam, p8219_1, p8254_2]
                                            · have p8254_0 := h8254c.1
                                              have p8254_1 := h8254c.2.1
                                              have p8254_2 := h8254c.2.2.1
                                              have p8254_3 := h8254c.2.2.2
                                              linarith only [h8204, hlam, p8254_0]
                                            · have p8254_0 := h8254c.1
                                              have p8254_1 := h8254c.2.1
                                              have p8254_2 := h8254c.2.2.1
                                              have p8254_3 := h8254c.2.2.2
                                              linarith only [h8212, hlam, p8254_0]
                                            · have p8254_0 := h8254c.1
                                              have p8254_1 := h8254c.2.1
                                              have p8254_2 := h8254c.2.2.1
                                              have p8254_3 := h8254c.2.2.2
                                              linarith only [h8216, hlam, p8254_0]
                                            · have p8254_0 := h8254c.1
                                              have p8254_1 := h8254c.2.1
                                              have p8254_2 := h8254c.2.2.1
                                              have p8254_3 := h8254c.2.2.2
                                              linarith only [h8218, hlam, p8254_0]
                                            · have p8254_0 := h8254c.1
                                              have p8254_1 := h8254c.2.1
                                              have p8254_2 := h8254c.2.2.1
                                              have p8254_3 := h8254c.2.2.2
                                              linarith only [hlam, p8254_0]
                                        · linarith only [h8213, h8251, hlam]
                                      · linarith only [h8212, h8250, hlam]
                                    · linarith only [h8209, h8249, hlam]
                                  · linarith only [h3, h8248, hlam]
                                · have p8219_0 := h8219c.1
                                  have p8219_1 := h8219c.2.1
                                  have p8219_2 := h8219c.2.2.1
                                  have p8219_3 := h8219c.2.2.2
                                  linarith only [h2, hlam, p8219_0]
                                · have p8219_0 := h8219c.1
                                  have p8219_1 := h8219c.2.1
                                  have p8219_2 := h8219c.2.2.1
                                  have p8219_3 := h8219c.2.2.2
                                  linarith only [h2, h8206, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8219_1]
                                · have p8219_0 := h8219c.1
                                  have p8219_1 := h8219c.2.1
                                  have p8219_2 := h8219c.2.2.1
                                  have p8219_3 := h8219c.2.2.2
                                  linarith only [h2, h8212, hc01, hc35, hlam, hphi, ht0b, ht5b, p8219_1]
                                · have p8219_0 := h8219c.1
                                  have p8219_1 := h8219c.2.1
                                  have p8219_2 := h8219c.2.2.1
                                  have p8219_3 := h8219c.2.2.2
                                  linarith only [hlam, p8219_0]
                                · have p8219_0 := h8219c.1
                                  have p8219_1 := h8219c.2.1
                                  have p8219_2 := h8219c.2.2.1
                                  have p8219_3 := h8219c.2.2.2
                                  rcases p8219_3 (m.d 0 1) (by simp) with h8300 | h8300
                                  · rcases p8219_3 (m.d 1 2) (by simp) with h8301 | h8301
                                    · linarith only [h8207, h8301, hlam]
                                    · linarith only [h8209, h8301, hlam]
                                  · linarith only [h3, h8300, hlam]
                                · have p8219_0 := h8219c.1
                                  have p8219_1 := h8219c.2.1
                                  have p8219_2 := h8219c.2.2.1
                                  have p8219_3 := h8219c.2.2.2
                                  linarith only [h3, hlam, p8219_0]
                                · have p8219_0 := h8219c.1
                                  have p8219_1 := h8219c.2.1
                                  have p8219_2 := h8219c.2.2.1
                                  have p8219_3 := h8219c.2.2.2
                                  linarith only [h8209, hlam, p8219_1]
                                · have p8219_0 := h8219c.1
                                  have p8219_1 := h8219c.2.1
                                  have p8219_2 := h8219c.2.2.1
                                  have p8219_3 := h8219c.2.2.2
                                  linarith only [h8212, hlam, p8219_0]
                                · have p8219_0 := h8219c.1
                                  have p8219_1 := h8219c.2.1
                                  have p8219_2 := h8219c.2.2.1
                                  have p8219_3 := h8219c.2.2.2
                                  linarith only [h8213, hlam, p8219_0]
                                · have p8219_0 := h8219c.1
                                  have p8219_1 := h8219c.2.1
                                  have p8219_2 := h8219c.2.2.1
                                  have p8219_3 := h8219c.2.2.2
                                  linarith only [hlam, p8219_0]
                              · linarith only [h0, h5, h8206, h8214, h8216, h8218, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                            · linarith only [h0, h5, h8206, h8216, h8217, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h4, h5, h8204, h8214, h8216, hc23, hc34, hlam, hphi]
                      · linarith only [h8202, h8204, h8205, h8206, h8207, h8213, hc23, hc34, hlam, hphi]
                    · linarith only [h8202, h8204, h8212, hc13, hc34, hlam, hphi]
                · linarith only [h5, h8201, h8206, h8209, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · linarith only [h4, h5, h8206, hc12, hc24, hlam, hphi]
          · linarith only [h4, h5, h8204, h8205, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h8318 | h8318
          · rcases m.htr 1 2 3 (by decide) (by decide) with h8319 | h8319
            · rcases m.htr 1 2 4 (by decide) (by decide) with h8320 | h8320
              · linarith only [h0, h5, h8201, h8320, hc01, hc25, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h8322 | h8322
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8323 | h8323
                  · linarith only [h1, h8202, h8323, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h8325 | h8325
                    · linarith only [h1, h8204, h8325, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h8327 | h8327
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8328 | h8328
                        · linarith only [h0, h5, h8202, h8319, h8328, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h8330 | h8330
                          · linarith only [h1, h8204, h8319, h8330, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h8332 | h8332
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h8333 | h8333
                              · rcases h1bigk with h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c | h8334c
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [hlam, p8334_0]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  rcases p8334_3 (m.d 0 1) (by simp) with h8336 | h8336
                                  · rcases p8334_3 (m.d 1 2) (by simp) with h8337 | h8337
                                    · linarith only [h8337, hlam, p8334_0]
                                    · rcases p8334_3 (m.d 1 3) (by simp) with h8339 | h8339
                                      · linarith only [h1, h8339, hlam]
                                      · rcases p8334_3 (m.d 1 4) (by simp) with h8341 | h8341
                                        · linarith only [h2, h8341, hlam]
                                        · linarith only [h8320, h8341, hlam]
                                  · linarith only [h8336, hlam, p8334_0]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  rcases p8334_3 (m.d 0 1) (by simp) with h8345 | h8345
                                  · rcases p8334_3 (m.d 1 2) (by simp) with h8346 | h8346
                                    · linarith only [h0, h8346, hlam]
                                    · linarith only [h8319, h8346, hlam]
                                  · linarith only [h8345, hlam, p8334_0]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  rcases p8334_3 (m.d 0 1) (by simp) with h8350 | h8350
                                  · rcases p8334_3 (m.d 1 2) (by simp) with h8351 | h8351
                                    · linarith only [h0, h8351, hlam]
                                    · rcases p8334_3 (m.d 1 3) (by simp) with h8353 | h8353
                                      · linarith only [h1, h8353, hlam]
                                      · rcases p8334_3 (m.d 1 4) (by simp) with h8355 | h8355
                                        · linarith only [h8355, hlam, p8334_0]
                                        · rcases p8334_3 (m.d 1 5) (by simp) with h8357 | h8357
                                          · linarith only [h3, h8357, hlam]
                                          · rcases h3bigk with h8359c | h8359c | h8359c | h8359c | h8359c | h8359c | h8359c | h8359c | h8359c | h8359c | h8359c | h8359c | h8359c | h8359c | h8359c | h8359c | h8359c | h8359c | h8359c | h8359c | h8359c | h8359c | h8359c | h8359c | h8359c
                                            · have p8359_0 := h8359c.1
                                              have p8359_1 := h8359c.2.1
                                              have p8359_2 := h8359c.2.2.1
                                              have p8359_3 := h8359c.2.2.2
                                              linarith only [hlam, p8359_0]
                                            · have p8359_0 := h8359c.1
                                              have p8359_1 := h8359c.2.1
                                              have p8359_2 := h8359c.2.2.1
                                              have p8359_3 := h8359c.2.2.2
                                              linarith only [h8204, h8319, hc23, hc35, hlam, hphi, p8359_1]
                                            · have p8359_0 := h8359c.1
                                              have p8359_1 := h8359c.2.1
                                              have p8359_2 := h8359c.2.2.1
                                              have p8359_3 := h8359c.2.2.2
                                              linarith only [h4, h5, h8328, hc23, hc34, hlam, hphi, p8359_1]
                                            · have p8359_0 := h8359c.1
                                              have p8359_1 := h8359c.2.1
                                              have p8359_2 := h8359c.2.2.1
                                              have p8359_3 := h8359c.2.2.2
                                              linarith only [h8202, hlam, p8359_0]
                                            · have p8359_0 := h8359c.1
                                              have p8359_1 := h8359c.2.1
                                              have p8359_2 := h8359c.2.2.1
                                              have p8359_3 := h8359c.2.2.2
                                              linarith only [h8204, hlam, p8359_0]
                                            · have p8359_0 := h8359c.1
                                              have p8359_1 := h8359c.2.1
                                              have p8359_2 := h8359c.2.2.1
                                              have p8359_3 := h8359c.2.2.2
                                              linarith only [h1, hlam, p8359_0]
                                            · have p8359_0 := h8359c.1
                                              have p8359_1 := h8359c.2.1
                                              have p8359_2 := h8359c.2.2.1
                                              have p8359_3 := h8359c.2.2.2
                                              linarith only [hlam, p8359_0]
                                            · have p8359_0 := h8359c.1
                                              have p8359_1 := h8359c.2.1
                                              have p8359_2 := h8359c.2.2.1
                                              have p8359_3 := h8359c.2.2.2
                                              linarith only [h1, h4, h5, h8328, hc23, hc34, hlam, hphi, p8359_1]
                                            · have p8359_0 := h8359c.1
                                              have p8359_1 := h8359c.2.1
                                              have p8359_2 := h8359c.2.2.1
                                              have p8359_3 := h8359c.2.2.2
                                              linarith only [h8323, hlam, p8359_0]
                                            · have p8359_0 := h8359c.1
                                              have p8359_1 := h8359c.2.1
                                              have p8359_2 := h8359c.2.2.1
                                              have p8359_3 := h8359c.2.2.2
                                              linarith only [h8325, hlam, p8359_0]
                                            · have p8359_0 := h8359c.1
                                              have p8359_1 := h8359c.2.1
                                              have p8359_2 := h8359c.2.2.1
                                              have p8359_3 := h8359c.2.2.2
                                              linarith only [h4, hlam, p8359_0]
                                            · have p8359_0 := h8359c.1
                                              have p8359_1 := h8359c.2.1
                                              have p8359_2 := h8359c.2.2.1
                                              have p8359_3 := h8359c.2.2.2
                                              linarith only [h8319, hlam, p8359_0]
                                            · have p8359_0 := h8359c.1
                                              have p8359_1 := h8359c.2.1
                                              have p8359_2 := h8359c.2.2.1
                                              have p8359_3 := h8359c.2.2.2
                                              linarith only [hlam, p8359_0]
                                            · have p8359_0 := h8359c.1
                                              have p8359_1 := h8359c.2.1
                                              have p8359_2 := h8359c.2.2.1
                                              have p8359_3 := h8359c.2.2.2
                                              linarith only [h8328, hlam, p8359_0]
                                            · have p8359_0 := h8359c.1
                                              have p8359_1 := h8359c.2.1
                                              have p8359_2 := h8359c.2.2.1
                                              have p8359_3 := h8359c.2.2.2
                                              linarith only [h8330, hlam, p8359_0]
                                            · have p8359_0 := h8359c.1
                                              have p8359_1 := h8359c.2.1
                                              have p8359_2 := h8359c.2.2.1
                                              have p8359_3 := h8359c.2.2.2
                                              rcases p8359_3 (m.d 0 3) (by simp) with h8375 | h8375
                                              · linarith only [h8375, hlam, p8359_0]
                                              · rcases p8359_3 (m.d 1 3) (by simp) with h8377 | h8377
                                                · linarith only [h8323, h8377, hlam]
                                                · rcases p8359_3 (m.d 2 3) (by simp) with h8379 | h8379
                                                  · linarith only [h8328, h8379, hlam]
                                                  · rcases p8359_3 (m.d 3 4) (by simp) with h8381 | h8381
                                                    · rcases p8359_3 (m.d 3 5) (by simp) with h8382 | h8382
                                                      · linarith only [h8333, h8382, hlam]
                                                      · linarith only [h8204, h8382, hlam]
                                                    · linarith only [h8381, hlam, p8359_0]
                                            · have p8359_0 := h8359c.1
                                              have p8359_1 := h8359c.2.1
                                              have p8359_2 := h8359c.2.2.1
                                              have p8359_3 := h8359c.2.2.2
                                              rcases p8359_3 (m.d 0 3) (by simp) with h8386 | h8386
                                              · linarith only [h8202, h8386, hlam]
                                              · linarith only [h1, h8386, hlam]
                                            · have p8359_0 := h8359c.1
                                              have p8359_1 := h8359c.2.1
                                              have p8359_2 := h8359c.2.2.1
                                              have p8359_3 := h8359c.2.2.2
                                              rcases p8359_3 (m.d 0 3) (by simp) with h8389 | h8389
                                              · linarith only [h8202, h8389, hlam]
                                              · linarith only [h4, h8389, hlam]
                                            · have p8359_0 := h8359c.1
                                              have p8359_1 := h8359c.2.1
                                              have p8359_2 := h8359c.2.2.1
                                              have p8359_3 := h8359c.2.2.2
                                              linarith only [hlam, p8359_0]
                                            · have p8359_0 := h8359c.1
                                              have p8359_1 := h8359c.2.1
                                              have p8359_2 := h8359c.2.2.1
                                              have p8359_3 := h8359c.2.2.2
                                              linarith only [h8204, hc03, hc34, hlam, hphi, p8359_1]
                                            · have p8359_0 := h8359c.1
                                              have p8359_1 := h8359c.2.1
                                              have p8359_2 := h8359c.2.2.1
                                              have p8359_3 := h8359c.2.2.2
                                              rcases p8359_3 (m.d 0 3) (by simp) with h8394 | h8394
                                              · linarith only [h8394, hlam, p8359_0]
                                              · rcases p8359_3 (m.d 1 3) (by simp) with h8396 | h8396
                                                · linarith only [h8325, h8396, hlam]
                                                · rcases p8359_3 (m.d 2 3) (by simp) with h8398 | h8398
                                                  · linarith only [h8330, h8398, hlam]
                                                  · rcases p8359_3 (m.d 3 4) (by simp) with h8400 | h8400
                                                    · rcases p8359_3 (m.d 3 5) (by simp) with h8401 | h8401
                                                      · rcases h5bigk with h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c
                                                        · have p8402_0 := h8402c.1
                                                          have p8402_1 := h8402c.2.1
                                                          have p8402_2 := h8402c.2.2.1
                                                          have p8402_3 := h8402c.2.2.2
                                                          linarith only [hlam, p8402_0]
                                                        · have p8402_0 := h8402c.1
                                                          have p8402_1 := h8402c.2.1
                                                          have p8402_2 := h8402c.2.2.1
                                                          have p8402_3 := h8402c.2.2.2
                                                          linarith only [h5, h8201, h8328, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8402_1]
                                                        · have p8402_0 := h8402c.1
                                                          have p8402_1 := h8402c.2.1
                                                          have p8402_2 := h8402c.2.2.1
                                                          have p8402_3 := h8402c.2.2.2
                                                          linarith only [h5, h8201, h8328, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8402_1]
                                                        · have p8402_0 := h8402c.1
                                                          have p8402_1 := h8402c.2.1
                                                          have p8402_2 := h8402c.2.2.1
                                                          have p8402_3 := h8402c.2.2.2
                                                          linarith only [h8204, hlam, p8402_1]
                                                        · have p8402_0 := h8402c.1
                                                          have p8402_1 := h8402c.2.1
                                                          have p8402_2 := h8402c.2.2.1
                                                          have p8402_3 := h8402c.2.2.2
                                                          linarith only [h5, h8201, h8328, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8402_1]
                                                        · have p8402_0 := h8402c.1
                                                          have p8402_1 := h8402c.2.1
                                                          have p8402_2 := h8402c.2.2.1
                                                          have p8402_3 := h8402c.2.2.2
                                                          linarith only [h3, hlam, p8402_0]
                                                        · have p8402_0 := h8402c.1
                                                          have p8402_1 := h8402c.2.1
                                                          have p8402_2 := h8402c.2.2.1
                                                          have p8402_3 := h8402c.2.2.2
                                                          linarith only [hlam, p8402_0]
                                                        · have p8402_0 := h8402c.1
                                                          have p8402_1 := h8402c.2.1
                                                          have p8402_2 := h8402c.2.2.1
                                                          have p8402_3 := h8402c.2.2.2
                                                          linarith only [h3, h8332, hc01, hc45, hlam, hphi, ht0b, ht5b, p8402_1]
                                                        · have p8402_0 := h8402c.1
                                                          have p8402_1 := h8402c.2.1
                                                          have p8402_2 := h8402c.2.2.1
                                                          have p8402_3 := h8402c.2.2.2
                                                          linarith only [h8325, hlam, p8402_1]
                                                        · have p8402_0 := h8402c.1
                                                          have p8402_1 := h8402c.2.1
                                                          have p8402_2 := h8402c.2.2.1
                                                          have p8402_3 := h8402c.2.2.2
                                                          linarith only [h8320, h8322, hc01, hc45, hlam, hphi, ht0b, ht5b, p8334_1, p8402_1]
                                                        · have p8402_0 := h8402c.1
                                                          have p8402_1 := h8402c.2.1
                                                          have p8402_2 := h8402c.2.2.1
                                                          have p8402_3 := h8402c.2.2.2
                                                          linarith only [h8201, hlam, p8402_1]
                                                        · have p8402_0 := h8402c.1
                                                          have p8402_1 := h8402c.2.1
                                                          have p8402_2 := h8402c.2.2.1
                                                          have p8402_3 := h8402c.2.2.2
                                                          linarith only [h8322, hlam, p8402_1]
                                                        · have p8402_0 := h8402c.1
                                                          have p8402_1 := h8402c.2.1
                                                          have p8402_2 := h8402c.2.2.1
                                                          have p8402_3 := h8402c.2.2.2
                                                          linarith only [hlam, p8402_0]
                                                        · have p8402_0 := h8402c.1
                                                          have p8402_1 := h8402c.2.1
                                                          have p8402_2 := h8402c.2.2.1
                                                          have p8402_3 := h8402c.2.2.2
                                                          linarith only [h8330, hlam, p8402_1]
                                                        · have p8402_0 := h8402c.1
                                                          have p8402_1 := h8402c.2.1
                                                          have p8402_2 := h8402c.2.2.1
                                                          have p8402_3 := h8402c.2.2.2
                                                          linarith only [h5, h8201, h8328, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8402_1]
                                                        · have p8402_0 := h8402c.1
                                                          have p8402_1 := h8402c.2.1
                                                          have p8402_2 := h8402c.2.2.1
                                                          have p8402_3 := h8402c.2.2.2
                                                          linarith only [h1, h8204, h8319, hc23, hc35, hlam, hphi, p8402_1]
                                                        · have p8402_0 := h8402c.1
                                                          have p8402_1 := h8402c.2.1
                                                          have p8402_2 := h8402c.2.2.1
                                                          have p8402_3 := h8402c.2.2.2
                                                          linarith only [h8319, h8325, hc23, hc35, hlam, hphi, p8402_1]
                                                        · have p8402_0 := h8402c.1
                                                          have p8402_1 := h8402c.2.1
                                                          have p8402_2 := h8402c.2.2.1
                                                          have p8402_3 := h8402c.2.2.2
                                                          linarith only [h8330, hc23, hc35, hlam, hphi, p8402_1]
                                                        · have p8402_0 := h8402c.1
                                                          have p8402_1 := h8402c.2.1
                                                          have p8402_2 := h8402c.2.2.1
                                                          have p8402_3 := h8402c.2.2.2
                                                          linarith only [hlam, p8402_0]
                                                        · have p8402_0 := h8402c.1
                                                          have p8402_1 := h8402c.2.1
                                                          have p8402_2 := h8402c.2.2.1
                                                          have p8402_3 := h8402c.2.2.2
                                                          rcases p8402_3 (m.d 0 5) (by simp) with h8422 | h8422
                                                          · linarith only [h8204, h8422, hlam]
                                                          · linarith only [h8318, h8422, hlam]
                                                        · have p8402_0 := h8402c.1
                                                          have p8402_1 := h8402c.2.1
                                                          have p8402_2 := h8402c.2.2.1
                                                          have p8402_3 := h8402c.2.2.2
                                                          linarith only [h8318, hlam, p8402_0]
                                                        · have p8402_0 := h8402c.1
                                                          have p8402_1 := h8402c.2.1
                                                          have p8402_2 := h8402c.2.2.1
                                                          have p8402_3 := h8402c.2.2.2
                                                          linarith only [h8327, hlam, p8402_0]
                                                        · have p8402_0 := h8402c.1
                                                          have p8402_1 := h8402c.2.1
                                                          have p8402_2 := h8402c.2.2.1
                                                          have p8402_3 := h8402c.2.2.2
                                                          linarith only [h8332, hlam, p8402_0]
                                                        · have p8402_0 := h8402c.1
                                                          have p8402_1 := h8402c.2.1
                                                          have p8402_2 := h8402c.2.2.1
                                                          have p8402_3 := h8402c.2.2.2
                                                          linarith only [h8333, hlam, p8402_0]
                                                        · have p8402_0 := h8402c.1
                                                          have p8402_1 := h8402c.2.1
                                                          have p8402_2 := h8402c.2.2.1
                                                          have p8402_3 := h8402c.2.2.2
                                                          linarith only [hlam, p8402_0]
                                                      · linarith only [h8401, hlam, p8359_0]
                                                    · linarith only [h8202, h8400, hlam]
                                            · have p8359_0 := h8359c.1
                                              have p8359_1 := h8359c.2.1
                                              have p8359_2 := h8359c.2.2.1
                                              have p8359_3 := h8359c.2.2.2
                                              rcases p8359_3 (m.d 0 3) (by simp) with h8432 | h8432
                                              · linarith only [h8204, h8432, hlam]
                                              · linarith only [h1, h8432, hlam]
                                            · have p8359_0 := h8359c.1
                                              have p8359_1 := h8359c.2.1
                                              have p8359_2 := h8359c.2.2.1
                                              have p8359_3 := h8359c.2.2.2
                                              rcases p8359_3 (m.d 0 3) (by simp) with h8435 | h8435
                                              · linarith only [h8204, h8435, hlam]
                                              · linarith only [h4, h8435, hlam]
                                            · have p8359_0 := h8359c.1
                                              have p8359_1 := h8359c.2.1
                                              have p8359_2 := h8359c.2.2.1
                                              have p8359_3 := h8359c.2.2.2
                                              linarith only [h8333, hlam, p8359_0]
                                            · have p8359_0 := h8359c.1
                                              have p8359_1 := h8359c.2.1
                                              have p8359_2 := h8359c.2.2.1
                                              have p8359_3 := h8359c.2.2.2
                                              linarith only [hlam, p8359_0]
                                  · linarith only [h8350, hlam, p8334_0]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  rcases p8334_3 (m.d 0 1) (by simp) with h8441 | h8441
                                  · rcases p8334_3 (m.d 1 2) (by simp) with h8442 | h8442
                                    · linarith only [h0, h8442, hlam]
                                    · linarith only [h8322, h8442, hlam]
                                  · linarith only [h8441, hlam, p8334_0]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h0, hlam, p8334_0]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [hlam, p8334_0]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h0, h5, h8319, h8328, hc23, hc34, hlam, hphi, p8334_1]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h8320, hlam, p8334_0]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h0, h5, h8322, h8328, h8330, hc23, hc34, hlam, hphi, p8334_1]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h1, hlam, p8334_0]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h8319, hlam, p8334_1]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [hlam, p8334_0]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h8323, hlam, p8334_1]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h8325, hlam, p8334_1]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h2, hlam, p8334_0]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h2, h8319, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8334_1]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  rcases p8334_3 (m.d 0 1) (by simp) with h8458 | h8458
                                  · rcases p8334_3 (m.d 1 2) (by simp) with h8459 | h8459
                                    · linarith only [h8320, h8459, hlam]
                                    · linarith only [h8319, h8459, hlam]
                                  · linarith only [h1, h8458, hlam]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [hlam, p8334_0]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  rcases p8334_3 (m.d 0 1) (by simp) with h8464 | h8464
                                  · rcases p8334_3 (m.d 1 2) (by simp) with h8465 | h8465
                                    · linarith only [h8320, h8465, hlam]
                                    · linarith only [h8322, h8465, hlam]
                                  · linarith only [h3, h8464, hlam]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h3, hlam, p8334_0]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h8322, hlam, p8334_1]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h3, h5, h8201, h8319, h8328, hc23, hc34, hlam, hphi, p8334_1]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [h8327, hlam, p8334_0]
                                · have p8334_0 := h8334c.1
                                  have p8334_1 := h8334c.2.1
                                  have p8334_2 := h8334c.2.2.1
                                  have p8334_3 := h8334c.2.2.2
                                  linarith only [hlam, p8334_0]
                              · linarith only [h0, h5, h8322, h8328, h8330, h8333, hc23, hc45, hlam, hphi, ht34]
                            · linarith only [h0, h5, h8322, h8327, h8332, hlam]
                      · linarith only [h8202, h8318, h8319, h8320, h8327, hc23, hc34, hlam, hphi]
                · linarith only [h5, h8201, h8319, h8322, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · linarith only [h4, h5, h8319, hc12, hc24, hlam, hphi]
          · linarith only [h5, h8201, h8318, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h8480 | h8480
      · linarith only [h4, h5, h8480, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h8482 | h8482
        · linarith only [h4, h8201, h8482, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h8484 | h8484
          · rcases m.htr 1 2 3 (by decide) (by decide) with h8485 | h8485
            · rcases m.htr 1 2 4 (by decide) (by decide) with h8486 | h8486
              · linarith only [h0, h5, h8486, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h8488 | h8488
                · linarith only [h0, h8201, h8488, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8490 | h8490
                  · linarith only [h1, h8480, h8490, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h8492 | h8492
                    · linarith only [h1, h8482, h8492, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h8494 | h8494
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8495 | h8495
                        · linarith only [h0, h1, h5, h8480, h8485, h8495, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h8497 | h8497
                          · linarith only [h4, h8201, h8482, h8497, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h8499 | h8499
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h8500 | h8500
                              · rcases h1bigk with h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c | h8501c
                                · have p8501_0 := h8501c.1
                                  have p8501_1 := h8501c.2.1
                                  have p8501_2 := h8501c.2.2.1
                                  have p8501_3 := h8501c.2.2.2
                                  linarith only [hlam, p8501_0]
                                · have p8501_0 := h8501c.1
                                  have p8501_1 := h8501c.2.1
                                  have p8501_2 := h8501c.2.2.1
                                  have p8501_3 := h8501c.2.2.2
                                  rcases p8501_3 (m.d 0 1) (by simp) with h8503 | h8503
                                  · rcases p8501_3 (m.d 1 2) (by simp) with h8504 | h8504
                                    · linarith only [h8504, hlam, p8501_0]
                                    · rcases p8501_3 (m.d 1 3) (by simp) with h8506 | h8506
                                      · linarith only [h1, h8506, hlam]
                                      · rcases p8501_3 (m.d 1 4) (by simp) with h8508 | h8508
                                        · linarith only [h2, h8508, hlam]
                                        · linarith only [h8486, h8508, hlam]
                                  · linarith only [h8503, hlam, p8501_0]
                                · have p8501_0 := h8501c.1
                                  have p8501_1 := h8501c.2.1
                                  have p8501_2 := h8501c.2.2.1
                                  have p8501_3 := h8501c.2.2.2
                                  rcases p8501_3 (m.d 0 1) (by simp) with h8512 | h8512
                                  · rcases p8501_3 (m.d 1 2) (by simp) with h8513 | h8513
                                    · linarith only [h0, h8513, hlam]
                                    · linarith only [h8485, h8513, hlam]
                                  · linarith only [h8512, hlam, p8501_0]
                                · have p8501_0 := h8501c.1
                                  have p8501_1 := h8501c.2.1
                                  have p8501_2 := h8501c.2.2.1
                                  have p8501_3 := h8501c.2.2.2
                                  rcases p8501_3 (m.d 0 1) (by simp) with h8517 | h8517
                                  · rcases p8501_3 (m.d 1 2) (by simp) with h8518 | h8518
                                    · linarith only [h0, h8518, hlam]
                                    · rcases p8501_3 (m.d 1 3) (by simp) with h8520 | h8520
                                      · linarith only [h1, h8520, hlam]
                                      · rcases p8501_3 (m.d 1 4) (by simp) with h8522 | h8522
                                        · linarith only [h8522, hlam, p8501_0]
                                        · rcases p8501_3 (m.d 1 5) (by simp) with h8524 | h8524
                                          · linarith only [h3, h8524, hlam]
                                          · rcases h3bigk with h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c | h8526c
                                            · have p8526_0 := h8526c.1
                                              have p8526_1 := h8526c.2.1
                                              have p8526_2 := h8526c.2.2.1
                                              have p8526_3 := h8526c.2.2.2
                                              linarith only [hlam, p8526_0]
                                            · have p8526_0 := h8526c.1
                                              have p8526_1 := h8526c.2.1
                                              have p8526_2 := h8526c.2.2.1
                                              have p8526_3 := h8526c.2.2.2
                                              linarith only [h4, h8201, h8495, h8499, hc13, hc34, hlam, hphi, p8526_1]
                                            · have p8526_0 := h8526c.1
                                              have p8526_1 := h8526c.2.1
                                              have p8526_2 := h8526c.2.2.1
                                              have p8526_3 := h8526c.2.2.2
                                              linarith only [h4, h8201, h8495, h8499, hc23, hc34, hlam, hphi, p8526_1]
                                            · have p8526_0 := h8526c.1
                                              have p8526_1 := h8526c.2.1
                                              have p8526_2 := h8526c.2.2.1
                                              have p8526_3 := h8526c.2.2.2
                                              linarith only [h8480, hlam, p8526_0]
                                            · have p8526_0 := h8526c.1
                                              have p8526_1 := h8526c.2.1
                                              have p8526_2 := h8526c.2.2.1
                                              have p8526_3 := h8526c.2.2.2
                                              linarith only [h8482, hlam, p8526_0]
                                            · have p8526_0 := h8526c.1
                                              have p8526_1 := h8526c.2.1
                                              have p8526_2 := h8526c.2.2.1
                                              have p8526_3 := h8526c.2.2.2
                                              linarith only [h1, hlam, p8526_0]
                                            · have p8526_0 := h8526c.1
                                              have p8526_1 := h8526c.2.1
                                              have p8526_2 := h8526c.2.2.1
                                              have p8526_3 := h8526c.2.2.2
                                              linarith only [hlam, p8526_0]
                                            · have p8526_0 := h8526c.1
                                              have p8526_1 := h8526c.2.1
                                              have p8526_2 := h8526c.2.2.1
                                              have p8526_3 := h8526c.2.2.2
                                              linarith only [h1, h4, h8201, h8495, h8499, hc23, hc34, hlam, hphi, p8526_1]
                                            · have p8526_0 := h8526c.1
                                              have p8526_1 := h8526c.2.1
                                              have p8526_2 := h8526c.2.2.1
                                              have p8526_3 := h8526c.2.2.2
                                              linarith only [h8490, hlam, p8526_0]
                                            · have p8526_0 := h8526c.1
                                              have p8526_1 := h8526c.2.1
                                              have p8526_2 := h8526c.2.2.1
                                              have p8526_3 := h8526c.2.2.2
                                              linarith only [h8492, hlam, p8526_0]
                                            · have p8526_0 := h8526c.1
                                              have p8526_1 := h8526c.2.1
                                              have p8526_2 := h8526c.2.2.1
                                              have p8526_3 := h8526c.2.2.2
                                              linarith only [h4, hlam, p8526_0]
                                            · have p8526_0 := h8526c.1
                                              have p8526_1 := h8526c.2.1
                                              have p8526_2 := h8526c.2.2.1
                                              have p8526_3 := h8526c.2.2.2
                                              linarith only [h8485, hlam, p8526_0]
                                            · have p8526_0 := h8526c.1
                                              have p8526_1 := h8526c.2.1
                                              have p8526_2 := h8526c.2.2.1
                                              have p8526_3 := h8526c.2.2.2
                                              linarith only [hlam, p8526_0]
                                            · have p8526_0 := h8526c.1
                                              have p8526_1 := h8526c.2.1
                                              have p8526_2 := h8526c.2.2.1
                                              have p8526_3 := h8526c.2.2.2
                                              linarith only [h8495, hlam, p8526_0]
                                            · have p8526_0 := h8526c.1
                                              have p8526_1 := h8526c.2.1
                                              have p8526_2 := h8526c.2.2.1
                                              have p8526_3 := h8526c.2.2.2
                                              linarith only [h8497, hlam, p8526_0]
                                            · have p8526_0 := h8526c.1
                                              have p8526_1 := h8526c.2.1
                                              have p8526_2 := h8526c.2.2.1
                                              have p8526_3 := h8526c.2.2.2
                                              rcases p8526_3 (m.d 0 3) (by simp) with h8542 | h8542
                                              · linarith only [h8542, hlam, p8526_0]
                                              · rcases p8526_3 (m.d 1 3) (by simp) with h8544 | h8544
                                                · linarith only [h8490, h8544, hlam]
                                                · rcases p8526_3 (m.d 2 3) (by simp) with h8546 | h8546
                                                  · linarith only [h8495, h8546, hlam]
                                                  · rcases p8526_3 (m.d 3 4) (by simp) with h8548 | h8548
                                                    · rcases p8526_3 (m.d 3 5) (by simp) with h8549 | h8549
                                                      · linarith only [h8500, h8549, hlam]
                                                      · linarith only [h8482, h8549, hlam]
                                                    · linarith only [h8548, hlam, p8526_0]
                                            · have p8526_0 := h8526c.1
                                              have p8526_1 := h8526c.2.1
                                              have p8526_2 := h8526c.2.2.1
                                              have p8526_3 := h8526c.2.2.2
                                              rcases p8526_3 (m.d 0 3) (by simp) with h8553 | h8553
                                              · linarith only [h8480, h8553, hlam]
                                              · linarith only [h1, h8553, hlam]
                                            · have p8526_0 := h8526c.1
                                              have p8526_1 := h8526c.2.1
                                              have p8526_2 := h8526c.2.2.1
                                              have p8526_3 := h8526c.2.2.2
                                              rcases p8526_3 (m.d 0 3) (by simp) with h8556 | h8556
                                              · linarith only [h8480, h8556, hlam]
                                              · linarith only [h4, h8556, hlam]
                                            · have p8526_0 := h8526c.1
                                              have p8526_1 := h8526c.2.1
                                              have p8526_2 := h8526c.2.2.1
                                              have p8526_3 := h8526c.2.2.2
                                              linarith only [hlam, p8526_0]
                                            · have p8526_0 := h8526c.1
                                              have p8526_1 := h8526c.2.1
                                              have p8526_2 := h8526c.2.2.1
                                              have p8526_3 := h8526c.2.2.2
                                              linarith only [h8201, h8497, hc02, hc34, hlam, hphi, ht23, p8526_1]
                                            · have p8526_0 := h8526c.1
                                              have p8526_1 := h8526c.2.1
                                              have p8526_2 := h8526c.2.2.1
                                              have p8526_3 := h8526c.2.2.2
                                              rcases p8526_3 (m.d 0 3) (by simp) with h8561 | h8561
                                              · linarith only [h8561, hlam, p8526_0]
                                              · rcases p8526_3 (m.d 1 3) (by simp) with h8563 | h8563
                                                · linarith only [h8492, h8563, hlam]
                                                · rcases p8526_3 (m.d 2 3) (by simp) with h8565 | h8565
                                                  · linarith only [h8497, h8565, hlam]
                                                  · rcases p8526_3 (m.d 3 4) (by simp) with h8567 | h8567
                                                    · rcases p8526_3 (m.d 3 5) (by simp) with h8568 | h8568
                                                      · rcases h5bigk with h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c | h8569c
                                                        · have p8569_0 := h8569c.1
                                                          have p8569_1 := h8569c.2.1
                                                          have p8569_2 := h8569c.2.2.1
                                                          have p8569_3 := h8569c.2.2.2
                                                          linarith only [hlam, p8569_0]
                                                        · have p8569_0 := h8569c.1
                                                          have p8569_1 := h8569c.2.1
                                                          have p8569_2 := h8569c.2.2.1
                                                          have p8569_3 := h8569c.2.2.2
                                                          linarith only [h5, h8484, h8485, h8488, h8495, hc23, hc34, hlam, hphi, p8569_1]
                                                        · have p8569_0 := h8569c.1
                                                          have p8569_1 := h8569c.2.1
                                                          have p8569_2 := h8569c.2.2.1
                                                          have p8569_3 := h8569c.2.2.2
                                                          linarith only [h8201, hlam, p8569_0]
                                                        · have p8569_0 := h8569c.1
                                                          have p8569_1 := h8569c.2.1
                                                          have p8569_2 := h8569c.2.2.1
                                                          have p8569_3 := h8569c.2.2.2
                                                          linarith only [h8482, hlam, p8569_1]
                                                        · have p8569_0 := h8569c.1
                                                          have p8569_1 := h8569c.2.1
                                                          have p8569_2 := h8569c.2.2.1
                                                          have p8569_3 := h8569c.2.2.2
                                                          rcases p8569_3 (m.d 0 5) (by simp) with h8574 | h8574
                                                          · rcases p8569_3 (m.d 1 5) (by simp) with h8575 | h8575
                                                            · linarith only [h3, h8575, hlam]
                                                            · linarith only [h8494, h8575, hlam]
                                                          · linarith only [h8484, h8574, hlam]
                                                        · have p8569_0 := h8569c.1
                                                          have p8569_1 := h8569c.2.1
                                                          have p8569_2 := h8569c.2.2.1
                                                          have p8569_3 := h8569c.2.2.2
                                                          linarith only [h3, hlam, p8569_0]
                                                        · have p8569_0 := h8569c.1
                                                          have p8569_1 := h8569c.2.1
                                                          have p8569_2 := h8569c.2.2.1
                                                          have p8569_3 := h8569c.2.2.2
                                                          linarith only [hlam, p8569_0]
                                                        · have p8569_0 := h8569c.1
                                                          have p8569_1 := h8569c.2.1
                                                          have p8569_2 := h8569c.2.2.1
                                                          have p8569_3 := h8569c.2.2.2
                                                          linarith only [h8488, hlam, p8569_0]
                                                        · have p8569_0 := h8569c.1
                                                          have p8569_1 := h8569c.2.1
                                                          have p8569_2 := h8569c.2.2.1
                                                          have p8569_3 := h8569c.2.2.2
                                                          linarith only [h8492, hlam, p8569_1]
                                                        · have p8569_0 := h8569c.1
                                                          have p8569_1 := h8569c.2.1
                                                          have p8569_2 := h8569c.2.2.1
                                                          have p8569_3 := h8569c.2.2.2
                                                          linarith only [h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p8569_1]
                                                        · have p8569_0 := h8569c.1
                                                          have p8569_1 := h8569c.2.1
                                                          have p8569_2 := h8569c.2.2.1
                                                          have p8569_3 := h8569c.2.2.2
                                                          linarith only [h8201, h8497, hc02, hc35, hlam, hphi, ht23, p8569_1]
                                                        · have p8569_0 := h8569c.1
                                                          have p8569_1 := h8569c.2.1
                                                          have p8569_2 := h8569c.2.2.1
                                                          have p8569_3 := h8569c.2.2.2
                                                          linarith only [h8485, h8488, h8497, hc23, hc35, hlam, hphi, p8569_1]
                                                        · have p8569_0 := h8569c.1
                                                          have p8569_1 := h8569c.2.1
                                                          have p8569_2 := h8569c.2.2.1
                                                          have p8569_3 := h8569c.2.2.2
                                                          linarith only [hlam, p8569_0]
                                                        · have p8569_0 := h8569c.1
                                                          have p8569_1 := h8569c.2.1
                                                          have p8569_2 := h8569c.2.2.1
                                                          have p8569_3 := h8569c.2.2.2
                                                          linarith only [h8497, hlam, p8569_1]
                                                        · have p8569_0 := h8569c.1
                                                          have p8569_1 := h8569c.2.1
                                                          have p8569_2 := h8569c.2.2.1
                                                          have p8569_3 := h8569c.2.2.2
                                                          rcases p8569_3 (m.d 0 5) (by simp) with h8588 | h8588
                                                          · linarith only [h8201, h8588, hlam]
                                                          · linarith only [h8484, h8588, hlam]
                                                        · have p8569_0 := h8569c.1
                                                          have p8569_1 := h8569c.2.1
                                                          have p8569_2 := h8569c.2.2.1
                                                          have p8569_3 := h8569c.2.2.2
                                                          linarith only [h0, h8201, h8485, h8500, hc23, hc34, hlam, hphi, p8569_1]
                                                        · have p8569_0 := h8569c.1
                                                          have p8569_1 := h8569c.2.1
                                                          have p8569_2 := h8569c.2.2.1
                                                          have p8569_3 := h8569c.2.2.2
                                                          linarith only [h8485, h8488, h8500, hc23, hc34, hlam, hphi, p8569_1]
                                                        · have p8569_0 := h8569c.1
                                                          have p8569_1 := h8569c.2.1
                                                          have p8569_2 := h8569c.2.2.1
                                                          have p8569_3 := h8569c.2.2.2
                                                          linarith only [h0, h8201, h8485, h8500, hc23, hc34, hlam, hphi, p8569_1]
                                                        · have p8569_0 := h8569c.1
                                                          have p8569_1 := h8569c.2.1
                                                          have p8569_2 := h8569c.2.2.1
                                                          have p8569_3 := h8569c.2.2.2
                                                          linarith only [hlam, p8569_0]
                                                        · have p8569_0 := h8569c.1
                                                          have p8569_1 := h8569c.2.1
                                                          have p8569_2 := h8569c.2.2.1
                                                          have p8569_3 := h8569c.2.2.2
                                                          rcases p8569_3 (m.d 0 5) (by simp) with h8595 | h8595
                                                          · linarith only [h8482, h8595, hlam]
                                                          · linarith only [h8484, h8595, hlam]
                                                        · have p8569_0 := h8569c.1
                                                          have p8569_1 := h8569c.2.1
                                                          have p8569_2 := h8569c.2.2.1
                                                          have p8569_3 := h8569c.2.2.2
                                                          linarith only [h8484, hlam, p8569_0]
                                                        · have p8569_0 := h8569c.1
                                                          have p8569_1 := h8569c.2.1
                                                          have p8569_2 := h8569c.2.2.1
                                                          have p8569_3 := h8569c.2.2.2
                                                          linarith only [h8494, hlam, p8569_0]
                                                        · have p8569_0 := h8569c.1
                                                          have p8569_1 := h8569c.2.1
                                                          have p8569_2 := h8569c.2.2.1
                                                          have p8569_3 := h8569c.2.2.2
                                                          linarith only [h8499, hlam, p8569_0]
                                                        · have p8569_0 := h8569c.1
                                                          have p8569_1 := h8569c.2.1
                                                          have p8569_2 := h8569c.2.2.1
                                                          have p8569_3 := h8569c.2.2.2
                                                          linarith only [h8500, hlam, p8569_0]
                                                        · have p8569_0 := h8569c.1
                                                          have p8569_1 := h8569c.2.1
                                                          have p8569_2 := h8569c.2.2.1
                                                          have p8569_3 := h8569c.2.2.2
                                                          linarith only [hlam, p8569_0]
                                                      · linarith only [h8568, hlam, p8526_0]
                                                    · linarith only [h8480, h8567, hlam]
                                            · have p8526_0 := h8526c.1
                                              have p8526_1 := h8526c.2.1
                                              have p8526_2 := h8526c.2.2.1
                                              have p8526_3 := h8526c.2.2.2
                                              rcases p8526_3 (m.d 0 3) (by simp) with h8605 | h8605
                                              · linarith only [h8482, h8605, hlam]
                                              · linarith only [h1, h8605, hlam]
                                            · have p8526_0 := h8526c.1
                                              have p8526_1 := h8526c.2.1
                                              have p8526_2 := h8526c.2.2.1
                                              have p8526_3 := h8526c.2.2.2
                                              rcases p8526_3 (m.d 0 3) (by simp) with h8608 | h8608
                                              · linarith only [h8482, h8608, hlam]
                                              · linarith only [h4, h8608, hlam]
                                            · have p8526_0 := h8526c.1
                                              have p8526_1 := h8526c.2.1
                                              have p8526_2 := h8526c.2.2.1
                                              have p8526_3 := h8526c.2.2.2
                                              linarith only [h8500, hlam, p8526_0]
                                            · have p8526_0 := h8526c.1
                                              have p8526_1 := h8526c.2.1
                                              have p8526_2 := h8526c.2.2.1
                                              have p8526_3 := h8526c.2.2.2
                                              linarith only [hlam, p8526_0]
                                  · linarith only [h8517, hlam, p8501_0]
                                · have p8501_0 := h8501c.1
                                  have p8501_1 := h8501c.2.1
                                  have p8501_2 := h8501c.2.2.1
                                  have p8501_3 := h8501c.2.2.2
                                  rcases p8501_3 (m.d 0 1) (by simp) with h8614 | h8614
                                  · rcases p8501_3 (m.d 1 2) (by simp) with h8615 | h8615
                                    · linarith only [h0, h8615, hlam]
                                    · rcases p8501_3 (m.d 1 3) (by simp) with h8617 | h8617
                                      · linarith only [h1, h8617, hlam]
                                      · rcases p8501_3 (m.d 1 4) (by simp) with h8619 | h8619
                                        · linarith only [h2, h8619, hlam]
                                        · linarith only [h8494, h8619, hlam]
                                  · linarith only [h8614, hlam, p8501_0]
                                · have p8501_0 := h8501c.1
                                  have p8501_1 := h8501c.2.1
                                  have p8501_2 := h8501c.2.2.1
                                  have p8501_3 := h8501c.2.2.2
                                  linarith only [h0, hlam, p8501_0]
                                · have p8501_0 := h8501c.1
                                  have p8501_1 := h8501c.2.1
                                  have p8501_2 := h8501c.2.2.1
                                  have p8501_3 := h8501c.2.2.2
                                  linarith only [hlam, p8501_0]
                                · have p8501_0 := h8501c.1
                                  have p8501_1 := h8501c.2.1
                                  have p8501_2 := h8501c.2.2.1
                                  have p8501_3 := h8501c.2.2.2
                                  linarith only [h0, h5, h8495, hc13, hc34, hlam, hphi, p8501_1]
                                · have p8501_0 := h8501c.1
                                  have p8501_1 := h8501c.2.1
                                  have p8501_2 := h8501c.2.2.1
                                  have p8501_3 := h8501c.2.2.2
                                  linarith only [h8486, hlam, p8501_0]
                                · have p8501_0 := h8501c.1
                                  have p8501_1 := h8501c.2.1
                                  have p8501_2 := h8501c.2.2.1
                                  have p8501_3 := h8501c.2.2.2
                                  linarith only [h8488, hlam, p8501_0]
                                · have p8501_0 := h8501c.1
                                  have p8501_1 := h8501c.2.1
                                  have p8501_2 := h8501c.2.2.1
                                  have p8501_3 := h8501c.2.2.2
                                  linarith only [h1, hlam, p8501_0]
                                · have p8501_0 := h8501c.1
                                  have p8501_1 := h8501c.2.1
                                  have p8501_2 := h8501c.2.2.1
                                  have p8501_3 := h8501c.2.2.2
                                  linarith only [h8485, hlam, p8501_1]
                                · have p8501_0 := h8501c.1
                                  have p8501_1 := h8501c.2.1
                                  have p8501_2 := h8501c.2.2.1
                                  have p8501_3 := h8501c.2.2.2
                                  linarith only [hlam, p8501_0]
                                · have p8501_0 := h8501c.1
                                  have p8501_1 := h8501c.2.1
                                  have p8501_2 := h8501c.2.2.1
                                  have p8501_3 := h8501c.2.2.2
                                  linarith only [h8490, hlam, p8501_1]
                                · have p8501_0 := h8501c.1
                                  have p8501_1 := h8501c.2.1
                                  have p8501_2 := h8501c.2.2.1
                                  have p8501_3 := h8501c.2.2.2
                                  linarith only [h8492, hlam, p8501_1]
                                · have p8501_0 := h8501c.1
                                  have p8501_1 := h8501c.2.1
                                  have p8501_2 := h8501c.2.2.1
                                  have p8501_3 := h8501c.2.2.2
                                  linarith only [h2, hlam, p8501_0]
                                · have p8501_0 := h8501c.1
                                  have p8501_1 := h8501c.2.1
                                  have p8501_2 := h8501c.2.2.1
                                  have p8501_3 := h8501c.2.2.2
                                  linarith only [h2, h8485, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8501_1]
                                · have p8501_0 := h8501c.1
                                  have p8501_1 := h8501c.2.1
                                  have p8501_2 := h8501c.2.2.1
                                  have p8501_3 := h8501c.2.2.2
                                  rcases p8501_3 (m.d 0 1) (by simp) with h8635 | h8635
                                  · rcases p8501_3 (m.d 1 2) (by simp) with h8636 | h8636
                                    · linarith only [h8486, h8636, hlam]
                                    · linarith only [h8485, h8636, hlam]
                                  · linarith only [h1, h8635, hlam]
                                · have p8501_0 := h8501c.1
                                  have p8501_1 := h8501c.2.1
                                  have p8501_2 := h8501c.2.2.1
                                  have p8501_3 := h8501c.2.2.2
                                  linarith only [hlam, p8501_0]
                                · have p8501_0 := h8501c.1
                                  have p8501_1 := h8501c.2.1
                                  have p8501_2 := h8501c.2.2.1
                                  have p8501_3 := h8501c.2.2.2
                                  linarith only [h2, h8485, h8488, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8501_1]
                                · have p8501_0 := h8501c.1
                                  have p8501_1 := h8501c.2.1
                                  have p8501_2 := h8501c.2.2.1
                                  have p8501_3 := h8501c.2.2.2
                                  linarith only [h3, hlam, p8501_0]
                                · have p8501_0 := h8501c.1
                                  have p8501_1 := h8501c.2.1
                                  have p8501_2 := h8501c.2.2.1
                                  have p8501_3 := h8501c.2.2.2
                                  linarith only [h3, h8485, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p8501_1]
                                · have p8501_0 := h8501c.1
                                  have p8501_1 := h8501c.2.1
                                  have p8501_2 := h8501c.2.2.1
                                  have p8501_3 := h8501c.2.2.2
                                  rcases p8501_3 (m.d 0 1) (by simp) with h8644 | h8644
                                  · rcases p8501_3 (m.d 1 2) (by simp) with h8645 | h8645
                                    · linarith only [h8488, h8645, hlam]
                                    · linarith only [h8485, h8645, hlam]
                                  · linarith only [h1, h8644, hlam]
                                · have p8501_0 := h8501c.1
                                  have p8501_1 := h8501c.2.1
                                  have p8501_2 := h8501c.2.2.1
                                  have p8501_3 := h8501c.2.2.2
                                  linarith only [h8494, hlam, p8501_0]
                                · have p8501_0 := h8501c.1
                                  have p8501_1 := h8501c.2.1
                                  have p8501_2 := h8501c.2.2.1
                                  have p8501_3 := h8501c.2.2.2
                                  linarith only [hlam, p8501_0]
                              · linarith only [h0, h8201, h8485, h8495, h8499, h8500, hc23, hc45, hlam, hphi, ht34]
                            · linarith only [h2, h5, h8494, h8499, hlam]
                      · linarith only [h8480, h8484, h8485, h8486, h8494, hc23, hc34, hlam, hphi]
            · linarith only [h4, h5, h8485, hc12, hc24, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h8655 | h8655
            · rcases m.htr 1 2 4 (by decide) (by decide) with h8656 | h8656
              · linarith only [h0, h5, h8656, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h8658 | h8658
                · linarith only [h0, h8201, h8658, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8660 | h8660
                  · linarith only [h1, h8480, h8660, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h8662 | h8662
                    · linarith only [h1, h8482, h8662, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h8664 | h8664
                      · linarith only [h0, h2, h5, h8484, h8655, h8664, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h8666 | h8666
                        · linarith only [h0, h1, h5, h8480, h8655, h8666, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h8668 | h8668
                          · linarith only [h1, h8482, h8655, h8668, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h8670 | h8670
                            · linarith only [h0, h5, h8484, h8655, h8666, h8670, hc23, hc34, hlam, hphi]
                            · linarith only [h0, h5, h8655, h8670, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h4, h5, h8655, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 6296000 in
set_option maxHeartbeats 6296000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x0_x0 (m : N7Model)
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
    (h10363 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10364 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  linarith only [h0, h10364, h4, hlam]

set_option maxHeartbeats 6296000 in
set_option maxHeartbeats 6296000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x0_x1_x0 (m : N7Model)
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
    (h10363 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10364 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h10366 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  linarith only [h0, h10366, h8674, hlam]

set_option maxHeartbeats 6296000 in
set_option maxHeartbeats 6296000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x0_x1_x1_x0 (m : N7Model)
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
    (h10363 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10364 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h10366 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h10368 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  linarith only [h0, h10368, h9870, hlam]

end R2N4
