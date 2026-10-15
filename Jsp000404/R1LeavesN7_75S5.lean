import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_75S4

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_13_24_L_0_H_I_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h398 | h398
  · rcases m.htr 0 2 4 (by decide) (by decide) with h399 | h399
    · rcases m.htr 0 3 4 (by decide) (by decide) with h400 | h400
      · rcases m.htr 1 2 3 (by decide) (by decide) with h401 | h401
        · rcases m.htr 1 2 4 (by decide) (by decide) with h402 | h402
          · rcases m.htr 1 3 4 (by decide) (by decide) with h403 | h403
            · rcases m.htr 1 4 5 (by decide) (by decide) with h404 | h404
              · linarith only [h0, h398, h404, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h406 | h406
                · rcases m.htr 2 4 5 (by decide) (by decide) with h407 | h407
                  · linarith only [h402, h404, h407, hlam]
                  · rcases h4bigk with h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [hlam, p409_0]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h0, h398, h402, h406, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p409_1, u3elo1]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h0, h398, h406, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p409_1, u3elo1]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h0, h398, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p409_1, u3elo1]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h0, h398, h402, h404, h406, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p409_1, u3elo1]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h398, hlam, p409_1]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [hlam, p409_0]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h404, h406, hc34, hc45, hlam, hphi, p409_1]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h0, h398, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p409_1, u3elo1]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h404, hlam, p409_0]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h399, hlam, p409_1]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h402, hlam, p409_1]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [hlam, p409_0]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h399, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p409_1]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h407, hlam, p409_0]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h400, hlam, p409_1]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h403, hlam, p409_0]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h406, hlam, p409_0]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [hlam, p409_0]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h404, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p409_1, u3elo3]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [hc04, hc45, hlam, hphi, p409_1]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [hc14, hc45, hlam, hphi, p409_1]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [h406, hc34, hc45, hlam, hphi, p409_1]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [hc34, hc45, hlam, hphi, p409_1]
                    · have p409_0 := h409c.1
                      have p409_1 := h409c.2.1
                      have p409_2 := h409c.2.2.1
                      have p409_3 := h409c.2.2.2
                      linarith only [hlam, p409_0]
                · linarith only [h0, h400, h406, hc23, hlam, hphi, u3elo1]
            · linarith only [h0, h398, h402, h403, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
          · linarith only [h0, h398, h399, h401, h402, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h438 | h438
          · rcases m.htr 1 3 4 (by decide) (by decide) with h439 | h439
            · rcases m.htr 1 4 5 (by decide) (by decide) with h440 | h440
              · linarith only [h0, h398, h440, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h442 | h442
                · rcases m.htr 2 4 5 (by decide) (by decide) with h443 | h443
                  · linarith only [h438, h440, h443, hlam]
                  · rcases h4bigk with h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c | h445c
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [hlam, p445_0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h0, h398, h401, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p445_1, u3elo2]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h0, h398, h401, h442, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p445_1, u3elo2]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h0, h398, h401, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p445_1, u3elo2]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h0, h398, h401, h438, h440, h442, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p445_1, u3elo2]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h398, hlam, p445_1]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [hlam, p445_0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h440, h442, hc34, hc45, hlam, hphi, p445_1]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h0, h398, h401, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p445_1, u3elo2]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h440, hlam, p445_0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h399, hlam, p445_1]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h438, hlam, p445_1]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [hlam, p445_0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h438, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p445_1]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h443, hlam, p445_0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h400, hlam, p445_1]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h439, hlam, p445_0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h442, hlam, p445_0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [hlam, p445_0]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h443, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p445_1, u3elo3]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [hc04, hc45, hlam, hphi, p445_1]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h438, h442, hc34, hc45, hlam, hphi, p445_1]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [h442, hc34, hc45, hlam, hphi, p445_1]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [hc34, hc45, hlam, hphi, p445_1]
                    · have p445_0 := h445c.1
                      have p445_1 := h445c.2.1
                      have p445_2 := h445c.2.2.1
                      have p445_3 := h445c.2.2.2
                      linarith only [hlam, p445_0]
                · linarith only [h0, h398, h401, h438, h442, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
            · linarith only [h0, h439, hc01, hlam, hphi, ht12, ht23, u3elo3]
          · linarith only [h0, h398, h399, h438, hc12, hlam, hphi, ht23, u3elo1]
      · linarith only [h0, h398, h400, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h475 | h475
      · rcases m.htr 1 2 3 (by decide) (by decide) with h476 | h476
        · rcases m.htr 1 2 4 (by decide) (by decide) with h477 | h477
          · linarith only [h0, h398, h399, h477, hc02, hlam, hphi, ht23, u3elo0]
          · linarith only [h0, h398, h477, hc12, hlam, hphi, ht23, u3elo1]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h480 | h480
          · linarith only [h399, h476, h480, hc02, hlam, hphi, ht23, u3elo2]
          · linarith only [h0, h398, h476, h480, hc12, hlam, hphi, ht23, u3elo2]
      · linarith only [h0, h398, h475, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h484 | h484
    · rcases m.htr 0 3 4 (by decide) (by decide) with h485 | h485
      · rcases m.htr 1 2 3 (by decide) (by decide) with h486 | h486
        · rcases m.htr 1 2 4 (by decide) (by decide) with h487 | h487
          · rcases m.htr 1 3 4 (by decide) (by decide) with h488 | h488
            · rcases m.htr 1 4 5 (by decide) (by decide) with h489 | h489
              · rcases m.htr 2 3 4 (by decide) (by decide) with h490 | h490
                · rcases m.htr 2 4 5 (by decide) (by decide) with h491 | h491
                  · rcases h4bigk with h492c | h492c | h492c | h492c | h492c | h492c | h492c | h492c | h492c | h492c | h492c | h492c | h492c | h492c | h492c | h492c | h492c | h492c | h492c | h492c | h492c | h492c | h492c | h492c | h492c
                    · have p492_0 := h492c.1
                      have p492_1 := h492c.2.1
                      have p492_2 := h492c.2.2.1
                      have p492_3 := h492c.2.2.2
                      linarith only [hlam, p492_0]
                    · have p492_0 := h492c.1
                      have p492_1 := h492c.2.1
                      have p492_2 := h492c.2.2.1
                      have p492_3 := h492c.2.2.2
                      linarith only [h398, hlam, p492_0]
                    · have p492_0 := h492c.1
                      have p492_1 := h492c.2.1
                      have p492_2 := h492c.2.2.1
                      have p492_3 := h492c.2.2.2
                      linarith only [h485, h491, hc03, hc45, hlam, hphi, ht0b, ht5b, p492_1]
                    · have p492_0 := h492c.1
                      have p492_1 := h492c.2.1
                      have p492_2 := h492c.2.2.1
                      have p492_3 := h492c.2.2.2
                      linarith only [h485, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p492_1, u3elo0]
                    · have p492_0 := h492c.1
                      have p492_1 := h492c.2.1
                      have p492_2 := h492c.2.2.1
                      have p492_3 := h492c.2.2.2
                      linarith only [h0, h485, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p492_1, u3elo1]
                    · have p492_0 := h492c.1
                      have p492_1 := h492c.2.1
                      have p492_2 := h492c.2.2.1
                      have p492_3 := h492c.2.2.2
                      linarith only [h488, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p492_1, u3elo1]
                    · have p492_0 := h492c.1
                      have p492_1 := h492c.2.1
                      have p492_2 := h492c.2.2.1
                      have p492_3 := h492c.2.2.2
                      linarith only [hlam, p492_0]
                    · have p492_0 := h492c.1
                      have p492_1 := h492c.2.1
                      have p492_2 := h492c.2.2.1
                      have p492_3 := h492c.2.2.2
                      linarith only [h488, h491, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p492_1, u3elo1]
                    · have p492_0 := h492c.1
                      have p492_1 := h492c.2.1
                      have p492_2 := h492c.2.2.1
                      have p492_3 := h492c.2.2.2
                      linarith only [h488, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p492_1, u3elo1]
                    · have p492_0 := h492c.1
                      have p492_1 := h492c.2.1
                      have p492_2 := h492c.2.2.1
                      have p492_3 := h492c.2.2.2
                      linarith only [h488, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p492_1, u3elo1]
                    · have p492_0 := h492c.1
                      have p492_1 := h492c.2.1
                      have p492_2 := h492c.2.2.1
                      have p492_3 := h492c.2.2.2
                      linarith only [h484, hlam, p492_1]
                    · have p492_0 := h492c.1
                      have p492_1 := h492c.2.1
                      have p492_2 := h492c.2.2.1
                      have p492_3 := h492c.2.2.2
                      linarith only [h487, hlam, p492_1]
                    · have p492_0 := h492c.1
                      have p492_1 := h492c.2.1
                      have p492_2 := h492c.2.2.1
                      have p492_3 := h492c.2.2.2
                      linarith only [hlam, p492_0]
                    · have p492_0 := h492c.1
                      have p492_1 := h492c.2.1
                      have p492_2 := h492c.2.2.1
                      have p492_3 := h492c.2.2.2
                      linarith only [h484, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p492_1]
                    · have p492_0 := h492c.1
                      have p492_1 := h492c.2.1
                      have p492_2 := h492c.2.2.1
                      have p492_3 := h492c.2.2.2
                      linarith only [h398, h484, h488, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p492_1, u3elo1]
                    · have p492_0 := h492c.1
                      have p492_1 := h492c.2.1
                      have p492_2 := h492c.2.2.1
                      have p492_3 := h492c.2.2.2
                      linarith only [h485, hlam, p492_1]
                    · have p492_0 := h492c.1
                      have p492_1 := h492c.2.1
                      have p492_2 := h492c.2.2.1
                      have p492_3 := h492c.2.2.2
                      linarith only [h488, hlam, p492_0]
                    · have p492_0 := h492c.1
                      have p492_1 := h492c.2.1
                      have p492_2 := h492c.2.2.1
                      have p492_3 := h492c.2.2.2
                      linarith only [h490, hlam, p492_0]
                    · have p492_0 := h492c.1
                      have p492_1 := h492c.2.1
                      have p492_2 := h492c.2.2.1
                      have p492_3 := h492c.2.2.2
                      linarith only [hlam, p492_0]
                    · have p492_0 := h492c.1
                      have p492_1 := h492c.2.1
                      have p492_2 := h492c.2.2.1
                      have p492_3 := h492c.2.2.2
                      linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p492_1, u3elo3]
                    · have p492_0 := h492c.1
                      have p492_1 := h492c.2.1
                      have p492_2 := h492c.2.2.1
                      have p492_3 := h492c.2.2.2
                      linarith only [hc04, hc45, hlam, hphi, p492_1]
                    · have p492_0 := h492c.1
                      have p492_1 := h492c.2.1
                      have p492_2 := h492c.2.2.1
                      have p492_3 := h492c.2.2.2
                      linarith only [h489, hlam, p492_0]
                    · have p492_0 := h492c.1
                      have p492_1 := h492c.2.1
                      have p492_2 := h492c.2.2.1
                      have p492_3 := h492c.2.2.2
                      linarith only [h491, hlam, p492_0]
                    · have p492_0 := h492c.1
                      have p492_1 := h492c.2.1
                      have p492_2 := h492c.2.2.1
                      have p492_3 := h492c.2.2.2
                      linarith only [h484, h491, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p492_1]
                    · have p492_0 := h492c.1
                      have p492_1 := h492c.2.1
                      have p492_2 := h492c.2.2.1
                      have p492_3 := h492c.2.2.2
                      linarith only [hlam, p492_0]
                  · rcases h4bigk with h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c
                    · have p518_0 := h518c.1
                      have p518_1 := h518c.2.1
                      have p518_2 := h518c.2.2.1
                      have p518_3 := h518c.2.2.2
                      linarith only [hlam, p518_0]
                    · have p518_0 := h518c.1
                      have p518_1 := h518c.2.1
                      have p518_2 := h518c.2.2.1
                      have p518_3 := h518c.2.2.2
                      linarith only [h398, hlam, p518_0]
                    · have p518_0 := h518c.1
                      have p518_1 := h518c.2.1
                      have p518_2 := h518c.2.2.1
                      have p518_3 := h518c.2.2.2
                      linarith only [h398, h488, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p518_1, u3elo1]
                    · have p518_0 := h518c.1
                      have p518_1 := h518c.2.1
                      have p518_2 := h518c.2.2.1
                      have p518_3 := h518c.2.2.2
                      linarith only [h398, h488, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p518_1, u3elo1]
                    · have p518_0 := h518c.1
                      have p518_1 := h518c.2.1
                      have p518_2 := h518c.2.2.1
                      have p518_3 := h518c.2.2.2
                      linarith only [h398, h488, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p518_1, u3elo1]
                    · have p518_0 := h518c.1
                      have p518_1 := h518c.2.1
                      have p518_2 := h518c.2.2.1
                      have p518_3 := h518c.2.2.2
                      linarith only [h488, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p518_1, u3elo1]
                    · have p518_0 := h518c.1
                      have p518_1 := h518c.2.1
                      have p518_2 := h518c.2.2.1
                      have p518_3 := h518c.2.2.2
                      linarith only [hlam, p518_0]
                    · have p518_0 := h518c.1
                      have p518_1 := h518c.2.1
                      have p518_2 := h518c.2.2.1
                      have p518_3 := h518c.2.2.2
                      linarith only [h488, h490, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p518_1, u3elo1]
                    · have p518_0 := h518c.1
                      have p518_1 := h518c.2.1
                      have p518_2 := h518c.2.2.1
                      have p518_3 := h518c.2.2.2
                      linarith only [h488, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p518_1, u3elo1]
                    · have p518_0 := h518c.1
                      have p518_1 := h518c.2.1
                      have p518_2 := h518c.2.2.1
                      have p518_3 := h518c.2.2.2
                      linarith only [h488, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p518_1, u3elo1]
                    · have p518_0 := h518c.1
                      have p518_1 := h518c.2.1
                      have p518_2 := h518c.2.2.1
                      have p518_3 := h518c.2.2.2
                      linarith only [h484, hlam, p518_1]
                    · have p518_0 := h518c.1
                      have p518_1 := h518c.2.1
                      have p518_2 := h518c.2.2.1
                      have p518_3 := h518c.2.2.2
                      linarith only [h487, hlam, p518_1]
                    · have p518_0 := h518c.1
                      have p518_1 := h518c.2.1
                      have p518_2 := h518c.2.2.1
                      have p518_3 := h518c.2.2.2
                      linarith only [hlam, p518_0]
                    · have p518_0 := h518c.1
                      have p518_1 := h518c.2.1
                      have p518_2 := h518c.2.2.1
                      have p518_3 := h518c.2.2.2
                      linarith only [h484, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p518_1]
                    · have p518_0 := h518c.1
                      have p518_1 := h518c.2.1
                      have p518_2 := h518c.2.2.1
                      have p518_3 := h518c.2.2.2
                      linarith only [h491, hlam, p518_0]
                    · have p518_0 := h518c.1
                      have p518_1 := h518c.2.1
                      have p518_2 := h518c.2.2.1
                      have p518_3 := h518c.2.2.2
                      linarith only [h485, hlam, p518_1]
                    · have p518_0 := h518c.1
                      have p518_1 := h518c.2.1
                      have p518_2 := h518c.2.2.1
                      have p518_3 := h518c.2.2.2
                      linarith only [h488, hlam, p518_0]
                    · have p518_0 := h518c.1
                      have p518_1 := h518c.2.1
                      have p518_2 := h518c.2.2.1
                      have p518_3 := h518c.2.2.2
                      linarith only [h490, hlam, p518_0]
                    · have p518_0 := h518c.1
                      have p518_1 := h518c.2.1
                      have p518_2 := h518c.2.2.1
                      have p518_3 := h518c.2.2.2
                      linarith only [hlam, p518_0]
                    · have p518_0 := h518c.1
                      have p518_1 := h518c.2.1
                      have p518_2 := h518c.2.2.1
                      have p518_3 := h518c.2.2.2
                      linarith only [h491, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p518_1, u3elo3]
                    · have p518_0 := h518c.1
                      have p518_1 := h518c.2.1
                      have p518_2 := h518c.2.2.1
                      have p518_3 := h518c.2.2.2
                      linarith only [hc04, hc45, hlam, hphi, p518_1]
                    · have p518_0 := h518c.1
                      have p518_1 := h518c.2.1
                      have p518_2 := h518c.2.2.1
                      have p518_3 := h518c.2.2.2
                      linarith only [h489, hlam, p518_0]
                    · have p518_0 := h518c.1
                      have p518_1 := h518c.2.1
                      have p518_2 := h518c.2.2.1
                      have p518_3 := h518c.2.2.2
                      linarith only [h488, h489, h490, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p518_1, u3elo1]
                    · have p518_0 := h518c.1
                      have p518_1 := h518c.2.1
                      have p518_2 := h518c.2.2.1
                      have p518_3 := h518c.2.2.2
                      linarith only [h488, h489, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p518_1, u3elo1]
                    · have p518_0 := h518c.1
                      have p518_1 := h518c.2.1
                      have p518_2 := h518c.2.2.1
                      have p518_3 := h518c.2.2.2
                      linarith only [hlam, p518_0]
                · linarith only [h0, h485, h490, hc23, hlam, hphi, u3elo1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h545 | h545
                · rcases m.htr 2 4 5 (by decide) (by decide) with h546 | h546
                  · linarith only [h398, h489, h546, hc01, hc24, hlam, hphi, ht12]
                  · rcases h4bigk with h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c | h548c
                    · have p548_0 := h548c.1
                      have p548_1 := h548c.2.1
                      have p548_2 := h548c.2.2.1
                      have p548_3 := h548c.2.2.2
                      linarith only [hlam, p548_0]
                    · have p548_0 := h548c.1
                      have p548_1 := h548c.2.1
                      have p548_2 := h548c.2.2.1
                      have p548_3 := h548c.2.2.2
                      linarith only [h398, hlam, p548_0]
                    · have p548_0 := h548c.1
                      have p548_1 := h548c.2.1
                      have p548_2 := h548c.2.2.1
                      have p548_3 := h548c.2.2.2
                      linarith only [h398, h489, hc24, hc45, hlam, hphi, p548_1]
                    · have p548_0 := h548c.1
                      have p548_1 := h548c.2.1
                      have p548_2 := h548c.2.2.1
                      have p548_3 := h548c.2.2.2
                      linarith only [h398, h489, hc34, hc45, hlam, hphi, p548_1]
                    · have p548_0 := h548c.1
                      have p548_1 := h548c.2.1
                      have p548_2 := h548c.2.2.1
                      have p548_3 := h548c.2.2.2
                      linarith only [h398, h489, hlam, p548_1]
                    · have p548_0 := h548c.1
                      have p548_1 := h548c.2.1
                      have p548_2 := h548c.2.2.1
                      have p548_3 := h548c.2.2.2
                      linarith only [h489, hc04, hc45, hlam, hphi, p548_1]
                    · have p548_0 := h548c.1
                      have p548_1 := h548c.2.1
                      have p548_2 := h548c.2.2.1
                      have p548_3 := h548c.2.2.2
                      linarith only [hlam, p548_0]
                    · have p548_0 := h548c.1
                      have p548_1 := h548c.2.1
                      have p548_2 := h548c.2.2.1
                      have p548_3 := h548c.2.2.2
                      linarith only [h489, h545, hc34, hc45, hlam, hphi, p548_1]
                    · have p548_0 := h548c.1
                      have p548_1 := h548c.2.1
                      have p548_2 := h548c.2.2.1
                      have p548_3 := h548c.2.2.2
                      linarith only [h489, hc34, hc45, hlam, hphi, p548_1]
                    · have p548_0 := h548c.1
                      have p548_1 := h548c.2.1
                      have p548_2 := h548c.2.2.1
                      have p548_3 := h548c.2.2.2
                      linarith only [h489, hlam, p548_0]
                    · have p548_0 := h548c.1
                      have p548_1 := h548c.2.1
                      have p548_2 := h548c.2.2.1
                      have p548_3 := h548c.2.2.2
                      linarith only [h484, hlam, p548_1]
                    · have p548_0 := h548c.1
                      have p548_1 := h548c.2.1
                      have p548_2 := h548c.2.2.1
                      have p548_3 := h548c.2.2.2
                      linarith only [h487, hlam, p548_1]
                    · have p548_0 := h548c.1
                      have p548_1 := h548c.2.1
                      have p548_2 := h548c.2.2.1
                      have p548_3 := h548c.2.2.2
                      linarith only [hlam, p548_0]
                    · have p548_0 := h548c.1
                      have p548_1 := h548c.2.1
                      have p548_2 := h548c.2.2.1
                      have p548_3 := h548c.2.2.2
                      linarith only [h484, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p548_1]
                    · have p548_0 := h548c.1
                      have p548_1 := h548c.2.1
                      have p548_2 := h548c.2.2.1
                      have p548_3 := h548c.2.2.2
                      linarith only [h546, hlam, p548_0]
                    · have p548_0 := h548c.1
                      have p548_1 := h548c.2.1
                      have p548_2 := h548c.2.2.1
                      have p548_3 := h548c.2.2.2
                      linarith only [h485, hlam, p548_1]
                    · have p548_0 := h548c.1
                      have p548_1 := h548c.2.1
                      have p548_2 := h548c.2.2.1
                      have p548_3 := h548c.2.2.2
                      linarith only [h488, hlam, p548_0]
                    · have p548_0 := h548c.1
                      have p548_1 := h548c.2.1
                      have p548_2 := h548c.2.2.1
                      have p548_3 := h548c.2.2.2
                      linarith only [h545, hlam, p548_0]
                    · have p548_0 := h548c.1
                      have p548_1 := h548c.2.1
                      have p548_2 := h548c.2.2.1
                      have p548_3 := h548c.2.2.2
                      linarith only [hlam, p548_0]
                    · have p548_0 := h548c.1
                      have p548_1 := h548c.2.1
                      have p548_2 := h548c.2.2.1
                      have p548_3 := h548c.2.2.2
                      linarith only [h398, h489, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p548_1, u3elo3]
                    · have p548_0 := h548c.1
                      have p548_1 := h548c.2.1
                      have p548_2 := h548c.2.2.1
                      have p548_3 := h548c.2.2.2
                      linarith only [h398, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p548_1]
                    · have p548_0 := h548c.1
                      have p548_1 := h548c.2.1
                      have p548_2 := h548c.2.2.1
                      have p548_3 := h548c.2.2.2
                      linarith only [h398, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p548_1]
                    · have p548_0 := h548c.1
                      have p548_1 := h548c.2.1
                      have p548_2 := h548c.2.2.1
                      have p548_3 := h548c.2.2.2
                      linarith only [h545, hc34, hc45, hlam, hphi, p548_1]
                    · have p548_0 := h548c.1
                      have p548_1 := h548c.2.1
                      have p548_2 := h548c.2.2.1
                      have p548_3 := h548c.2.2.2
                      linarith only [hc34, hc45, hlam, hphi, p548_1]
                    · have p548_0 := h548c.1
                      have p548_1 := h548c.2.1
                      have p548_2 := h548c.2.2.1
                      have p548_3 := h548c.2.2.2
                      linarith only [hlam, p548_0]
                · linarith only [h0, h485, h545, hc23, hlam, hphi, u3elo1]
            · linarith only [h0, h488, hc01, hlam, hphi, ht12, ht23, u3elo3]
          · linarith only [h0, h484, h485, h486, h487, hc23, hlam, hphi, u3elo1]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h577 | h577
          · linarith only [h398, h486, h577, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · linarith only [h398, h484, h577, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h580 | h580
        · rcases m.htr 1 2 4 (by decide) (by decide) with h581 | h581
          · rcases m.htr 1 3 4 (by decide) (by decide) with h582 | h582
            · linarith only [h485, h582, hc03, hlam, hphi, u3elo1]
            · linarith only [h0, h582, hc01, hlam, hphi, ht12, ht23, u3elo3]
          · linarith only [h484, h485, h580, h581, hc23, hlam, hphi, u3elo3]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h586 | h586
          · linarith only [h398, h580, h586, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · linarith only [h398, h484, h586, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h589 | h589
      · rcases m.htr 1 2 3 (by decide) (by decide) with h590 | h590
        · rcases m.htr 1 2 4 (by decide) (by decide) with h591 | h591
          · rcases m.htr 1 3 4 (by decide) (by decide) with h592 | h592
            · rcases m.htr 1 4 5 (by decide) (by decide) with h593 | h593
              · rcases m.htr 2 3 4 (by decide) (by decide) with h594 | h594
                · rcases m.htr 2 4 5 (by decide) (by decide) with h595 | h595
                  · rcases h4bigk with h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c | h596c
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [hlam, p596_0]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h398, hlam, p596_0]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h484, hlam, p596_0]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h589, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p596_1, u3elo0]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h0, h589, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p596_1, u3elo1]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h398, hc01, hc14, hlam, hphi, p596_1]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [hlam, p596_0]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h484, h591, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p596_1]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h592, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p596_1, u3elo1]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h592, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p596_1, u3elo1]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h398, hc01, hc24, hlam, hphi, ht12, p596_1]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h591, hlam, p596_1]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [hlam, p596_0]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h591, h592, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p596_1, u3elo1]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h591, h592, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p596_1, u3elo1]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h589, hlam, p596_1]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h592, hlam, p596_0]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h594, hlam, p596_0]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [hlam, p596_0]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p596_1, u3elo3]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h398, h595, hc01, hc25, hlam, hphi, ht12, p596_1]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h593, hlam, p596_0]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h595, hlam, p596_0]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [h591, h592, h595, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p596_1, u3elo1]
                    · have p596_0 := h596c.1
                      have p596_1 := h596c.2.1
                      have p596_2 := h596c.2.2.1
                      have p596_3 := h596c.2.2.2
                      linarith only [hlam, p596_0]
                  · linarith only [h484, h592, h593, h595, hc02, hlam, hphi, ht23, u3elo1]
                · linarith only [h0, h589, h594, hc23, hlam, hphi, u3elo1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h624 | h624
                · rcases m.htr 2 4 5 (by decide) (by decide) with h625 | h625
                  · linarith only [h398, h593, h625, hc01, hc24, hlam, hphi, ht12]
                  · rcases h4bigk with h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c | h627c
                    · have p627_0 := h627c.1
                      have p627_1 := h627c.2.1
                      have p627_2 := h627c.2.2.1
                      have p627_3 := h627c.2.2.2
                      linarith only [hlam, p627_0]
                    · have p627_0 := h627c.1
                      have p627_1 := h627c.2.1
                      have p627_2 := h627c.2.2.1
                      have p627_3 := h627c.2.2.2
                      linarith only [h398, hlam, p627_0]
                    · have p627_0 := h627c.1
                      have p627_1 := h627c.2.1
                      have p627_2 := h627c.2.2.1
                      have p627_3 := h627c.2.2.2
                      linarith only [h484, hlam, p627_0]
                    · have p627_0 := h627c.1
                      have p627_1 := h627c.2.1
                      have p627_2 := h627c.2.2.1
                      have p627_3 := h627c.2.2.2
                      linarith only [h398, h593, hc34, hc45, hlam, hphi, p627_1]
                    · have p627_0 := h627c.1
                      have p627_1 := h627c.2.1
                      have p627_2 := h627c.2.2.1
                      have p627_3 := h627c.2.2.2
                      linarith only [h484, h591, h593, hlam, p627_1]
                    · have p627_0 := h627c.1
                      have p627_1 := h627c.2.1
                      have p627_2 := h627c.2.2.1
                      have p627_3 := h627c.2.2.2
                      linarith only [h593, hc04, hc45, hlam, hphi, p627_1]
                    · have p627_0 := h627c.1
                      have p627_1 := h627c.2.1
                      have p627_2 := h627c.2.2.1
                      have p627_3 := h627c.2.2.2
                      linarith only [hlam, p627_0]
                    · have p627_0 := h627c.1
                      have p627_1 := h627c.2.1
                      have p627_2 := h627c.2.2.1
                      have p627_3 := h627c.2.2.2
                      linarith only [h593, hc24, hc45, hlam, hphi, p627_1]
                    · have p627_0 := h627c.1
                      have p627_1 := h627c.2.1
                      have p627_2 := h627c.2.2.1
                      have p627_3 := h627c.2.2.2
                      linarith only [h593, hc34, hc45, hlam, hphi, p627_1]
                    · have p627_0 := h627c.1
                      have p627_1 := h627c.2.1
                      have p627_2 := h627c.2.2.1
                      have p627_3 := h627c.2.2.2
                      linarith only [h593, hlam, p627_0]
                    · have p627_0 := h627c.1
                      have p627_1 := h627c.2.1
                      have p627_2 := h627c.2.2.1
                      have p627_3 := h627c.2.2.2
                      linarith only [h398, hc01, hc24, hlam, hphi, ht12, p627_1]
                    · have p627_0 := h627c.1
                      have p627_1 := h627c.2.1
                      have p627_2 := h627c.2.2.1
                      have p627_3 := h627c.2.2.2
                      linarith only [h591, hlam, p627_1]
                    · have p627_0 := h627c.1
                      have p627_1 := h627c.2.1
                      have p627_2 := h627c.2.2.1
                      have p627_3 := h627c.2.2.2
                      linarith only [hlam, p627_0]
                    · have p627_0 := h627c.1
                      have p627_1 := h627c.2.1
                      have p627_2 := h627c.2.2.1
                      have p627_3 := h627c.2.2.2
                      linarith only [h591, h593, hc34, hc45, hlam, hphi, p627_1]
                    · have p627_0 := h627c.1
                      have p627_1 := h627c.2.1
                      have p627_2 := h627c.2.2.1
                      have p627_3 := h627c.2.2.2
                      linarith only [h625, hlam, p627_0]
                    · have p627_0 := h627c.1
                      have p627_1 := h627c.2.1
                      have p627_2 := h627c.2.2.1
                      have p627_3 := h627c.2.2.2
                      linarith only [h589, hlam, p627_1]
                    · have p627_0 := h627c.1
                      have p627_1 := h627c.2.1
                      have p627_2 := h627c.2.2.1
                      have p627_3 := h627c.2.2.2
                      linarith only [h592, hlam, p627_0]
                    · have p627_0 := h627c.1
                      have p627_1 := h627c.2.1
                      have p627_2 := h627c.2.2.1
                      have p627_3 := h627c.2.2.2
                      linarith only [h624, hlam, p627_0]
                    · have p627_0 := h627c.1
                      have p627_1 := h627c.2.1
                      have p627_2 := h627c.2.2.1
                      have p627_3 := h627c.2.2.2
                      linarith only [hlam, p627_0]
                    · have p627_0 := h627c.1
                      have p627_1 := h627c.2.1
                      have p627_2 := h627c.2.2.1
                      have p627_3 := h627c.2.2.2
                      linarith only [h593, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p627_1, u3elo3]
                    · have p627_0 := h627c.1
                      have p627_1 := h627c.2.1
                      have p627_2 := h627c.2.2.1
                      have p627_3 := h627c.2.2.2
                      linarith only [h398, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p627_1]
                    · have p627_0 := h627c.1
                      have p627_1 := h627c.2.1
                      have p627_2 := h627c.2.2.1
                      have p627_3 := h627c.2.2.2
                      linarith only [h398, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p627_1]
                    · have p627_0 := h627c.1
                      have p627_1 := h627c.2.1
                      have p627_2 := h627c.2.2.1
                      have p627_3 := h627c.2.2.2
                      linarith only [h484, hc02, hc45, hlam, hphi, ht23, ht34, p627_1]
                    · have p627_0 := h627c.1
                      have p627_1 := h627c.2.1
                      have p627_2 := h627c.2.2.1
                      have p627_3 := h627c.2.2.2
                      linarith only [hc34, hc45, hlam, hphi, p627_1]
                    · have p627_0 := h627c.1
                      have p627_1 := h627c.2.1
                      have p627_2 := h627c.2.2.1
                      have p627_3 := h627c.2.2.2
                      linarith only [hlam, p627_0]
                · linarith only [h0, h589, h624, hc23, hlam, hphi, u3elo1]
            · linarith only [h0, h592, hc01, hlam, hphi, ht12, ht23, u3elo3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h655 | h655
            · linarith only [h590, h591, h655, hlam]
            · linarith only [h0, h589, h655, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h658 | h658
          · linarith only [h484, h590, h658, hc02, hlam, hphi, ht23, u3elo2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h660 | h660
            · rcases m.htr 1 4 5 (by decide) (by decide) with h661 | h661
              · rcases m.htr 2 3 4 (by decide) (by decide) with h662 | h662
                · rcases m.htr 2 4 5 (by decide) (by decide) with h663 | h663
                  · rcases h4bigk with h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c | h664c
                    · have p664_0 := h664c.1
                      have p664_1 := h664c.2.1
                      have p664_2 := h664c.2.2.1
                      have p664_3 := h664c.2.2.2
                      linarith only [hlam, p664_0]
                    · have p664_0 := h664c.1
                      have p664_1 := h664c.2.1
                      have p664_2 := h664c.2.2.1
                      have p664_3 := h664c.2.2.2
                      linarith only [h398, hlam, p664_0]
                    · have p664_0 := h664c.1
                      have p664_1 := h664c.2.1
                      have p664_2 := h664c.2.2.1
                      have p664_3 := h664c.2.2.2
                      linarith only [h484, hlam, p664_0]
                    · have p664_0 := h664c.1
                      have p664_1 := h664c.2.1
                      have p664_2 := h664c.2.2.1
                      have p664_3 := h664c.2.2.2
                      linarith only [h398, h590, h660, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p664_1, u3elo2]
                    · have p664_0 := h664c.1
                      have p664_1 := h664c.2.1
                      have p664_2 := h664c.2.2.1
                      have p664_3 := h664c.2.2.2
                      linarith only [h398, h590, h660, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p664_1, u3elo2]
                    · have p664_0 := h664c.1
                      have p664_1 := h664c.2.1
                      have p664_2 := h664c.2.2.1
                      have p664_3 := h664c.2.2.2
                      linarith only [h590, h660, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p664_1, u3elo2]
                    · have p664_0 := h664c.1
                      have p664_1 := h664c.2.1
                      have p664_2 := h664c.2.2.1
                      have p664_3 := h664c.2.2.2
                      linarith only [hlam, p664_0]
                    · have p664_0 := h664c.1
                      have p664_1 := h664c.2.1
                      have p664_2 := h664c.2.2.1
                      have p664_3 := h664c.2.2.2
                      linarith only [h658, hlam, p664_0]
                    · have p664_0 := h664c.1
                      have p664_1 := h664c.2.1
                      have p664_2 := h664c.2.2.1
                      have p664_3 := h664c.2.2.2
                      linarith only [h590, h660, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p664_1, u3elo2]
                    · have p664_0 := h664c.1
                      have p664_1 := h664c.2.1
                      have p664_2 := h664c.2.2.1
                      have p664_3 := h664c.2.2.2
                      linarith only [h590, h660, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p664_1, u3elo2]
                    · have p664_0 := h664c.1
                      have p664_1 := h664c.2.1
                      have p664_2 := h664c.2.2.1
                      have p664_3 := h664c.2.2.2
                      linarith only [h398, hc01, hc24, hlam, hphi, ht12, p664_1]
                    · have p664_0 := h664c.1
                      have p664_1 := h664c.2.1
                      have p664_2 := h664c.2.2.1
                      have p664_3 := h664c.2.2.2
                      linarith only [h398, hc01, hc24, hlam, hphi, ht12, p664_1]
                    · have p664_0 := h664c.1
                      have p664_1 := h664c.2.1
                      have p664_2 := h664c.2.2.1
                      have p664_3 := h664c.2.2.2
                      linarith only [hlam, p664_0]
                    · have p664_0 := h664c.1
                      have p664_1 := h664c.2.1
                      have p664_2 := h664c.2.2.1
                      have p664_3 := h664c.2.2.2
                      linarith only [h662, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p664_1, u3elo2]
                    · have p664_0 := h664c.1
                      have p664_1 := h664c.2.1
                      have p664_2 := h664c.2.2.1
                      have p664_3 := h664c.2.2.2
                      linarith only [h662, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p664_1, u3elo2]
                    · have p664_0 := h664c.1
                      have p664_1 := h664c.2.1
                      have p664_2 := h664c.2.2.1
                      have p664_3 := h664c.2.2.2
                      linarith only [h589, hlam, p664_1]
                    · have p664_0 := h664c.1
                      have p664_1 := h664c.2.1
                      have p664_2 := h664c.2.2.1
                      have p664_3 := h664c.2.2.2
                      linarith only [h660, hlam, p664_0]
                    · have p664_0 := h664c.1
                      have p664_1 := h664c.2.1
                      have p664_2 := h664c.2.2.1
                      have p664_3 := h664c.2.2.2
                      linarith only [h662, hlam, p664_0]
                    · have p664_0 := h664c.1
                      have p664_1 := h664c.2.1
                      have p664_2 := h664c.2.2.1
                      have p664_3 := h664c.2.2.2
                      linarith only [hlam, p664_0]
                    · have p664_0 := h664c.1
                      have p664_1 := h664c.2.1
                      have p664_2 := h664c.2.2.1
                      have p664_3 := h664c.2.2.2
                      linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p664_1, u3elo3]
                    · have p664_0 := h664c.1
                      have p664_1 := h664c.2.1
                      have p664_2 := h664c.2.2.1
                      have p664_3 := h664c.2.2.2
                      linarith only [h398, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p664_1]
                    · have p664_0 := h664c.1
                      have p664_1 := h664c.2.1
                      have p664_2 := h664c.2.2.1
                      have p664_3 := h664c.2.2.2
                      linarith only [h661, hlam, p664_0]
                    · have p664_0 := h664c.1
                      have p664_1 := h664c.2.1
                      have p664_2 := h664c.2.2.1
                      have p664_3 := h664c.2.2.2
                      linarith only [h663, hlam, p664_0]
                    · have p664_0 := h664c.1
                      have p664_1 := h664c.2.1
                      have p664_2 := h664c.2.2.1
                      have p664_3 := h664c.2.2.2
                      linarith only [h661, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p664_1]
                    · have p664_0 := h664c.1
                      have p664_1 := h664c.2.1
                      have p664_2 := h664c.2.2.1
                      have p664_3 := h664c.2.2.2
                      linarith only [hlam, p664_0]
                  · linarith only [h658, h661, h663, hlam]
                · linarith only [h0, h590, h662, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h692 | h692
                · rcases m.htr 2 4 5 (by decide) (by decide) with h693 | h693
                  · linarith only [h398, h661, h692, h693, hc01, hc23, hlam, hphi, ht12]
                  · rcases h4bigk with h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c
                    · have p695_0 := h695c.1
                      have p695_1 := h695c.2.1
                      have p695_2 := h695c.2.2.1
                      have p695_3 := h695c.2.2.2
                      linarith only [hlam, p695_0]
                    · have p695_0 := h695c.1
                      have p695_1 := h695c.2.1
                      have p695_2 := h695c.2.2.1
                      have p695_3 := h695c.2.2.2
                      linarith only [h398, hlam, p695_0]
                    · have p695_0 := h695c.1
                      have p695_1 := h695c.2.1
                      have p695_2 := h695c.2.2.1
                      have p695_3 := h695c.2.2.2
                      linarith only [h484, hlam, p695_0]
                    · have p695_0 := h695c.1
                      have p695_1 := h695c.2.1
                      have p695_2 := h695c.2.2.1
                      have p695_3 := h695c.2.2.2
                      linarith only [h398, h660, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p695_1, u3elo1]
                    · have p695_0 := h695c.1
                      have p695_1 := h695c.2.1
                      have p695_2 := h695c.2.2.1
                      have p695_3 := h695c.2.2.2
                      linarith only [h398, h658, h693, hlam, p695_1]
                    · have p695_0 := h695c.1
                      have p695_1 := h695c.2.1
                      have p695_2 := h695c.2.2.1
                      have p695_3 := h695c.2.2.2
                      linarith only [h658, h693, hc04, hc45, hlam, hphi, p695_1]
                    · have p695_0 := h695c.1
                      have p695_1 := h695c.2.1
                      have p695_2 := h695c.2.2.1
                      have p695_3 := h695c.2.2.2
                      linarith only [hlam, p695_0]
                    · have p695_0 := h695c.1
                      have p695_1 := h695c.2.1
                      have p695_2 := h695c.2.2.1
                      have p695_3 := h695c.2.2.2
                      linarith only [h658, hlam, p695_0]
                    · have p695_0 := h695c.1
                      have p695_1 := h695c.2.1
                      have p695_2 := h695c.2.2.1
                      have p695_3 := h695c.2.2.2
                      linarith only [h658, h693, hc34, hc45, hlam, hphi, p695_1]
                    · have p695_0 := h695c.1
                      have p695_1 := h695c.2.1
                      have p695_2 := h695c.2.2.1
                      have p695_3 := h695c.2.2.2
                      linarith only [h661, hlam, p695_0]
                    · have p695_0 := h695c.1
                      have p695_1 := h695c.2.1
                      have p695_2 := h695c.2.2.1
                      have p695_3 := h695c.2.2.2
                      linarith only [h398, h693, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p695_1]
                    · have p695_0 := h695c.1
                      have p695_1 := h695c.2.1
                      have p695_2 := h695c.2.2.1
                      have p695_3 := h695c.2.2.2
                      linarith only [h693, hc14, hc45, hlam, hphi, p695_1]
                    · have p695_0 := h695c.1
                      have p695_1 := h695c.2.1
                      have p695_2 := h695c.2.2.1
                      have p695_3 := h695c.2.2.2
                      linarith only [hlam, p695_0]
                    · have p695_0 := h695c.1
                      have p695_1 := h695c.2.1
                      have p695_2 := h695c.2.2.1
                      have p695_3 := h695c.2.2.2
                      linarith only [h693, hc34, hc45, hlam, hphi, p695_1]
                    · have p695_0 := h695c.1
                      have p695_1 := h695c.2.1
                      have p695_2 := h695c.2.2.1
                      have p695_3 := h695c.2.2.2
                      linarith only [h693, hlam, p695_0]
                    · have p695_0 := h695c.1
                      have p695_1 := h695c.2.1
                      have p695_2 := h695c.2.2.1
                      have p695_3 := h695c.2.2.2
                      linarith only [h589, hlam, p695_1]
                    · have p695_0 := h695c.1
                      have p695_1 := h695c.2.1
                      have p695_2 := h695c.2.2.1
                      have p695_3 := h695c.2.2.2
                      linarith only [h660, hlam, p695_0]
                    · have p695_0 := h695c.1
                      have p695_1 := h695c.2.1
                      have p695_2 := h695c.2.2.1
                      have p695_3 := h695c.2.2.2
                      linarith only [h692, hlam, p695_0]
                    · have p695_0 := h695c.1
                      have p695_1 := h695c.2.1
                      have p695_2 := h695c.2.2.1
                      have p695_3 := h695c.2.2.2
                      linarith only [hlam, p695_0]
                    · have p695_0 := h695c.1
                      have p695_1 := h695c.2.1
                      have p695_2 := h695c.2.2.1
                      have p695_3 := h695c.2.2.2
                      linarith only [h658, h693, hc12, hlam, hphi, ht23, p695_1, u3elo3]
                    · have p695_0 := h695c.1
                      have p695_1 := h695c.2.1
                      have p695_2 := h695c.2.2.1
                      have p695_3 := h695c.2.2.2
                      linarith only [h398, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p695_1]
                    · have p695_0 := h695c.1
                      have p695_1 := h695c.2.1
                      have p695_2 := h695c.2.2.1
                      have p695_3 := h695c.2.2.2
                      linarith only [h398, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p695_1]
                    · have p695_0 := h695c.1
                      have p695_1 := h695c.2.1
                      have p695_2 := h695c.2.2.1
                      have p695_3 := h695c.2.2.2
                      linarith only [h398, h658, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p695_1]
                    · have p695_0 := h695c.1
                      have p695_1 := h695c.2.1
                      have p695_2 := h695c.2.2.1
                      have p695_3 := h695c.2.2.2
                      linarith only [hc34, hc45, hlam, hphi, p695_1]
                    · have p695_0 := h695c.1
                      have p695_1 := h695c.2.1
                      have p695_2 := h695c.2.2.1
                      have p695_3 := h695c.2.2.2
                      linarith only [hlam, p695_0]
                · linarith only [h0, h590, h692, hc01, hlam, hphi, ht12, ht23, u3elo3]
            · linarith only [h0, h589, h660, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h723 | h723
        · rcases m.htr 1 2 4 (by decide) (by decide) with h724 | h724
          · rcases m.htr 1 3 4 (by decide) (by decide) with h725 | h725
            · linarith only [h0, h589, h725, hc01, hlam, hphi, ht12, ht23, u3elo1]
            · linarith only [h0, h725, hc01, hlam, hphi, ht12, ht23, u3elo3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h728 | h728
            · linarith only [h0, h589, h728, hc01, hlam, hphi, ht12, ht23, u3elo1]
            · linarith only [h0, h728, hc01, hlam, hphi, ht12, ht23, u3elo3]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h731 | h731
          · linarith only [h484, h723, h731, hc02, hc23, hlam, hphi]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h733 | h733
            · linarith only [h0, h589, h733, hc01, hlam, hphi, ht12, ht23, u3elo1]
            · linarith only [h0, h733, hc01, hlam, hphi, ht12, ht23, u3elo3]

theorem r1l7_13_24_L_0_H_I (m : N7Model)
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · exact r1l7_13_24_L_0_H_I_x0 m hb3 hb4 h0
  · exact r1l7_13_24_L_0_H_I_x1 m hb3 hb4 h0

theorem r1l7_20_11_13_14_H_L_L_0_L_0_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0elo := hb0.1
  have h1elo := hb1.1
  have h3elo := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h4, h8, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h11 | h11
                  · linarith only [h0, h11, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h11, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h14 | h14
                · linarith only [h14, h5, h6, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h16 | h16
                  · linarith only [h0, h16, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h16, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h19 | h19
              · rcases m.htr 0 4 5 (by decide) (by decide) with h20 | h20
                · rcases m.htr 1 2 3 (by decide) (by decide) with h21 | h21
                  · linarith only [h0, h21, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h21, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · linarith only [h19, h20, h5, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h25 | h25
                · rcases m.htr 1 2 3 (by decide) (by decide) with h26 | h26
                  · linarith only [h0, h26, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h26, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h29 | h29
                  · linarith only [h0, h29, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h29, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h32 | h32
            · rcases m.htr 0 3 5 (by decide) (by decide) with h33 | h33
              · rcases m.htr 0 4 5 (by decide) (by decide) with h34 | h34
                · rcases m.htr 1 2 3 (by decide) (by decide) with h35 | h35
                  · linarith only [h0, h35, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h37 | h37
                    · linarith only [h0, h37, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h39 | h39
                      · linarith only [h1, h35, h39, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h41 | h41
                        · linarith only [h1, h41, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h32, h35, h41, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h44 | h44
                  · linarith only [h0, h4, h44, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h46 | h46
                    · linarith only [h0, h46, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h48 | h48
                      · linarith only [h1, h44, h48, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h50 | h50
                        · linarith only [h1, h50, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h1, h32, h44, h50, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h53 | h53
                · linarith only [h32, h33, h53, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h55 | h55
                  · linarith only [h0, h4, h55, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h57 | h57
                    · linarith only [h0, h57, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h59 | h59
                      · linarith only [h1, h55, h59, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h61 | h61
                        · linarith only [h1, h61, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h32, h33, h55, h61, hc12, hlam, hphi, ht23, u3elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h64 | h64
              · rcases m.htr 0 4 5 (by decide) (by decide) with h65 | h65
                · rcases m.htr 1 2 3 (by decide) (by decide) with h66 | h66
                  · linarith only [h0, h4, h66, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h68 | h68
                    · linarith only [h0, h68, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h70 | h70
                      · linarith only [h1, h66, h70, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h72 | h72
                        · linarith only [h1, h32, h72, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h74 | h74
                          · linarith only [h2, h72, h74, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h64, h66, h74, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h32, h64, h65, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h78 | h78
                · rcases m.htr 1 2 3 (by decide) (by decide) with h79 | h79
                  · linarith only [h0, h4, h79, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h81 | h81
                    · linarith only [h0, h81, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h83 | h83
                      · linarith only [h1, h79, h83, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h85 | h85
                        · linarith only [h1, h32, h85, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h87 | h87
                          · linarith only [h1, h64, h87, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h89 | h89
                            · linarith only [h2, h89, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h78, h79, h85, h89, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h92 | h92
                  · linarith only [h0, h4, h92, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h94 | h94
                    · linarith only [h1, h92, h94, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h96 | h96
                      · linarith only [h1, h92, h96, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h98 | h98
                        · linarith only [h1, h32, h4, h98, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h100 | h100
                          · linarith only [h1, h100, h64, h78, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h102 | h102
                            · linarith only [h0, h102, h2, h32, h4, h78, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h104 | h104
                              · linarith only [h0, h104, h32, h4, hc12, hlam, hphi, ht23, u3elo2]
                              · linarith only [h0, h104, h4, hc12, hlam, hphi, ht23, u3elo3]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h107 | h107
          · rcases m.htr 0 3 4 (by decide) (by decide) with h108 | h108
            · rcases m.htr 0 3 5 (by decide) (by decide) with h109 | h109
              · linarith only [h1, h109, h3, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h111 | h111
                · linarith only [h111, h2, h3, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h113 | h113
                  · linarith only [h0, h113, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h107, h113, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h116 | h116
              · linarith only [h0, h107, h108, h116, h3, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h118 | h118
                · linarith only [h118, h2, h3, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h120 | h120
                  · linarith only [h0, h120, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h107, h120, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h123 | h123
            · rcases m.htr 0 3 5 (by decide) (by decide) with h124 | h124
              · linarith only [h1, h124, h3, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h126 | h126
                · linarith only [h0, h123, h124, h126, h3, hc12, hlam, hphi, ht23, u3elo4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h128 | h128
                  · linarith only [h0, h128, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h130 | h130
                    · linarith only [h0, h130, h3, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h132 | h132
                      · linarith only [h1, h128, h132, h3, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h134 | h134
                        · linarith only [h1, h134, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                        · linarith only [h123, h124, h128, h134, hc12, hlam, hphi, ht23, u3elo4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h137 | h137
              · linarith only [h1, h123, h137, h3, hc13, hlam, hphi, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h139 | h139
                · linarith only [h139, h2, h3, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h141 | h141
                  · linarith only [h0, h141, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h143 | h143
                    · linarith only [h0, h143, h3, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h145 | h145
                      · linarith only [h1, h141, h145, h3, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h147 | h147
                        · linarith only [h1, h107, h123, h147, h3, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h149 | h149
                          · linarith only [h1, h137, h149, h3, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                          · linarith only [h147, h149, h2, h3, hc13, hlam, hphi, u3elo4]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h152 | h152
        · rcases m.htr 0 2 3 (by decide) (by decide) with h153 | h153
          · rcases m.htr 0 3 4 (by decide) (by decide) with h154 | h154
            · linarith only [h0, h153, h154, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h156 | h156
              · rcases m.htr 0 4 5 (by decide) (by decide) with h157 | h157
                · rcases m.htr 1 2 3 (by decide) (by decide) with h158 | h158
                  · linarith only [h0, h158, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h153, h158, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                · linarith only [h0, h153, h154, h156, h157, h2, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h162 | h162
                · rcases m.htr 1 2 3 (by decide) (by decide) with h163 | h163
                  · linarith only [h0, h163, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h153, h163, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h152, h162, h2, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h167 | h167
            · linarith only [h1, h167, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h169 | h169
              · rcases m.htr 0 4 5 (by decide) (by decide) with h170 | h170
                · rcases m.htr 1 2 3 (by decide) (by decide) with h171 | h171
                  · linarith only [h0, h171, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h173 | h173
                    · linarith only [h0, h173, h2, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h175 | h175
                      · linarith only [h1, h171, h175, h2, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h177 | h177
                        · linarith only [h1, h153, h167, h177, h2, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                        · linarith only [h1, h171, h177, h2, hc12, hlam, hphi, ht23, u3elo3]
                · linarith only [h1, h169, h170, h2, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h181 | h181
                · rcases m.htr 1 2 3 (by decide) (by decide) with h182 | h182
                  · linarith only [h0, h182, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h184 | h184
                    · linarith only [h1, h182, h184, h2, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h186 | h186
                      · linarith only [h1, h182, h186, h2, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h188 | h188
                        · linarith only [h1, h167, h188, h2, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                        · linarith only [h1, h182, h188, h2, hc12, hlam, hphi, ht23, u3elo3]
                · linarith only [h152, h181, h2, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h192 | h192
          · rcases m.htr 0 3 4 (by decide) (by decide) with h193 | h193
            · linarith only [h1, h193, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h195 | h195
              · linarith only [h1, h152, h193, h195, hc13, hlam, hphi, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h197 | h197
                · rcases m.htr 1 2 3 (by decide) (by decide) with h198 | h198
                  · linarith only [h0, h152, h197, h198, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h152, h192, h197, h198, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h201 | h201
                  · linarith only [h0, h2, h201, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                  · linarith only [h0, h192, h197, h2, h201, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h204 | h204
            · linarith only [h1, h2, h204, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h206 | h206
              · linarith only [h0, h152, h204, h206, hc12, hlam, hphi, ht23, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h208 | h208
                · rcases m.htr 1 2 3 (by decide) (by decide) with h209 | h209
                  · linarith only [h0, h152, h208, h209, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h211 | h211
                    · linarith only [h1, h152, h208, h209, h211, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h213 | h213
                      · linarith only [h1, h152, h208, h209, h213, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h215 | h215
                        · linarith only [h1, h152, h204, h208, h215, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                        · linarith only [h1, h2, h209, h215, hc12, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h218 | h218
                  · linarith only [h0, h192, h218, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h220 | h220
                    · linarith only [h1, h2, h218, h220, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h222 | h222
                      · linarith only [h1, h2, h208, h218, h222, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h224 | h224
                        · linarith only [h1, h2, h208, h224, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                        · linarith only [h1, h2, h218, h224, hc12, hlam, hphi, ht23, u3elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h228 | h228
    · rcases m.htr 0 1 4 (by decide) (by decide) with h229 | h229
      · rcases m.htr 0 1 5 (by decide) (by decide) with h230 | h230
        · rcases m.htr 0 2 3 (by decide) (by decide) with h231 | h231
          · rcases m.htr 0 3 4 (by decide) (by decide) with h232 | h232
            · rcases m.htr 0 3 5 (by decide) (by decide) with h233 | h233
              · rcases m.htr 0 4 5 (by decide) (by decide) with h234 | h234
                · rcases m.htr 1 2 3 (by decide) (by decide) with h235 | h235
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h236 | h236
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h237 | h237
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h238 | h238
                        · linarith only [h228, h238, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h232, h238, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h230, h237, hlam]
                    · linarith only [h0, h229, h236, hlam]
                  · linarith only [h0, h235, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h244 | h244
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h245 | h245
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h246 | h246
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h247 | h247
                        · linarith only [h228, h247, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h232, h247, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h230, h246, hlam]
                    · linarith only [h0, h229, h245, hlam]
                  · linarith only [h0, h244, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h253 | h253
                · linarith only [h232, h233, h253, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h255 | h255
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h256 | h256
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h257 | h257
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h258 | h258
                        · linarith only [h228, h258, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h232, h258, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h230, h257, hlam]
                    · linarith only [h0, h229, h256, hlam]
                  · linarith only [h0, h228, h255, hc13, hlam, hphi, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h264 | h264
              · rcases m.htr 0 4 5 (by decide) (by decide) with h265 | h265
                · rcases m.htr 1 2 3 (by decide) (by decide) with h266 | h266
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h267 | h267
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h268 | h268
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h269 | h269
                        · linarith only [h228, h232, h269, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h271 | h271
                          · linarith only [h0, h229, h269, h271, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                          · linarith only [h264, h271, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                      · linarith only [h0, h230, h268, hlam]
                    · linarith only [h0, h229, h267, hlam]
                  · linarith only [h0, h266, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h232, h264, h265, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h278 | h278
                · rcases m.htr 1 2 3 (by decide) (by decide) with h279 | h279
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h280 | h280
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h281 | h281
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h282 | h282
                        · linarith only [h0, h228, h232, h282, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h284 | h284
                          · linarith only [h0, h228, h264, h284, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h286 | h286
                            · linarith only [h0, h229, h286, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                            · linarith only [h0, h229, h278, h279, h282, h286, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · linarith only [h0, h230, h281, hlam]
                    · linarith only [h0, h229, h280, hlam]
                  · linarith only [h0, h279, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h292 | h292
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h293 | h293
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h294 | h294
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h295 | h295
                        · linarith only [h228, h232, h295, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h297 | h297
                          · linarith only [h0, h228, h264, h278, h297, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h299 | h299
                            · linarith only [h229, h278, h299, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h301 | h301
                              · linarith only [h0, h228, h292, h301, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h303 | h303
                                · linarith only [h228, h264, h292, h303, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h305 | h305
                                  · linarith only [h228, h232, h278, h292, h293, h305, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h307 | h307
                                    · linarith only [h228, h232, h278, h292, h307, hc23, hlam, hphi, u3elo3]
                                    · rcases h4bigk with h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c | h309c
                                      · have p309_0 := h309c.1
                                        have p309_1 := h309c.2.1
                                        have p309_2 := h309c.2.2.1
                                        have p309_3 := h309c.2.2.2
                                        linarith only [hlam, p309_0]
                                      · have p309_0 := h309c.1
                                        have p309_1 := h309c.2.1
                                        have p309_2 := h309c.2.2.1
                                        have p309_3 := h309c.2.2.2
                                        linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p309_1, u0elo3]
                                      · have p309_0 := h309c.1
                                        have p309_1 := h309c.2.1
                                        have p309_2 := h309c.2.2.1
                                        have p309_3 := h309c.2.2.2
                                        linarith only [h0, h230, h278, h301, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p309_1, u1elo1]
                                      · have p309_0 := h309c.1
                                        have p309_1 := h309c.2.1
                                        have p309_2 := h309c.2.2.1
                                        have p309_3 := h309c.2.2.2
                                        linarith only [h232, hlam, p309_0]
                                      · have p309_0 := h309c.1
                                        have p309_1 := h309c.2.1
                                        have p309_2 := h309c.2.2.1
                                        have p309_3 := h309c.2.2.2
                                        linarith only [h278, hlam, p309_0]
                                      · have p309_0 := h309c.1
                                        have p309_1 := h309c.2.1
                                        have p309_2 := h309c.2.2.1
                                        have p309_3 := h309c.2.2.2
                                        linarith only [h229, hlam, p309_1]
                                      · have p309_0 := h309c.1
                                        have p309_1 := h309c.2.1
                                        have p309_2 := h309c.2.2.1
                                        have p309_3 := h309c.2.2.2
                                        linarith only [hlam, p309_0]
                                      · have p309_0 := h309c.1
                                        have p309_1 := h309c.2.1
                                        have p309_2 := h309c.2.2.1
                                        have p309_3 := h309c.2.2.2
                                        linarith only [h0, h230, h299, h301, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p309_1, u1elo1]
                                      · have p309_0 := h309c.1
                                        have p309_1 := h309c.2.1
                                        have p309_2 := h309c.2.2.1
                                        have p309_3 := h309c.2.2.2
                                        linarith only [h295, hlam, p309_1]
                                      · have p309_0 := h309c.1
                                        have p309_1 := h309c.2.1
                                        have p309_2 := h309c.2.2.1
                                        have p309_3 := h309c.2.2.2
                                        linarith only [h299, hlam, p309_0]
                                      · have p309_0 := h309c.1
                                        have p309_1 := h309c.2.1
                                        have p309_2 := h309c.2.2.1
                                        have p309_3 := h309c.2.2.2
                                        linarith only [h228, h232, h292, h293, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p309_1, u1elo1]
                                      · have p309_0 := h309c.1
                                        have p309_1 := h309c.2.1
                                        have p309_2 := h309c.2.2.1
                                        have p309_3 := h309c.2.2.2
                                        linarith only [h293, hlam, p309_1]
                                      · have p309_0 := h309c.1
                                        have p309_1 := h309c.2.1
                                        have p309_2 := h309c.2.2.1
                                        have p309_3 := h309c.2.2.2
                                        linarith only [hlam, p309_0]
                                      · have p309_0 := h309c.1
                                        have p309_1 := h309c.2.1
                                        have p309_2 := h309c.2.2.1
                                        have p309_3 := h309c.2.2.2
                                        linarith only [h301, hlam, p309_1]
                                      · have p309_0 := h309c.1
                                        have p309_1 := h309c.2.1
                                        have p309_2 := h309c.2.2.1
                                        have p309_3 := h309c.2.2.2
                                        linarith only [h305, hlam, p309_0]
                                      · have p309_0 := h309c.1
                                        have p309_1 := h309c.2.1
                                        have p309_2 := h309c.2.2.1
                                        have p309_3 := h309c.2.2.2
                                        linarith only [h228, h232, h292, h307, hc23, hlam, hphi, p309_1, u3elo4]
                                      · have p309_0 := h309c.1
                                        have p309_1 := h309c.2.1
                                        have p309_2 := h309c.2.2.1
                                        have p309_3 := h309c.2.2.2
                                        linarith only [h293, h307, hc24, hc45, hlam, hphi, p309_1]
                                      · have p309_0 := h309c.1
                                        have p309_1 := h309c.2.1
                                        have p309_2 := h309c.2.2.1
                                        have p309_3 := h309c.2.2.2
                                        linarith only [h307, hc24, hc45, hlam, hphi, p309_1]
                                      · have p309_0 := h309c.1
                                        have p309_1 := h309c.2.1
                                        have p309_2 := h309c.2.2.1
                                        have p309_3 := h309c.2.2.2
                                        linarith only [hlam, p309_0]
                                      · have p309_0 := h309c.1
                                        have p309_1 := h309c.2.1
                                        have p309_2 := h309c.2.2.1
                                        have p309_3 := h309c.2.2.2
                                        linarith only [h307, hlam, p309_0]
                                      · have p309_0 := h309c.1
                                        have p309_1 := h309c.2.1
                                        have p309_2 := h309c.2.2.1
                                        have p309_3 := h309c.2.2.2
                                        rcases p309_3 (m.d 0 4) (by simp) with h330 | h330
                                        · linarith only [h330, hlam, p309_0]
                                        · rcases p309_3 (m.d 1 4) (by simp) with h332 | h332
                                          · linarith only [h299, h332, hlam]
                                          · rcases p309_3 (m.d 2 4) (by simp) with h334 | h334
                                            · linarith only [h305, h334, hlam]
                                            · rcases p309_3 (m.d 3 4) (by simp) with h336 | h336
                                              · linarith only [h307, h336, hlam]
                                              · linarith only [h232, h336, hlam]
                                      · have p309_0 := h309c.1
                                        have p309_1 := h309c.2.1
                                        have p309_2 := h309c.2.2.1
                                        have p309_3 := h309c.2.2.2
                                        rcases p309_3 (m.d 0 4) (by simp) with h339 | h339
                                        · linarith only [h278, h339, hlam]
                                        · linarith only [h229, h339, hlam]
                                      · have p309_0 := h309c.1
                                        have p309_1 := h309c.2.1
                                        have p309_2 := h309c.2.2.1
                                        have p309_3 := h309c.2.2.2
                                        rcases p309_3 (m.d 0 4) (by simp) with h342 | h342
                                        · linarith only [h278, h342, hlam]
                                        · linarith only [h229, h293, h342, hlam]
                                      · have p309_0 := h309c.1
                                        have p309_1 := h309c.2.1
                                        have p309_2 := h309c.2.2.1
                                        have p309_3 := h309c.2.2.2
                                        linarith only [h228, h232, h292, hc23, hc45, hlam, hphi, ht34, p309_1]
                                      · have p309_0 := h309c.1
                                        have p309_1 := h309c.2.1
                                        have p309_2 := h309c.2.2.1
                                        have p309_3 := h309c.2.2.2
                                        linarith only [hlam, p309_0]
                      · linarith only [h0, h230, h294, hlam]
                    · linarith only [h0, h229, h230, h293, hc15, hlam, hphi, ht0b, ht5b, u0elo3]
                  · linarith only [h0, h228, h292, hc13, hlam, hphi, u3elo2]
          · linarith only [h0, h228, h231, hc13, hlam, hphi, u3elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h351 | h351
          · rcases m.htr 0 3 4 (by decide) (by decide) with h352 | h352
            · rcases m.htr 0 3 5 (by decide) (by decide) with h353 | h353
              · linarith only [h228, h230, h353, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h355 | h355
                · linarith only [h229, h230, h355, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h357 | h357
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h358 | h358
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h359 | h359
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h360 | h360
                        · linarith only [h228, h230, h359, h360, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · linarith only [h352, h353, h357, h360, hc23, hlam, hphi, u3elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h363 | h363
                        · linarith only [h228, h363, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h352, h353, h357, h363, hc23, hlam, hphi, u3elo4]
                    · linarith only [h0, h229, h358, hlam]
                  · linarith only [h0, h357, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h368 | h368
              · linarith only [h229, h230, h352, h368, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h370 | h370
                · linarith only [h229, h230, h370, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h372 | h372
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h373 | h373
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h374 | h374
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h375 | h375
                        · linarith only [h228, h352, h375, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h377 | h377
                          · linarith only [h228, h230, h368, h374, h377, hc05, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                          · linarith only [h229, h230, h372, h375, h377, hc23, hlam, hphi, u3elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h380 | h380
                        · linarith only [h352, h380, hc03, hlam, hphi, u3elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h382 | h382
                          · linarith only [h228, h382, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h0, h229, h374, h380, h382, hc13, hlam, hphi, u3elo4]
                    · linarith only [h0, h229, h373, hlam]
                  · linarith only [h0, h372, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · linarith only [h0, h228, h351, hc13, hlam, hphi, u3elo2]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h388 | h388
        · rcases m.htr 0 2 3 (by decide) (by decide) with h389 | h389
          · rcases m.htr 0 3 4 (by decide) (by decide) with h390 | h390
            · linarith only [h228, h229, h390, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h392 | h392
              · rcases m.htr 0 4 5 (by decide) (by decide) with h393 | h393
                · rcases m.htr 1 2 3 (by decide) (by decide) with h394 | h394
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h395 | h395
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h396 | h396
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h397 | h397
                        · linarith only [h228, h390, h397, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h228, h229, h397, hc13, hlam, hphi, u3elo3]
                      · linarith only [h229, h388, h395, h396, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h401 | h401
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h402 | h402
                        · linarith only [h228, h402, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h0, h228, h394, h395, h402, hc23, hlam, hphi, u3elo3]
                      · linarith only [h0, h388, h401, hlam]
                  · linarith only [h0, h394, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h228, h229, h392, h393, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h408 | h408
                · rcases m.htr 1 2 3 (by decide) (by decide) with h409 | h409
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h410 | h410
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h411 | h411
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h412 | h412
                        · linarith only [h228, h412, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h228, h229, h412, hc13, hlam, hphi, u3elo3]
                      · linarith only [h229, h388, h410, h411, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h416 | h416
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h417 | h417
                        · linarith only [h228, h417, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h0, h228, h410, h417, hc13, hlam, hphi, u3elo3]
                      · linarith only [h0, h388, h416, hlam]
                  · linarith only [h0, h228, h409, hc13, hlam, hphi, u3elo2]
                · linarith only [h229, h388, h408, hlam]
          · linarith only [h0, h228, h389, hc13, hlam, hphi, u3elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h424 | h424
          · rcases m.htr 0 3 4 (by decide) (by decide) with h425 | h425
            · linarith only [h228, h229, h425, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h427 | h427
              · linarith only [h228, h388, h427, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h429 | h429
                · rcases m.htr 1 2 3 (by decide) (by decide) with h430 | h430
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h431 | h431
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h432 | h432
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h433 | h433
                        · linarith only [h228, h425, h433, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h228, h229, h430, h433, hc23, hlam, hphi, u3elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h436 | h436
                        · linarith only [h228, h229, h431, h432, h436, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h228, h229, h430, h436, hc23, hlam, hphi, u3elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h439 | h439
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h440 | h440
                        · linarith only [h228, h440, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h228, h388, h431, h439, h440, hc13, hlam, hphi, u3elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h443 | h443
                        · linarith only [h0, h228, h431, h443, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                        · linarith only [h0, h228, h430, h431, h443, hc23, hlam, hphi, u3elo3]
                  · linarith only [h0, h430, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h447 | h447
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h448 | h448
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h449 | h449
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h450 | h450
                        · linarith only [h228, h229, h429, h450, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                        · linarith only [h228, h229, h447, h450, hc23, hlam, hphi, u3elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h453 | h453
                        · linarith only [h228, h229, h448, h449, h453, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h228, h229, h447, h453, hc23, hlam, hphi, u3elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h456 | h456
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h457 | h457
                        · linarith only [h228, h457, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h228, h388, h448, h456, h457, hc13, hlam, hphi, u3elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h460 | h460
                        · linarith only [h228, h460, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h0, h228, h447, h448, h460, hc23, hlam, hphi, u3elo3]
                  · linarith only [h0, h447, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · linarith only [h0, h228, h424, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h465 | h465
      · rcases m.htr 0 1 5 (by decide) (by decide) with h466 | h466
        · rcases m.htr 0 2 3 (by decide) (by decide) with h467 | h467
          · rcases m.htr 0 3 4 (by decide) (by decide) with h468 | h468
            · rcases m.htr 0 3 5 (by decide) (by decide) with h469 | h469
              · rcases m.htr 0 4 5 (by decide) (by decide) with h470 | h470
                · rcases m.htr 1 2 3 (by decide) (by decide) with h471 | h471
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h472 | h472
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h473 | h473
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h474 | h474
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h475 | h475
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h476 | h476
                            · linarith only [h228, h465, h476, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                            · linarith only [h228, h465, h470, h476, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                          · linarith only [h228, h475, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h228, h467, h468, h474, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h228, h466, h471, h473, hlam]
                    · linarith only [h228, h465, h471, h472, hlam]
                  · linarith only [h467, h471, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h484 | h484
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h485 | h485
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h486 | h486
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h487 | h487
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h488 | h488
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h489 | h489
                            · linarith only [h465, h470, h489, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h491 | h491
                              · linarith only [h467, h491, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · linarith only [h467, h468, h491, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h228, h488, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h228, h465, h485, h487, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h228, h466, h484, h486, hlam]
                    · linarith only [h228, h465, h484, h485, hlam]
                  · linarith only [h0, h484, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · linarith only [h228, h466, h469, hlam]
            · linarith only [h228, h465, h468, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h501 | h501
            · rcases m.htr 0 3 5 (by decide) (by decide) with h502 | h502
              · rcases m.htr 0 4 5 (by decide) (by decide) with h503 | h503
                · rcases m.htr 1 2 3 (by decide) (by decide) with h504 | h504
                  · linarith only [h0, h465, h467, h504, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · linarith only [h0, h465, h504, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h507 | h507
                  · linarith only [h0, h465, h467, h507, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · linarith only [h0, h465, h507, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · linarith only [h0, h466, h467, h502, hlam]
            · linarith only [h0, h465, h467, h501, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h512 | h512
          · rcases m.htr 0 3 4 (by decide) (by decide) with h513 | h513
            · rcases m.htr 0 3 5 (by decide) (by decide) with h514 | h514
              · rcases m.htr 0 4 5 (by decide) (by decide) with h515 | h515
                · linarith only [h465, h466, h515, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h517 | h517
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h518 | h518
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h519 | h519
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h520 | h520
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h521 | h521
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h522 | h522
                            · linarith only [h465, h515, h522, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h524 | h524
                              · linarith only [h512, h524, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · linarith only [h512, h513, h524, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h228, h465, h512, h514, h518, h521, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h228, h465, h518, h520, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h529 | h529
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h530 | h530
                          · linarith only [h517, h519, h530, hlam]
                          · linarith only [h228, h465, h512, h514, h518, h530, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · linarith only [h228, h465, h518, h529, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h228, h465, h517, h518, hlam]
                  · linarith only [h0, h517, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h536 | h536
                · linarith only [h228, h465, h514, h536, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h538 | h538
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h539 | h539
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h540 | h540
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h541 | h541
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h542 | h542
                          · linarith only [h228, h514, h542, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h228, h465, h539, h542, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h228, h465, h539, h541, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h546 | h546
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h547 | h547
                          · linarith only [h228, h465, h514, h539, h547, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                          · linarith only [h228, h465, h539, h547, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h228, h465, h539, h546, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h228, h465, h539, hc12, hlam, hphi, ht23, u3elo1]
                  · linarith only [h0, h538, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h228, h465, h513, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h554 | h554
            · rcases m.htr 0 3 5 (by decide) (by decide) with h555 | h555
              · rcases m.htr 0 4 5 (by decide) (by decide) with h556 | h556
                · linarith only [h465, h466, h556, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h558 | h558
                  · linarith only [h0, h465, h512, h558, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · linarith only [h0, h465, h558, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h561 | h561
                · linarith only [h0, h465, h512, h555, h561, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h563 | h563
                  · linarith only [h0, h465, h512, h563, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · linarith only [h0, h465, h563, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
            · linarith only [h0, h465, h512, h554, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h567 | h567
        · rcases m.htr 0 2 3 (by decide) (by decide) with h568 | h568
          · rcases m.htr 0 3 4 (by decide) (by decide) with h569 | h569
            · rcases m.htr 0 3 5 (by decide) (by decide) with h570 | h570
              · rcases m.htr 0 4 5 (by decide) (by decide) with h571 | h571
                · rcases m.htr 1 2 3 (by decide) (by decide) with h572 | h572
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h573 | h573
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h574 | h574
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h575 | h575
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h576 | h576
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h577 | h577
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h578 | h578
                              · linarith only [h568, h578, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · linarith only [h569, h578, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h465, h571, h577, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                          · linarith only [h465, h567, h574, h575, h576, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                        · linarith only [h568, h569, h575, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h228, h567, h572, h574, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h585 | h585
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h586 | h586
                        · linarith only [h572, h573, h586, hlam]
                        · linarith only [h228, h568, h569, h586, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h228, h567, h572, h585, hlam]
                  · linarith only [h0, h567, h572, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                · linarith only [h465, h567, h571, hlam]
              · linarith only [h228, h567, h570, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h593 | h593
              · rcases m.htr 0 4 5 (by decide) (by decide) with h594 | h594
                · rcases m.htr 1 2 3 (by decide) (by decide) with h595 | h595
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h596 | h596
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h597 | h597
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h598 | h598
                        · linarith only [h228, h569, h595, h598, hc01, hlam, hphi, u1elo1]
                        · linarith only [h228, h567, h597, h598, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h567, h596, h597, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h602 | h602
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h603 | h603
                        · linarith only [h228, h569, h595, h603, hc01, hlam, hphi, u1elo1]
                        · linarith only [h228, h567, h602, h603, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h228, h567, h602, hc12, hlam, hphi, ht23, u3elo1]
                  · linarith only [h0, h595, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h465, h567, h594, hlam]
              · linarith only [h228, h567, h593, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h610 | h610
            · rcases m.htr 0 3 5 (by decide) (by decide) with h611 | h611
              · rcases m.htr 0 4 5 (by decide) (by decide) with h612 | h612
                · rcases m.htr 1 2 3 (by decide) (by decide) with h613 | h613
                  · linarith only [h0, h567, h568, h613, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · linarith only [h0, h567, h613, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                · linarith only [h465, h567, h612, hlam]
              · linarith only [h0, h567, h568, h611, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h618 | h618
              · rcases m.htr 0 4 5 (by decide) (by decide) with h619 | h619
                · rcases m.htr 1 2 3 (by decide) (by decide) with h620 | h620
                  · linarith only [h0, h567, h568, h620, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · linarith only [h0, h567, h620, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                · linarith only [h0, h567, h568, h610, h619, hlam]
              · linarith only [h0, h567, h568, h618, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h625 | h625
          · rcases m.htr 0 3 4 (by decide) (by decide) with h626 | h626
            · rcases m.htr 0 3 5 (by decide) (by decide) with h627 | h627
              · rcases m.htr 0 4 5 (by decide) (by decide) with h628 | h628
                · rcases m.htr 1 2 3 (by decide) (by decide) with h629 | h629
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h630 | h630
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h631 | h631
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h632 | h632
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h633 | h633
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h634 | h634
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h635 | h635
                              · linarith only [h625, h635, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · linarith only [h626, h635, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h465, h625, h626, h628, h634, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h625, h627, h633, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h228, h626, h632, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h641 | h641
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h642 | h642
                          · linarith only [h629, h631, h642, hlam]
                          · linarith only [h625, h627, h642, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h228, h626, h641, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h646 | h646
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h647 | h647
                        · linarith only [h629, h630, h647, hlam]
                        · linarith only [h625, h626, h647, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h650 | h650
                        · linarith only [h629, h630, h650, hlam]
                        · linarith only [h625, h626, h650, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h629, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h654 | h654
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h655 | h655
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h656 | h656
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h657 | h657
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h658 | h658
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h659 | h659
                            · linarith only [h465, h628, h657, h659, hc01, hlam, hphi, ht12, ht23, u3elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h661 | h661
                              · linarith only [h625, h661, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                              · linarith only [h625, h626, h661, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                          · linarith only [h625, h627, h658, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h228, h626, h627, h657, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h666 | h666
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h667 | h667
                          · linarith only [h654, h656, h667, hlam]
                          · linarith only [h228, h667, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h228, h626, h666, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h671 | h671
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h672 | h672
                        · linarith only [h654, h655, h672, hlam]
                        · linarith only [h625, h626, h672, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h675 | h675
                        · linarith only [h654, h655, h675, hlam]
                        · linarith only [h625, h626, h675, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h654, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h679 | h679
                · linarith only [h626, h627, h679, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h681 | h681
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h682 | h682
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h683 | h683
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h684 | h684
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h685 | h685
                          · linarith only [h626, h627, h681, h685, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · linarith only [h228, h685, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h228, h626, h684, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h689 | h689
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h690 | h690
                          · linarith only [h626, h627, h690, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                          · linarith only [h228, h690, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h228, h625, h626, h689, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h694 | h694
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h695 | h695
                        · linarith only [h681, h682, h695, hlam]
                        · linarith only [h626, h627, h695, hc13, hlam, hphi, u3elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h698 | h698
                        · linarith only [h681, h682, h698, hlam]
                        · linarith only [h626, h627, h698, hc13, hlam, hphi, u3elo4]
                  · linarith only [h0, h681, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h702 | h702
              · rcases m.htr 0 4 5 (by decide) (by decide) with h703 | h703
                · rcases m.htr 1 2 3 (by decide) (by decide) with h704 | h704
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h705 | h705
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h706 | h706
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h707 | h707
                        · linarith only [h626, h702, h707, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · linarith only [h228, h707, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h710 | h710
                        · linarith only [h567, h626, h702, h710, hc01, hlam, hphi, u1elo2]
                        · linarith only [h228, h710, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h713 | h713
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h714 | h714
                        · linarith only [h567, h626, h702, h714, hc01, hlam, hphi, u1elo2]
                        · linarith only [h228, h714, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h717 | h717
                        · linarith only [h567, h626, h702, h717, hc01, hlam, hphi, u1elo2]
                        · linarith only [h228, h717, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h625, h704, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h626, h702, h703, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h722 | h722
                · rcases m.htr 1 2 3 (by decide) (by decide) with h723 | h723
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h724 | h724
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h725 | h725
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h726 | h726
                        · linarith only [h626, h726, hc03, hlam, hphi, u3elo1]
                        · linarith only [h228, h726, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h729 | h729
                        · linarith only [h228, h626, h729, hc01, hlam, hphi, u1elo2]
                        · linarith only [h228, h729, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h732 | h732
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h733 | h733
                        · linarith only [h228, h626, h733, hc01, hlam, hphi, u1elo2]
                        · linarith only [h228, h733, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h736 | h736
                        · linarith only [h228, h626, h736, hc01, hlam, hphi, u1elo2]
                        · linarith only [h228, h736, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h625, h723, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h740 | h740
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h741 | h741
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h742 | h742
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h743 | h743
                        · linarith only [h228, h626, h743, hc01, hlam, hphi, u1elo2]
                        · linarith only [h228, h743, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h746 | h746
                        · linarith only [h228, h626, h746, hc01, hlam, hphi, u1elo2]
                        · linarith only [h228, h746, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h749 | h749
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h750 | h750
                        · linarith only [h228, h626, h750, hc01, hlam, hphi, u1elo2]
                        · linarith only [h228, h750, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h753 | h753
                        · linarith only [h228, h626, h753, hc01, hlam, hphi, u1elo2]
                        · linarith only [h228, h753, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h625, h702, h740, hc02, hlam, hphi, ht23, u3elo4]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h757 | h757
            · rcases m.htr 0 3 5 (by decide) (by decide) with h758 | h758
              · rcases m.htr 0 4 5 (by decide) (by decide) with h759 | h759
                · rcases m.htr 1 2 3 (by decide) (by decide) with h760 | h760
                  · linarith only [h0, h625, h760, hc01, hlam, hphi, u1elo1]
                  · linarith only [h0, h760, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h763 | h763
                  · linarith only [h0, h625, h763, hc01, hlam, hphi, u1elo1]
                  · linarith only [h0, h763, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h766 | h766
                · linarith only [h757, h758, h766, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h768 | h768
                  · linarith only [h0, h625, h768, hc01, hlam, hphi, u1elo1]
                  · linarith only [h0, h768, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h771 | h771
              · rcases m.htr 0 4 5 (by decide) (by decide) with h772 | h772
                · rcases m.htr 1 2 3 (by decide) (by decide) with h773 | h773
                  · linarith only [h0, h625, h773, hc01, hlam, hphi, u1elo1]
                  · linarith only [h0, h773, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h757, h771, h772, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h777 | h777
                · rcases m.htr 1 2 3 (by decide) (by decide) with h778 | h778
                  · linarith only [h0, h625, h778, hc01, hlam, hphi, u1elo1]
                  · linarith only [h0, h778, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h781 | h781
                  · linarith only [h0, h625, h781, hc01, hlam, hphi, u1elo1]
                  · linarith only [h0, h781, hc01, hlam, hphi, ht12, ht23, u3elo2]

end R2N4
