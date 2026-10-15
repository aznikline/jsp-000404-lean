import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_75S11

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_22_13_15_H_I_L_R_L_R_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h364 | h364
  · rcases m.htr 0 2 5 (by decide) (by decide) with h365 | h365
    · rcases m.htr 1 2 4 (by decide) (by decide) with h366 | h366
      · rcases m.htr 1 2 5 (by decide) (by decide) with h367 | h367
        · rcases m.htr 2 3 4 (by decide) (by decide) with h368 | h368
          · rcases m.htr 2 4 5 (by decide) (by decide) with h369 | h369
            · rcases m.htr 3 4 5 (by decide) (by decide) with h370 | h370
              · linarith only [h364, h368, h370, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
              · linarith only [h366, h369, h370, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h373 | h373
              · linarith only [h0, h364, h368, h369, h373, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · rcases h2bigk with h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c | h375c
                · have p375_0 := h375c.1
                  have p375_1 := h375c.2.1
                  have p375_2 := h375c.2.2.1
                  have p375_3 := h375c.2.2.2
                  linarith only [hlam, p375_0]
                · have p375_0 := h375c.1
                  have p375_1 := h375c.2.1
                  have p375_2 := h375c.2.2.1
                  have p375_3 := h375c.2.2.2
                  linarith only [h0, hlam, p375_0]
                · have p375_0 := h375c.1
                  have p375_1 := h375c.2.1
                  have p375_2 := h375c.2.2.1
                  have p375_3 := h375c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p375_1, u3ehi2]
                · have p375_0 := h375c.1
                  have p375_1 := h375c.2.1
                  have p375_2 := h375c.2.2.1
                  have p375_3 := h375c.2.2.2
                  linarith only [h0, h368, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p375_1, u3ehi3]
                · have p375_0 := h375c.1
                  have p375_1 := h375c.2.1
                  have p375_2 := h375c.2.2.1
                  have p375_3 := h375c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p375_1, u5ehi2]
                · have p375_0 := h375c.1
                  have p375_1 := h375c.2.1
                  have p375_2 := h375c.2.2.1
                  have p375_3 := h375c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p375_1]
                · have p375_0 := h375c.1
                  have p375_1 := h375c.2.1
                  have p375_2 := h375c.2.2.1
                  have p375_3 := h375c.2.2.2
                  linarith only [hlam, p375_0]
                · have p375_0 := h375c.1
                  have p375_1 := h375c.2.1
                  have p375_2 := h375c.2.2.1
                  have p375_3 := h375c.2.2.2
                  linarith only [h368, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p375_1, u3ehi3]
                · have p375_0 := h375c.1
                  have p375_1 := h375c.2.1
                  have p375_2 := h375c.2.2.1
                  have p375_3 := h375c.2.2.2
                  linarith only [h368, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p375_1, u3ehi3]
                · have p375_0 := h375c.1
                  have p375_1 := h375c.2.1
                  have p375_2 := h375c.2.2.1
                  have p375_3 := h375c.2.2.2
                  linarith only [h368, h369, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p375_1, u3ehi3]
                · have p375_0 := h375c.1
                  have p375_1 := h375c.2.1
                  have p375_2 := h375c.2.2.1
                  have p375_3 := h375c.2.2.2
                  linarith only [h364, hlam, p375_0]
                · have p375_0 := h375c.1
                  have p375_1 := h375c.2.1
                  have p375_2 := h375c.2.2.1
                  have p375_3 := h375c.2.2.2
                  linarith only [h364, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p375_1]
                · have p375_0 := h375c.1
                  have p375_1 := h375c.2.1
                  have p375_2 := h375c.2.2.1
                  have p375_3 := h375c.2.2.2
                  linarith only [hlam, p375_0]
                · have p375_0 := h375c.1
                  have p375_1 := h375c.2.1
                  have p375_2 := h375c.2.2.1
                  have p375_3 := h375c.2.2.2
                  linarith only [h0, h364, h368, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p375_1, u3ehi3]
                · have p375_0 := h375c.1
                  have p375_1 := h375c.2.1
                  have p375_2 := h375c.2.2.1
                  have p375_3 := h375c.2.2.2
                  linarith only [h0, h364, h368, h369, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p375_1, u3ehi3]
                · have p375_0 := h375c.1
                  have p375_1 := h375c.2.1
                  have p375_2 := h375c.2.2.1
                  have p375_3 := h375c.2.2.2
                  linarith only [h364, h365, h369, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p375_1, u3ehi2]
                · have p375_0 := h375c.1
                  have p375_1 := h375c.2.1
                  have p375_2 := h375c.2.2.1
                  have p375_3 := h375c.2.2.2
                  linarith only [h366, hlam, p375_0]
                · have p375_0 := h375c.1
                  have p375_1 := h375c.2.1
                  have p375_2 := h375c.2.2.1
                  have p375_3 := h375c.2.2.2
                  linarith only [h368, hlam, p375_0]
                · have p375_0 := h375c.1
                  have p375_1 := h375c.2.1
                  have p375_2 := h375c.2.2.1
                  have p375_3 := h375c.2.2.2
                  linarith only [hlam, p375_0]
                · have p375_0 := h375c.1
                  have p375_1 := h375c.2.1
                  have p375_2 := h375c.2.2.1
                  have p375_3 := h375c.2.2.2
                  linarith only [h369, hlam, p375_0]
                · have p375_0 := h375c.1
                  have p375_1 := h375c.2.1
                  have p375_2 := h375c.2.2.1
                  have p375_3 := h375c.2.2.2
                  linarith only [h365, hlam, p375_0]
                · have p375_0 := h375c.1
                  have p375_1 := h375c.2.1
                  have p375_2 := h375c.2.2.1
                  have p375_3 := h375c.2.2.2
                  linarith only [h367, hlam, p375_0]
                · have p375_0 := h375c.1
                  have p375_1 := h375c.2.1
                  have p375_2 := h375c.2.2.1
                  have p375_3 := h375c.2.2.2
                  linarith only [h365, h368, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p375_1, u3ehi3]
                · have p375_0 := h375c.1
                  have p375_1 := h375c.2.1
                  have p375_2 := h375c.2.2.1
                  have p375_3 := h375c.2.2.2
                  linarith only [h0, h365, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p375_1]
                · have p375_0 := h375c.1
                  have p375_1 := h375c.2.1
                  have p375_2 := h375c.2.2.1
                  have p375_3 := h375c.2.2.2
                  linarith only [hlam, p375_0]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h401 | h401
            · rcases m.htr 3 4 5 (by decide) (by decide) with h402 | h402
              · rcases h2bigk with h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c
                · have p403_0 := h403c.1
                  have p403_1 := h403c.2.1
                  have p403_2 := h403c.2.2.1
                  have p403_3 := h403c.2.2.2
                  linarith only [hlam, p403_0]
                · have p403_0 := h403c.1
                  have p403_1 := h403c.2.1
                  have p403_2 := h403c.2.2.1
                  have p403_3 := h403c.2.2.2
                  linarith only [h0, hlam, p403_0]
                · have p403_0 := h403c.1
                  have p403_1 := h403c.2.1
                  have p403_2 := h403c.2.2.1
                  have p403_3 := h403c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p403_1, u3ehi2]
                · have p403_0 := h403c.1
                  have p403_1 := h403c.2.1
                  have p403_2 := h403c.2.2.1
                  have p403_3 := h403c.2.2.2
                  linarith only [h0, h401, hc12, hlam, hphi, ht01, ht0b, ht5b, p403_1, u5ehi4]
                · have p403_0 := h403c.1
                  have p403_1 := h403c.2.1
                  have p403_2 := h403c.2.2.1
                  have p403_3 := h403c.2.2.2
                  linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p403_1, u5ehi2]
                · have p403_0 := h403c.1
                  have p403_1 := h403c.2.1
                  have p403_2 := h403c.2.2.1
                  have p403_3 := h403c.2.2.2
                  linarith only [h365, hc12, hlam, hphi, ht01, ht0b, ht5b, p403_1, u5ehi0]
                · have p403_0 := h403c.1
                  have p403_1 := h403c.2.1
                  have p403_2 := h403c.2.2.1
                  have p403_3 := h403c.2.2.2
                  linarith only [hlam, p403_0]
                · have p403_0 := h403c.1
                  have p403_1 := h403c.2.1
                  have p403_2 := h403c.2.2.1
                  have p403_3 := h403c.2.2.2
                  linarith only [hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p403_1, u3ehi2]
                · have p403_0 := h403c.1
                  have p403_1 := h403c.2.1
                  have p403_2 := h403c.2.2.1
                  have p403_3 := h403c.2.2.2
                  linarith only [h401, hc12, hlam, hphi, ht01, ht0b, ht5b, p403_1, u5ehi4]
                · have p403_0 := h403c.1
                  have p403_1 := h403c.2.1
                  have p403_2 := h403c.2.2.1
                  have p403_3 := h403c.2.2.2
                  linarith only [h401, hc12, hlam, hphi, ht01, ht0b, ht5b, p403_1, u5ehi4]
                · have p403_0 := h403c.1
                  have p403_1 := h403c.2.1
                  have p403_2 := h403c.2.2.1
                  have p403_3 := h403c.2.2.2
                  linarith only [h364, hlam, p403_0]
                · have p403_0 := h403c.1
                  have p403_1 := h403c.2.1
                  have p403_2 := h403c.2.2.1
                  have p403_3 := h403c.2.2.2
                  linarith only [h364, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p403_1]
                · have p403_0 := h403c.1
                  have p403_1 := h403c.2.1
                  have p403_2 := h403c.2.2.1
                  have p403_3 := h403c.2.2.2
                  linarith only [hlam, p403_0]
                · have p403_0 := h403c.1
                  have p403_1 := h403c.2.1
                  have p403_2 := h403c.2.2.1
                  have p403_3 := h403c.2.2.2
                  linarith only [h368, hlam, p403_1]
                · have p403_0 := h403c.1
                  have p403_1 := h403c.2.1
                  have p403_2 := h403c.2.2.1
                  have p403_3 := h403c.2.2.2
                  linarith only [h368, h401, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p403_1, u5ehi4]
                · have p403_0 := h403c.1
                  have p403_1 := h403c.2.1
                  have p403_2 := h403c.2.2.1
                  have p403_3 := h403c.2.2.2
                  linarith only [hc02, hc24, hlam, hphi, p403_1]
                · have p403_0 := h403c.1
                  have p403_1 := h403c.2.1
                  have p403_2 := h403c.2.2.1
                  have p403_3 := h403c.2.2.2
                  linarith only [h366, hlam, p403_0]
                · have p403_0 := h403c.1
                  have p403_1 := h403c.2.1
                  have p403_2 := h403c.2.2.1
                  have p403_3 := h403c.2.2.2
                  linarith only [h366, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p403_1, u3ehi2]
                · have p403_0 := h403c.1
                  have p403_1 := h403c.2.1
                  have p403_2 := h403c.2.2.1
                  have p403_3 := h403c.2.2.2
                  linarith only [hlam, p403_0]
                · have p403_0 := h403c.1
                  have p403_1 := h403c.2.1
                  have p403_2 := h403c.2.2.1
                  have p403_3 := h403c.2.2.2
                  linarith only [h366, h401, hc12, hlam, hphi, ht01, ht0b, ht5b, p403_1, u5ehi4]
                · have p403_0 := h403c.1
                  have p403_1 := h403c.2.1
                  have p403_2 := h403c.2.2.1
                  have p403_3 := h403c.2.2.2
                  linarith only [h365, hlam, p403_0]
                · have p403_0 := h403c.1
                  have p403_1 := h403c.2.1
                  have p403_2 := h403c.2.2.1
                  have p403_3 := h403c.2.2.2
                  linarith only [h367, hlam, p403_0]
                · have p403_0 := h403c.1
                  have p403_1 := h403c.2.1
                  have p403_2 := h403c.2.2.1
                  have p403_3 := h403c.2.2.2
                  linarith only [h365, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p403_1, u3ehi2]
                · have p403_0 := h403c.1
                  have p403_1 := h403c.2.1
                  have p403_2 := h403c.2.2.1
                  have p403_3 := h403c.2.2.2
                  linarith only [h401, hlam, p403_1]
                · have p403_0 := h403c.1
                  have p403_1 := h403c.2.1
                  have p403_2 := h403c.2.2.1
                  have p403_3 := h403c.2.2.2
                  linarith only [hlam, p403_0]
              · linarith only [h368, h402, hc45, hlam, hphi, ht34, u3ehi2]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h430 | h430
              · linarith only [h368, h401, h430, hc34, hlam, hphi, u3ehi2]
              · linarith only [h368, h430, hc45, hlam, hphi, ht34, u3ehi2]
        · linarith only [h0, h365, h367, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h434 | h434
        · rcases m.htr 2 3 4 (by decide) (by decide) with h435 | h435
          · linarith only [h0, h364, h366, h435, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
          · linarith only [h0, h364, h366, h435, hc34, hlam, hphi, u3ehi2]
        · linarith only [h0, h365, h434, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h439 | h439
      · rcases m.htr 1 2 5 (by decide) (by decide) with h440 | h440
        · linarith only [h364, h365, h440, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h442 | h442
          · linarith only [h0, h364, h440, h442, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h444 | h444
            · linarith only [h439, h440, h444, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
            · linarith only [h0, h364, h440, h444, hc45, hlam, hphi, ht34, u3ehi2]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h447 | h447
        · linarith only [h364, h365, h447, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h449 | h449
          · linarith only [h0, h364, h447, h449, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
          · linarith only [h0, h364, h439, h449, hc34, hlam, hphi, u3ehi2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h452 | h452
    · rcases m.htr 1 2 4 (by decide) (by decide) with h453 | h453
      · rcases m.htr 1 2 5 (by decide) (by decide) with h454 | h454
        · rcases m.htr 2 3 4 (by decide) (by decide) with h455 | h455
          · rcases m.htr 2 4 5 (by decide) (by decide) with h456 | h456
            · rcases m.htr 3 4 5 (by decide) (by decide) with h457 | h457
              · rcases h2bigk with h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c
                · have p458_0 := h458c.1
                  have p458_1 := h458c.2.1
                  have p458_2 := h458c.2.2.1
                  have p458_3 := h458c.2.2.2
                  linarith only [hlam, p458_0]
                · have p458_0 := h458c.1
                  have p458_1 := h458c.2.1
                  have p458_2 := h458c.2.2.1
                  have p458_3 := h458c.2.2.2
                  linarith only [h0, hlam, p458_0]
                · have p458_0 := h458c.1
                  have p458_1 := h458c.2.1
                  have p458_2 := h458c.2.2.1
                  have p458_3 := h458c.2.2.2
                  linarith only [h364, hlam, p458_0]
                · have p458_0 := h458c.1
                  have p458_1 := h458c.2.1
                  have p458_2 := h458c.2.2.1
                  have p458_3 := h458c.2.2.2
                  linarith only [h364, h455, h457, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p458_1, u5ehi4]
                · have p458_0 := h458c.1
                  have p458_1 := h458c.2.1
                  have p458_2 := h458c.2.2.1
                  have p458_3 := h458c.2.2.2
                  linarith only [h364, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p458_1, u5ehi2]
                · have p458_0 := h458c.1
                  have p458_1 := h458c.2.1
                  have p458_2 := h458c.2.2.1
                  have p458_3 := h458c.2.2.2
                  linarith only [h452, hc12, hlam, hphi, ht01, ht0b, ht5b, p458_1, u5ehi0]
                · have p458_0 := h458c.1
                  have p458_1 := h458c.2.1
                  have p458_2 := h458c.2.2.1
                  have p458_3 := h458c.2.2.2
                  linarith only [hlam, p458_0]
                · have p458_0 := h458c.1
                  have p458_1 := h458c.2.1
                  have p458_2 := h458c.2.2.1
                  have p458_3 := h458c.2.2.2
                  linarith only [hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p458_1, u3ehi2]
                · have p458_0 := h458c.1
                  have p458_1 := h458c.2.1
                  have p458_2 := h458c.2.2.1
                  have p458_3 := h458c.2.2.2
                  linarith only [h455, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p458_1, u3ehi3]
                · have p458_0 := h458c.1
                  have p458_1 := h458c.2.1
                  have p458_2 := h458c.2.2.1
                  have p458_3 := h458c.2.2.2
                  linarith only [h456, hc12, hlam, hphi, ht01, ht0b, ht5b, p458_1, u5ehi4]
                · have p458_0 := h458c.1
                  have p458_1 := h458c.2.1
                  have p458_2 := h458c.2.2.1
                  have p458_3 := h458c.2.2.2
                  linarith only [h452, h456, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p458_1, u5ehi4]
                · have p458_0 := h458c.1
                  have p458_1 := h458c.2.1
                  have p458_2 := h458c.2.2.1
                  have p458_3 := h458c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p458_1]
                · have p458_0 := h458c.1
                  have p458_1 := h458c.2.1
                  have p458_2 := h458c.2.2.1
                  have p458_3 := h458c.2.2.2
                  linarith only [hlam, p458_0]
                · have p458_0 := h458c.1
                  have p458_1 := h458c.2.1
                  have p458_2 := h458c.2.2.1
                  have p458_3 := h458c.2.2.2
                  linarith only [h455, h457, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p458_1, u5ehi4]
                · have p458_0 := h458c.1
                  have p458_1 := h458c.2.1
                  have p458_2 := h458c.2.2.1
                  have p458_3 := h458c.2.2.2
                  linarith only [h456, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p458_1, u5ehi4]
                · have p458_0 := h458c.1
                  have p458_1 := h458c.2.1
                  have p458_2 := h458c.2.2.1
                  have p458_3 := h458c.2.2.2
                  linarith only [h452, h453, h456, hc12, hlam, hphi, ht01, ht0b, ht5b, p458_1, u5ehi4]
                · have p458_0 := h458c.1
                  have p458_1 := h458c.2.1
                  have p458_2 := h458c.2.2.1
                  have p458_3 := h458c.2.2.2
                  linarith only [h453, hlam, p458_0]
                · have p458_0 := h458c.1
                  have p458_1 := h458c.2.1
                  have p458_2 := h458c.2.2.1
                  have p458_3 := h458c.2.2.2
                  linarith only [h455, hlam, p458_0]
                · have p458_0 := h458c.1
                  have p458_1 := h458c.2.1
                  have p458_2 := h458c.2.2.1
                  have p458_3 := h458c.2.2.2
                  linarith only [hlam, p458_0]
                · have p458_0 := h458c.1
                  have p458_1 := h458c.2.1
                  have p458_2 := h458c.2.2.1
                  have p458_3 := h458c.2.2.2
                  linarith only [h453, h456, hc12, hlam, hphi, ht01, ht0b, ht5b, p458_1, u5ehi4]
                · have p458_0 := h458c.1
                  have p458_1 := h458c.2.1
                  have p458_2 := h458c.2.2.1
                  have p458_3 := h458c.2.2.2
                  linarith only [h452, hlam, p458_0]
                · have p458_0 := h458c.1
                  have p458_1 := h458c.2.1
                  have p458_2 := h458c.2.2.1
                  have p458_3 := h458c.2.2.2
                  linarith only [h454, hlam, p458_0]
                · have p458_0 := h458c.1
                  have p458_1 := h458c.2.1
                  have p458_2 := h458c.2.2.1
                  have p458_3 := h458c.2.2.2
                  linarith only [h452, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p458_1, u3ehi2]
                · have p458_0 := h458c.1
                  have p458_1 := h458c.2.1
                  have p458_2 := h458c.2.2.1
                  have p458_3 := h458c.2.2.2
                  linarith only [h456, hlam, p458_1]
                · have p458_0 := h458c.1
                  have p458_1 := h458c.2.1
                  have p458_2 := h458c.2.2.1
                  have p458_3 := h458c.2.2.2
                  linarith only [hlam, p458_0]
              · linarith only [h453, h456, h457, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h485 | h485
              · linarith only [h364, h452, h455, h456, h485, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · rcases h2bigk with h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c | h487c
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [hlam, p487_0]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h0, hlam, p487_0]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h364, hlam, p487_0]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h364, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p487_1]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h364, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p487_1, u5ehi2]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p487_1]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [hlam, p487_0]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h364, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p487_1, u3ehi0]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h455, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p487_1, u3ehi3]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h455, h456, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p487_1, u3ehi3]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h452, h455, h456, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p487_1, u3ehi3]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p487_1]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [hlam, p487_0]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h455, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p487_1, u3ehi3]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h455, h456, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p487_1, u3ehi3]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h452, h456, hlam, p487_1]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h453, hlam, p487_0]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h455, hlam, p487_0]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [hlam, p487_0]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h456, hlam, p487_0]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h452, hlam, p487_0]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h454, hlam, p487_0]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h452, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p487_1, u3ehi2]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [h364, h452, h455, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p487_1, u3ehi3]
                · have p487_0 := h487c.1
                  have p487_1 := h487c.2.1
                  have p487_2 := h487c.2.2.1
                  have p487_3 := h487c.2.2.2
                  linarith only [hlam, p487_0]
          · linarith only [h364, h452, h455, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
        · linarith only [h364, h452, h454, hc12, hc23, hlam, hphi]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h515 | h515
        · rcases m.htr 2 3 4 (by decide) (by decide) with h516 | h516
          · rcases m.htr 2 4 5 (by decide) (by decide) with h517 | h517
            · rcases m.htr 3 4 5 (by decide) (by decide) with h518 | h518
              · rcases h2bigk with h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c
                · have p519_0 := h519c.1
                  have p519_1 := h519c.2.1
                  have p519_2 := h519c.2.2.1
                  have p519_3 := h519c.2.2.2
                  linarith only [hlam, p519_0]
                · have p519_0 := h519c.1
                  have p519_1 := h519c.2.1
                  have p519_2 := h519c.2.2.1
                  have p519_3 := h519c.2.2.2
                  linarith only [h0, hlam, p519_0]
                · have p519_0 := h519c.1
                  have p519_1 := h519c.2.1
                  have p519_2 := h519c.2.2.1
                  have p519_3 := h519c.2.2.2
                  linarith only [h364, hlam, p519_0]
                · have p519_0 := h519c.1
                  have p519_1 := h519c.2.1
                  have p519_2 := h519c.2.2.1
                  have p519_3 := h519c.2.2.2
                  linarith only [h0, h453, hlam, p519_1]
                · have p519_0 := h519c.1
                  have p519_1 := h519c.2.1
                  have p519_2 := h519c.2.2.1
                  have p519_3 := h519c.2.2.2
                  linarith only [h0, h453, h516, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p519_1, u5ehi2]
                · have p519_0 := h519c.1
                  have p519_1 := h519c.2.1
                  have p519_2 := h519c.2.2.1
                  have p519_3 := h519c.2.2.2
                  linarith only [h453, h516, hc02, hc23, hlam, hphi, p519_1]
                · have p519_0 := h519c.1
                  have p519_1 := h519c.2.1
                  have p519_2 := h519c.2.2.1
                  have p519_3 := h519c.2.2.2
                  linarith only [hlam, p519_0]
                · have p519_0 := h519c.1
                  have p519_1 := h519c.2.1
                  have p519_2 := h519c.2.2.1
                  have p519_3 := h519c.2.2.2
                  linarith only [h453, h516, hlam, p519_1]
                · have p519_0 := h519c.1
                  have p519_1 := h519c.2.1
                  have p519_2 := h519c.2.2.1
                  have p519_3 := h519c.2.2.2
                  linarith only [h453, hlam, p519_0]
                · have p519_0 := h519c.1
                  have p519_1 := h519c.2.1
                  have p519_2 := h519c.2.2.1
                  have p519_3 := h519c.2.2.2
                  linarith only [h453, h516, h517, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p519_1, u5ehi4]
                · have p519_0 := h519c.1
                  have p519_1 := h519c.2.1
                  have p519_2 := h519c.2.2.1
                  have p519_3 := h519c.2.2.2
                  linarith only [h452, h517, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p519_1, u5ehi4]
                · have p519_0 := h519c.1
                  have p519_1 := h519c.2.1
                  have p519_2 := h519c.2.2.1
                  have p519_3 := h519c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p519_1]
                · have p519_0 := h519c.1
                  have p519_1 := h519c.2.1
                  have p519_2 := h519c.2.2.1
                  have p519_3 := h519c.2.2.2
                  linarith only [hlam, p519_0]
                · have p519_0 := h519c.1
                  have p519_1 := h519c.2.1
                  have p519_2 := h519c.2.2.1
                  have p519_3 := h519c.2.2.2
                  linarith only [h0, h452, h453, h517, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p519_1, u5ehi4]
                · have p519_0 := h519c.1
                  have p519_1 := h519c.2.1
                  have p519_2 := h519c.2.2.1
                  have p519_3 := h519c.2.2.2
                  linarith only [h517, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p519_1, u5ehi4]
                · have p519_0 := h519c.1
                  have p519_1 := h519c.2.1
                  have p519_2 := h519c.2.2.1
                  have p519_3 := h519c.2.2.2
                  linarith only [h452, h517, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p519_1, u5ehi4]
                · have p519_0 := h519c.1
                  have p519_1 := h519c.2.1
                  have p519_2 := h519c.2.2.1
                  have p519_3 := h519c.2.2.2
                  linarith only [h0, h452, h517, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p519_1, u5ehi4]
                · have p519_0 := h519c.1
                  have p519_1 := h519c.2.1
                  have p519_2 := h519c.2.2.1
                  have p519_3 := h519c.2.2.2
                  linarith only [h516, hlam, p519_0]
                · have p519_0 := h519c.1
                  have p519_1 := h519c.2.1
                  have p519_2 := h519c.2.2.1
                  have p519_3 := h519c.2.2.2
                  linarith only [hlam, p519_0]
                · have p519_0 := h519c.1
                  have p519_1 := h519c.2.1
                  have p519_2 := h519c.2.2.1
                  have p519_3 := h519c.2.2.2
                  linarith only [h516, h517, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p519_1, u5ehi4]
                · have p519_0 := h519c.1
                  have p519_1 := h519c.2.1
                  have p519_2 := h519c.2.2.1
                  have p519_3 := h519c.2.2.2
                  linarith only [h452, hlam, p519_0]
                · have p519_0 := h519c.1
                  have p519_1 := h519c.2.1
                  have p519_2 := h519c.2.2.1
                  have p519_3 := h519c.2.2.2
                  linarith only [h515, hlam, p519_0]
                · have p519_0 := h519c.1
                  have p519_1 := h519c.2.1
                  have p519_2 := h519c.2.2.1
                  have p519_3 := h519c.2.2.2
                  linarith only [h364, h452, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p519_1, u3ehi0]
                · have p519_0 := h519c.1
                  have p519_1 := h519c.2.1
                  have p519_2 := h519c.2.2.1
                  have p519_3 := h519c.2.2.2
                  linarith only [h517, hlam, p519_1]
                · have p519_0 := h519c.1
                  have p519_1 := h519c.2.1
                  have p519_2 := h519c.2.2.1
                  have p519_3 := h519c.2.2.2
                  linarith only [hlam, p519_0]
              · linarith only [h0, h452, h453, h516, h517, h518, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
            · linarith only [h0, h452, h453, h517, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
          · linarith only [h364, h452, h516, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
        · linarith only [h0, h452, h515, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h549 | h549
      · rcases m.htr 1 2 5 (by decide) (by decide) with h550 | h550
        · rcases m.htr 2 3 4 (by decide) (by decide) with h551 | h551
          · rcases m.htr 2 4 5 (by decide) (by decide) with h552 | h552
            · rcases m.htr 3 4 5 (by decide) (by decide) with h553 | h553
              · rcases h2bigk with h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c | h554c
                · have p554_0 := h554c.1
                  have p554_1 := h554c.2.1
                  have p554_2 := h554c.2.2.1
                  have p554_3 := h554c.2.2.2
                  linarith only [hlam, p554_0]
                · have p554_0 := h554c.1
                  have p554_1 := h554c.2.1
                  have p554_2 := h554c.2.2.1
                  have p554_3 := h554c.2.2.2
                  linarith only [h0, hlam, p554_0]
                · have p554_0 := h554c.1
                  have p554_1 := h554c.2.1
                  have p554_2 := h554c.2.2.1
                  have p554_3 := h554c.2.2.2
                  linarith only [h364, hlam, p554_0]
                · have p554_0 := h554c.1
                  have p554_1 := h554c.2.1
                  have p554_2 := h554c.2.2.1
                  have p554_3 := h554c.2.2.2
                  linarith only [h551, h553, hc02, hlam, hphi, ht0b, ht5b, p554_1, u5ehi4]
                · have p554_0 := h554c.1
                  have p554_1 := h554c.2.1
                  have p554_2 := h554c.2.2.1
                  have p554_3 := h554c.2.2.2
                  linarith only [h452, hlam, p554_0]
                · have p554_0 := h554c.1
                  have p554_1 := h554c.2.1
                  have p554_2 := h554c.2.2.1
                  have p554_3 := h554c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p554_1]
                · have p554_0 := h554c.1
                  have p554_1 := h554c.2.1
                  have p554_2 := h554c.2.2.1
                  have p554_3 := h554c.2.2.2
                  linarith only [hlam, p554_0]
                · have p554_0 := h554c.1
                  have p554_1 := h554c.2.1
                  have p554_2 := h554c.2.2.1
                  have p554_3 := h554c.2.2.2
                  linarith only [h551, h553, hc12, hlam, hphi, ht01, ht0b, ht5b, p554_1, u5ehi4]
                · have p554_0 := h554c.1
                  have p554_1 := h554c.2.1
                  have p554_2 := h554c.2.2.1
                  have p554_3 := h554c.2.2.2
                  linarith only [h552, hc12, hlam, hphi, ht01, ht0b, ht5b, p554_1, u5ehi2]
                · have p554_0 := h554c.1
                  have p554_1 := h554c.2.1
                  have p554_2 := h554c.2.2.1
                  have p554_3 := h554c.2.2.2
                  linarith only [h0, h452, hc01, hc12, hlam, hphi, p554_1]
                · have p554_0 := h554c.1
                  have p554_1 := h554c.2.1
                  have p554_2 := h554c.2.2.1
                  have p554_3 := h554c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p554_1]
                · have p554_0 := h554c.1
                  have p554_1 := h554c.2.1
                  have p554_2 := h554c.2.2.1
                  have p554_3 := h554c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p554_1]
                · have p554_0 := h554c.1
                  have p554_1 := h554c.2.1
                  have p554_2 := h554c.2.2.1
                  have p554_3 := h554c.2.2.2
                  linarith only [hlam, p554_0]
                · have p554_0 := h554c.1
                  have p554_1 := h554c.2.1
                  have p554_2 := h554c.2.2.1
                  have p554_3 := h554c.2.2.2
                  linarith only [h551, h553, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p554_1, u5ehi4]
                · have p554_0 := h554c.1
                  have p554_1 := h554c.2.1
                  have p554_2 := h554c.2.2.1
                  have p554_3 := h554c.2.2.2
                  linarith only [h0, h452, hc01, hc23, hlam, hphi, ht12, p554_1]
                · have p554_0 := h554c.1
                  have p554_1 := h554c.2.1
                  have p554_2 := h554c.2.2.1
                  have p554_3 := h554c.2.2.2
                  linarith only [h0, h549, hc01, hc12, hlam, hphi, p554_1]
                · have p554_0 := h554c.1
                  have p554_1 := h554c.2.1
                  have p554_2 := h554c.2.2.1
                  have p554_3 := h554c.2.2.2
                  linarith only [h549, hlam, p554_0]
                · have p554_0 := h554c.1
                  have p554_1 := h554c.2.1
                  have p554_2 := h554c.2.2.1
                  have p554_3 := h554c.2.2.2
                  linarith only [h551, hlam, p554_0]
                · have p554_0 := h554c.1
                  have p554_1 := h554c.2.1
                  have p554_2 := h554c.2.2.1
                  have p554_3 := h554c.2.2.2
                  linarith only [hlam, p554_0]
                · have p554_0 := h554c.1
                  have p554_1 := h554c.2.1
                  have p554_2 := h554c.2.2.1
                  have p554_3 := h554c.2.2.2
                  linarith only [h0, h452, h549, hc01, hc12, hlam, hphi, p554_1]
                · have p554_0 := h554c.1
                  have p554_1 := h554c.2.1
                  have p554_2 := h554c.2.2.1
                  have p554_3 := h554c.2.2.2
                  linarith only [h0, h550, hc01, hc15, hlam, hphi, p554_1]
                · have p554_0 := h554c.1
                  have p554_1 := h554c.2.1
                  have p554_2 := h554c.2.2.1
                  have p554_3 := h554c.2.2.2
                  linarith only [h550, hlam, p554_0]
                · have p554_0 := h554c.1
                  have p554_1 := h554c.2.1
                  have p554_2 := h554c.2.2.1
                  have p554_3 := h554c.2.2.2
                  linarith only [h549, h552, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p554_1, u3ehi2]
                · have p554_0 := h554c.1
                  have p554_1 := h554c.2.1
                  have p554_2 := h554c.2.2.1
                  have p554_3 := h554c.2.2.2
                  linarith only [h552, hlam, p554_1]
                · have p554_0 := h554c.1
                  have p554_1 := h554c.2.1
                  have p554_2 := h554c.2.2.1
                  have p554_3 := h554c.2.2.2
                  linarith only [hlam, p554_0]
              · linarith only [h549, h552, h553, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h581 | h581
              · linarith only [h551, h552, h581, hlam]
              · rcases h2bigk with h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c
                · have p583_0 := h583c.1
                  have p583_1 := h583c.2.1
                  have p583_2 := h583c.2.2.1
                  have p583_3 := h583c.2.2.2
                  linarith only [hlam, p583_0]
                · have p583_0 := h583c.1
                  have p583_1 := h583c.2.1
                  have p583_2 := h583c.2.2.1
                  have p583_3 := h583c.2.2.2
                  linarith only [h0, hlam, p583_0]
                · have p583_0 := h583c.1
                  have p583_1 := h583c.2.1
                  have p583_2 := h583c.2.2.1
                  have p583_3 := h583c.2.2.2
                  linarith only [h364, hlam, p583_0]
                · have p583_0 := h583c.1
                  have p583_1 := h583c.2.1
                  have p583_2 := h583c.2.2.1
                  have p583_3 := h583c.2.2.2
                  linarith only [h551, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p583_1, u3ehi3]
                · have p583_0 := h583c.1
                  have p583_1 := h583c.2.1
                  have p583_2 := h583c.2.2.1
                  have p583_3 := h583c.2.2.2
                  linarith only [h452, hlam, p583_0]
                · have p583_0 := h583c.1
                  have p583_1 := h583c.2.1
                  have p583_2 := h583c.2.2.1
                  have p583_3 := h583c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p583_1]
                · have p583_0 := h583c.1
                  have p583_1 := h583c.2.1
                  have p583_2 := h583c.2.2.1
                  have p583_3 := h583c.2.2.2
                  linarith only [hlam, p583_0]
                · have p583_0 := h583c.1
                  have p583_1 := h583c.2.1
                  have p583_2 := h583c.2.2.1
                  have p583_3 := h583c.2.2.2
                  linarith only [hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p583_1, u3ehi2]
                · have p583_0 := h583c.1
                  have p583_1 := h583c.2.1
                  have p583_2 := h583c.2.2.1
                  have p583_3 := h583c.2.2.2
                  linarith only [h551, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p583_1, u3ehi3]
                · have p583_0 := h583c.1
                  have p583_1 := h583c.2.1
                  have p583_2 := h583c.2.2.1
                  have p583_3 := h583c.2.2.2
                  linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p583_1, u5ehi2]
                · have p583_0 := h583c.1
                  have p583_1 := h583c.2.1
                  have p583_2 := h583c.2.2.1
                  have p583_3 := h583c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p583_1]
                · have p583_0 := h583c.1
                  have p583_1 := h583c.2.1
                  have p583_2 := h583c.2.2.1
                  have p583_3 := h583c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p583_1]
                · have p583_0 := h583c.1
                  have p583_1 := h583c.2.1
                  have p583_2 := h583c.2.2.1
                  have p583_3 := h583c.2.2.2
                  linarith only [hlam, p583_0]
                · have p583_0 := h583c.1
                  have p583_1 := h583c.2.1
                  have p583_2 := h583c.2.2.1
                  have p583_3 := h583c.2.2.2
                  linarith only [h551, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p583_1, u3ehi3]
                · have p583_0 := h583c.1
                  have p583_1 := h583c.2.1
                  have p583_2 := h583c.2.2.1
                  have p583_3 := h583c.2.2.2
                  linarith only [h0, h452, hc01, hc23, hlam, hphi, ht12, p583_1]
                · have p583_0 := h583c.1
                  have p583_1 := h583c.2.1
                  have p583_2 := h583c.2.2.1
                  have p583_3 := h583c.2.2.2
                  linarith only [h0, hc01, hc24, hlam, hphi, ht12, p583_1]
                · have p583_0 := h583c.1
                  have p583_1 := h583c.2.1
                  have p583_2 := h583c.2.2.1
                  have p583_3 := h583c.2.2.2
                  linarith only [h549, hlam, p583_0]
                · have p583_0 := h583c.1
                  have p583_1 := h583c.2.1
                  have p583_2 := h583c.2.2.1
                  have p583_3 := h583c.2.2.2
                  linarith only [h551, hlam, p583_0]
                · have p583_0 := h583c.1
                  have p583_1 := h583c.2.1
                  have p583_2 := h583c.2.2.1
                  have p583_3 := h583c.2.2.2
                  linarith only [hlam, p583_0]
                · have p583_0 := h583c.1
                  have p583_1 := h583c.2.1
                  have p583_2 := h583c.2.2.1
                  have p583_3 := h583c.2.2.2
                  linarith only [h552, hlam, p583_0]
                · have p583_0 := h583c.1
                  have p583_1 := h583c.2.1
                  have p583_2 := h583c.2.2.1
                  have p583_3 := h583c.2.2.2
                  linarith only [h0, h550, hc01, hc12, hlam, hphi, p583_1]
                · have p583_0 := h583c.1
                  have p583_1 := h583c.2.1
                  have p583_2 := h583c.2.2.1
                  have p583_3 := h583c.2.2.2
                  linarith only [h550, hlam, p583_0]
                · have p583_0 := h583c.1
                  have p583_1 := h583c.2.1
                  have p583_2 := h583c.2.2.1
                  have p583_3 := h583c.2.2.2
                  linarith only [h550, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p583_1, u3ehi2]
                · have p583_0 := h583c.1
                  have p583_1 := h583c.2.1
                  have p583_2 := h583c.2.2.1
                  have p583_3 := h583c.2.2.2
                  linarith only [h550, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p583_1]
                · have p583_0 := h583c.1
                  have p583_1 := h583c.2.1
                  have p583_2 := h583c.2.2.1
                  have p583_3 := h583c.2.2.2
                  linarith only [hlam, p583_0]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h609 | h609
            · rcases m.htr 3 4 5 (by decide) (by decide) with h610 | h610
              · rcases h2bigk with h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c | h611c
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [hlam, p611_0]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h0, hlam, p611_0]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h364, hlam, p611_0]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h551, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p611_1, u3ehi2]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h452, hlam, p611_0]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p611_1]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [hlam, p611_0]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h0, h364, hc01, hc12, hlam, hphi, p611_1]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h609, hc12, hlam, hphi, ht01, ht0b, ht5b, p611_1, u5ehi4]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h0, h452, hc01, hc12, hlam, hphi, p611_1]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p611_1]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p611_1]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [hlam, p611_0]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h551, hlam, p611_1]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h0, h452, h551, hc01, hc34, hlam, hphi, ht12, ht23, p611_1]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h0, h549, hc01, hc12, hlam, hphi, p611_1]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h549, hlam, p611_0]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h549, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p611_1, u3ehi2]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [hlam, p611_0]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h0, h452, h549, hc01, hc12, hlam, hphi, p611_1]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h0, h550, hc01, hc15, hlam, hphi, p611_1]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h550, hlam, p611_0]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h0, h364, h549, h609, hc01, hc12, hlam, hphi, p611_1]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [h609, hlam, p611_1]
                · have p611_0 := h611c.1
                  have p611_1 := h611c.2.1
                  have p611_2 := h611c.2.2.1
                  have p611_3 := h611c.2.2.2
                  linarith only [hlam, p611_0]
              · linarith only [h0, h364, h551, h610, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h638 | h638
              · linarith only [h0, h364, h551, h609, h638, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h0, h364, h551, h638, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h641 | h641
          · rcases m.htr 2 4 5 (by decide) (by decide) with h642 | h642
            · linarith only [h549, h550, h642, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
            · linarith only [h549, h550, h641, h642, hc45, hlam, hphi, ht34, u3ehi3]
          · linarith only [h0, h364, h549, h550, h641, hc01, hc25, hlam, hphi, ht12]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h646 | h646
        · linarith only [h0, h452, h549, h646, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h648 | h648
          · rcases m.htr 2 4 5 (by decide) (by decide) with h649 | h649
            · rcases m.htr 3 4 5 (by decide) (by decide) with h650 | h650
              · rcases h2bigk with h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c | h651c
                · have p651_0 := h651c.1
                  have p651_1 := h651c.2.1
                  have p651_2 := h651c.2.2.1
                  have p651_3 := h651c.2.2.2
                  linarith only [hlam, p651_0]
                · have p651_0 := h651c.1
                  have p651_1 := h651c.2.1
                  have p651_2 := h651c.2.2.1
                  have p651_3 := h651c.2.2.2
                  linarith only [h0, hlam, p651_0]
                · have p651_0 := h651c.1
                  have p651_1 := h651c.2.1
                  have p651_2 := h651c.2.2.1
                  have p651_3 := h651c.2.2.2
                  linarith only [h364, hlam, p651_0]
                · have p651_0 := h651c.1
                  have p651_1 := h651c.2.1
                  have p651_2 := h651c.2.2.1
                  have p651_3 := h651c.2.2.2
                  linarith only [h646, h649, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p651_1]
                · have p651_0 := h651c.1
                  have p651_1 := h651c.2.1
                  have p651_2 := h651c.2.2.1
                  have p651_3 := h651c.2.2.2
                  linarith only [h452, hlam, p651_0]
                · have p651_0 := h651c.1
                  have p651_1 := h651c.2.1
                  have p651_2 := h651c.2.2.1
                  have p651_3 := h651c.2.2.2
                  linarith only [h646, h648, h649, hc02, hc23, hlam, hphi, p651_1]
                · have p651_0 := h651c.1
                  have p651_1 := h651c.2.1
                  have p651_2 := h651c.2.2.1
                  have p651_3 := h651c.2.2.2
                  linarith only [hlam, p651_0]
                · have p651_0 := h651c.1
                  have p651_1 := h651c.2.1
                  have p651_2 := h651c.2.2.1
                  have p651_3 := h651c.2.2.2
                  linarith only [h646, h648, h649, hlam, p651_1]
                · have p651_0 := h651c.1
                  have p651_1 := h651c.2.1
                  have p651_2 := h651c.2.2.1
                  have p651_3 := h651c.2.2.2
                  linarith only [h549, hlam, p651_0]
                · have p651_0 := h651c.1
                  have p651_1 := h651c.2.1
                  have p651_2 := h651c.2.2.1
                  have p651_3 := h651c.2.2.2
                  linarith only [h646, hlam, p651_0]
                · have p651_0 := h651c.1
                  have p651_1 := h651c.2.1
                  have p651_2 := h651c.2.2.1
                  have p651_3 := h651c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p651_1]
                · have p651_0 := h651c.1
                  have p651_1 := h651c.2.1
                  have p651_2 := h651c.2.2.1
                  have p651_3 := h651c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p651_1]
                · have p651_0 := h651c.1
                  have p651_1 := h651c.2.1
                  have p651_2 := h651c.2.2.1
                  have p651_3 := h651c.2.2.2
                  linarith only [hlam, p651_0]
                · have p651_0 := h651c.1
                  have p651_1 := h651c.2.1
                  have p651_2 := h651c.2.2.1
                  have p651_3 := h651c.2.2.2
                  linarith only [h646, h649, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p651_1, u5ehi1]
                · have p651_0 := h651c.1
                  have p651_1 := h651c.2.1
                  have p651_2 := h651c.2.2.1
                  have p651_3 := h651c.2.2.2
                  linarith only [h0, h646, hc01, hc23, hlam, hphi, ht12, p651_1]
                · have p651_0 := h651c.1
                  have p651_1 := h651c.2.1
                  have p651_2 := h651c.2.2.1
                  have p651_3 := h651c.2.2.2
                  linarith only [h0, hc01, hc24, hlam, hphi, ht12, p651_1]
                · have p651_0 := h651c.1
                  have p651_1 := h651c.2.1
                  have p651_2 := h651c.2.2.1
                  have p651_3 := h651c.2.2.2
                  linarith only [h0, hc01, hc24, hlam, hphi, ht12, p651_1]
                · have p651_0 := h651c.1
                  have p651_1 := h651c.2.1
                  have p651_2 := h651c.2.2.1
                  have p651_3 := h651c.2.2.2
                  linarith only [h648, hlam, p651_0]
                · have p651_0 := h651c.1
                  have p651_1 := h651c.2.1
                  have p651_2 := h651c.2.2.1
                  have p651_3 := h651c.2.2.2
                  linarith only [hlam, p651_0]
                · have p651_0 := h651c.1
                  have p651_1 := h651c.2.1
                  have p651_2 := h651c.2.2.1
                  have p651_3 := h651c.2.2.2
                  linarith only [h0, h646, h648, hc01, hc23, hlam, hphi, ht12, p651_1]
                · have p651_0 := h651c.1
                  have p651_1 := h651c.2.1
                  have p651_2 := h651c.2.2.1
                  have p651_3 := h651c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p651_1]
                · have p651_0 := h651c.1
                  have p651_1 := h651c.2.1
                  have p651_2 := h651c.2.2.1
                  have p651_3 := h651c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p651_1]
                · have p651_0 := h651c.1
                  have p651_1 := h651c.2.1
                  have p651_2 := h651c.2.2.1
                  have p651_3 := h651c.2.2.2
                  linarith only [h648, h649, hlam, p651_1]
                · have p651_0 := h651c.1
                  have p651_1 := h651c.2.1
                  have p651_2 := h651c.2.2.1
                  have p651_3 := h651c.2.2.2
                  linarith only [h649, hlam, p651_1]
                · have p651_0 := h651c.1
                  have p651_1 := h651c.2.1
                  have p651_2 := h651c.2.2.1
                  have p651_3 := h651c.2.2.2
                  linarith only [hlam, p651_0]
              · rcases h2bigk with h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c
                · have p677_0 := h677c.1
                  have p677_1 := h677c.2.1
                  have p677_2 := h677c.2.2.1
                  have p677_3 := h677c.2.2.2
                  linarith only [hlam, p677_0]
                · have p677_0 := h677c.1
                  have p677_1 := h677c.2.1
                  have p677_2 := h677c.2.2.1
                  have p677_3 := h677c.2.2.2
                  linarith only [h0, hlam, p677_0]
                · have p677_0 := h677c.1
                  have p677_1 := h677c.2.1
                  have p677_2 := h677c.2.2.1
                  have p677_3 := h677c.2.2.2
                  linarith only [h364, hlam, p677_0]
                · have p677_0 := h677c.1
                  have p677_1 := h677c.2.1
                  have p677_2 := h677c.2.2.1
                  have p677_3 := h677c.2.2.2
                  linarith only [h649, hc02, hlam, hphi, ht0b, ht5b, p677_1, u5ehi2]
                · have p677_0 := h677c.1
                  have p677_1 := h677c.2.1
                  have p677_2 := h677c.2.2.1
                  have p677_3 := h677c.2.2.2
                  linarith only [h452, hlam, p677_0]
                · have p677_0 := h677c.1
                  have p677_1 := h677c.2.1
                  have p677_2 := h677c.2.2.1
                  have p677_3 := h677c.2.2.2
                  linarith only [h0, hc01, hc12, hlam, hphi, p677_1]
                · have p677_0 := h677c.1
                  have p677_1 := h677c.2.1
                  have p677_2 := h677c.2.2.1
                  have p677_3 := h677c.2.2.2
                  linarith only [hlam, p677_0]
                · have p677_0 := h677c.1
                  have p677_1 := h677c.2.1
                  have p677_2 := h677c.2.2.1
                  have p677_3 := h677c.2.2.2
                  linarith only [h646, h648, h649, hlam, p677_1]
                · have p677_0 := h677c.1
                  have p677_1 := h677c.2.1
                  have p677_2 := h677c.2.2.1
                  have p677_3 := h677c.2.2.2
                  linarith only [h549, hlam, p677_0]
                · have p677_0 := h677c.1
                  have p677_1 := h677c.2.1
                  have p677_2 := h677c.2.2.1
                  have p677_3 := h677c.2.2.2
                  linarith only [h646, hlam, p677_0]
                · have p677_0 := h677c.1
                  have p677_1 := h677c.2.1
                  have p677_2 := h677c.2.2.1
                  have p677_3 := h677c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p677_1]
                · have p677_0 := h677c.1
                  have p677_1 := h677c.2.1
                  have p677_2 := h677c.2.2.1
                  have p677_3 := h677c.2.2.2
                  linarith only [hc12, hc23, hlam, hphi, p677_1]
                · have p677_0 := h677c.1
                  have p677_1 := h677c.2.1
                  have p677_2 := h677c.2.2.1
                  have p677_3 := h677c.2.2.2
                  linarith only [hlam, p677_0]
                · have p677_0 := h677c.1
                  have p677_1 := h677c.2.1
                  have p677_2 := h677c.2.2.1
                  have p677_3 := h677c.2.2.2
                  linarith only [h649, h650, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p677_1, u3ehi3]
                · have p677_0 := h677c.1
                  have p677_1 := h677c.2.1
                  have p677_2 := h677c.2.2.1
                  have p677_3 := h677c.2.2.2
                  linarith only [hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p677_1, u5ehi2]
                · have p677_0 := h677c.1
                  have p677_1 := h677c.2.1
                  have p677_2 := h677c.2.2.1
                  have p677_3 := h677c.2.2.2
                  linarith only [h0, hc01, hc24, hlam, hphi, ht12, p677_1]
                · have p677_0 := h677c.1
                  have p677_1 := h677c.2.1
                  have p677_2 := h677c.2.2.1
                  have p677_3 := h677c.2.2.2
                  linarith only [h0, hc01, hc24, hlam, hphi, ht12, p677_1]
                · have p677_0 := h677c.1
                  have p677_1 := h677c.2.1
                  have p677_2 := h677c.2.2.1
                  have p677_3 := h677c.2.2.2
                  linarith only [h648, hlam, p677_0]
                · have p677_0 := h677c.1
                  have p677_1 := h677c.2.1
                  have p677_2 := h677c.2.2.1
                  have p677_3 := h677c.2.2.2
                  linarith only [hlam, p677_0]
                · have p677_0 := h677c.1
                  have p677_1 := h677c.2.1
                  have p677_2 := h677c.2.2.1
                  have p677_3 := h677c.2.2.2
                  linarith only [h0, h646, h648, hc01, hc23, hlam, hphi, ht12, p677_1]
                · have p677_0 := h677c.1
                  have p677_1 := h677c.2.1
                  have p677_2 := h677c.2.2.1
                  have p677_3 := h677c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p677_1]
                · have p677_0 := h677c.1
                  have p677_1 := h677c.2.1
                  have p677_2 := h677c.2.2.1
                  have p677_3 := h677c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p677_1]
                · have p677_0 := h677c.1
                  have p677_1 := h677c.2.1
                  have p677_2 := h677c.2.2.1
                  have p677_3 := h677c.2.2.2
                  linarith only [h648, h649, hlam, p677_1]
                · have p677_0 := h677c.1
                  have p677_1 := h677c.2.1
                  have p677_2 := h677c.2.2.1
                  have p677_3 := h677c.2.2.2
                  linarith only [h649, hlam, p677_1]
                · have p677_0 := h677c.1
                  have p677_1 := h677c.2.1
                  have p677_2 := h677c.2.2.1
                  have p677_3 := h677c.2.2.2
                  linarith only [hlam, p677_0]
            · linarith only [h0, h549, h649, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h704 | h704
            · rcases m.htr 3 4 5 (by decide) (by decide) with h705 | h705
              · rcases h2bigk with h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c | h706c
                · have p706_0 := h706c.1
                  have p706_1 := h706c.2.1
                  have p706_2 := h706c.2.2.1
                  have p706_3 := h706c.2.2.2
                  linarith only [hlam, p706_0]
                · have p706_0 := h706c.1
                  have p706_1 := h706c.2.1
                  have p706_2 := h706c.2.2.1
                  have p706_3 := h706c.2.2.2
                  linarith only [h0, hlam, p706_0]
                · have p706_0 := h706c.1
                  have p706_1 := h706c.2.1
                  have p706_2 := h706c.2.2.1
                  have p706_3 := h706c.2.2.2
                  linarith only [h364, hlam, p706_0]
                · have p706_0 := h706c.1
                  have p706_1 := h706c.2.1
                  have p706_2 := h706c.2.2.1
                  have p706_3 := h706c.2.2.2
                  linarith only [h0, h646, h704, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p706_1]
                · have p706_0 := h706c.1
                  have p706_1 := h706c.2.1
                  have p706_2 := h706c.2.2.1
                  have p706_3 := h706c.2.2.2
                  linarith only [h452, hlam, p706_0]
                · have p706_0 := h706c.1
                  have p706_1 := h706c.2.1
                  have p706_2 := h706c.2.2.1
                  have p706_3 := h706c.2.2.2
                  linarith only [h646, h704, hc02, hc24, hlam, hphi, p706_1]
                · have p706_0 := h706c.1
                  have p706_1 := h706c.2.1
                  have p706_2 := h706c.2.2.1
                  have p706_3 := h706c.2.2.2
                  linarith only [hlam, p706_0]
                · have p706_0 := h706c.1
                  have p706_1 := h706c.2.1
                  have p706_2 := h706c.2.2.1
                  have p706_3 := h706c.2.2.2
                  linarith only [h646, h648, h704, hc34, hlam, hphi, p706_1, u3ehi2]
                · have p706_0 := h706c.1
                  have p706_1 := h706c.2.1
                  have p706_2 := h706c.2.2.1
                  have p706_3 := h706c.2.2.2
                  linarith only [h549, hlam, p706_0]
                · have p706_0 := h706c.1
                  have p706_1 := h706c.2.1
                  have p706_2 := h706c.2.2.1
                  have p706_3 := h706c.2.2.2
                  linarith only [h646, hlam, p706_0]
                · have p706_0 := h706c.1
                  have p706_1 := h706c.2.1
                  have p706_2 := h706c.2.2.1
                  have p706_3 := h706c.2.2.2
                  linarith only [h0, hc01, hc23, hlam, hphi, ht12, p706_1]
                · have p706_0 := h706c.1
                  have p706_1 := h706c.2.1
                  have p706_2 := h706c.2.2.1
                  have p706_3 := h706c.2.2.2
                  linarith only [h648, hc12, hc34, hlam, hphi, ht23, p706_1]
                · have p706_0 := h706c.1
                  have p706_1 := h706c.2.1
                  have p706_2 := h706c.2.2.1
                  have p706_3 := h706c.2.2.2
                  linarith only [hlam, p706_0]
                · have p706_0 := h706c.1
                  have p706_1 := h706c.2.1
                  have p706_2 := h706c.2.2.1
                  have p706_3 := h706c.2.2.2
                  linarith only [h648, hlam, p706_1]
                · have p706_0 := h706c.1
                  have p706_1 := h706c.2.1
                  have p706_2 := h706c.2.2.1
                  have p706_3 := h706c.2.2.2
                  linarith only [h648, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p706_1, u5ehi2]
                · have p706_0 := h706c.1
                  have p706_1 := h706c.2.1
                  have p706_2 := h706c.2.2.1
                  have p706_3 := h706c.2.2.2
                  linarith only [h0, h648, hc01, hc34, hlam, hphi, ht12, ht23, p706_1]
                · have p706_0 := h706c.1
                  have p706_1 := h706c.2.1
                  have p706_2 := h706c.2.2.1
                  have p706_3 := h706c.2.2.2
                  linarith only [h0, h648, hc01, hc34, hlam, hphi, ht12, ht23, p706_1]
                · have p706_0 := h706c.1
                  have p706_1 := h706c.2.1
                  have p706_2 := h706c.2.2.1
                  have p706_3 := h706c.2.2.2
                  linarith only [h648, hc34, hlam, hphi, p706_1, u3ehi2]
                · have p706_0 := h706c.1
                  have p706_1 := h706c.2.1
                  have p706_2 := h706c.2.2.1
                  have p706_3 := h706c.2.2.2
                  linarith only [hlam, p706_0]
                · have p706_0 := h706c.1
                  have p706_1 := h706c.2.1
                  have p706_2 := h706c.2.2.1
                  have p706_3 := h706c.2.2.2
                  linarith only [h0, h646, h648, hc01, hc34, hlam, hphi, ht12, ht23, p706_1]
                · have p706_0 := h706c.1
                  have p706_1 := h706c.2.1
                  have p706_2 := h706c.2.2.1
                  have p706_3 := h706c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p706_1]
                · have p706_0 := h706c.1
                  have p706_1 := h706c.2.1
                  have p706_2 := h706c.2.2.1
                  have p706_3 := h706c.2.2.2
                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p706_1]
                · have p706_0 := h706c.1
                  have p706_1 := h706c.2.1
                  have p706_2 := h706c.2.2.1
                  have p706_3 := h706c.2.2.2
                  linarith only [h0, h364, h648, h704, hc01, hc34, hlam, hphi, ht12, ht23, p706_1]
                · have p706_0 := h706c.1
                  have p706_1 := h706c.2.1
                  have p706_2 := h706c.2.2.1
                  have p706_3 := h706c.2.2.2
                  linarith only [h704, hlam, p706_1]
                · have p706_0 := h706c.1
                  have p706_1 := h706c.2.1
                  have p706_2 := h706c.2.2.1
                  have p706_3 := h706c.2.2.2
                  linarith only [hlam, p706_0]
              · linarith only [h648, h704, h705, hlam]
            · linarith only [h0, h549, h704, hc01, hc45, hlam, hphi, ht12, ht23, ht34]

theorem r1l7_22_13_15_H_I_L_R_L_R (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_22_13_15_H_I_L_R_L_R_x0 m hb2 hb3 hb5 h0
  · exact r1l7_22_13_15_H_I_L_R_L_R_x1 m hb2 hb3 hb5 h0

end R2N4
