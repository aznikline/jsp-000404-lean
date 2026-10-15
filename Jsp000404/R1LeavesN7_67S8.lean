import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_67S7

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_14_H_I_L_R_L_R_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h0bigk := hb0.1
  have h2ehi := hb2.1
  have h4ehi := hb4.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h386 | h386
  · rcases m.htr 0 1 4 (by decide) (by decide) with h387 | h387
    · rcases m.htr 0 1 5 (by decide) (by decide) with h388 | h388
      · rcases m.htr 0 2 3 (by decide) (by decide) with h389 | h389
        · rcases m.htr 0 2 4 (by decide) (by decide) with h390 | h390
          · rcases m.htr 0 2 5 (by decide) (by decide) with h391 | h391
            · rcases m.htr 0 3 4 (by decide) (by decide) with h392 | h392
              · rcases m.htr 0 3 5 (by decide) (by decide) with h393 | h393
                · rcases m.htr 0 4 5 (by decide) (by decide) with h394 | h394
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h395 | h395
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h396 | h396
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h397 | h397
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h398 | h398
                          · linarith only [h0, h386, h398, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h0, h386, h392, h395, h398, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h0, h387, h397, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                      · linarith only [h0, h387, h396, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                    · linarith only [h0, h386, h392, h394, h395, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h404 | h404
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h405 | h405
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h406 | h406
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h407 | h407
                          · linarith only [h0, h386, h407, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h0, h386, h392, h404, h407, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h0, h387, h406, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                      · linarith only [h0, h387, h405, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                    · linarith only [h0, h387, h404, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h413 | h413
                  · linarith only [h392, h393, h413, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h415 | h415
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h416 | h416
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h417 | h417
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h418 | h418
                          · linarith only [h0, h386, h418, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h392, h393, h418, hc13, hc35, hlam, hphi]
                        · linarith only [h0, h387, h416, h417, hc25, hlam, hphi, u2ehi3]
                      · linarith only [h0, h387, h416, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                    · linarith only [h0, h388, h392, h393, h415, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h424 | h424
                · rcases m.htr 0 4 5 (by decide) (by decide) with h425 | h425
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h426 | h426
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h427 | h427
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h428 | h428
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h429 | h429
                          · linarith only [h0, h386, h392, h429, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h431 | h431
                            · linarith only [h0, h387, h431, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h0, h387, h425, h427, h431, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                        · linarith only [h0, h386, h426, h428, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h0, h386, h426, h427, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h387, h426, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                  · linarith only [h392, h424, h425, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h438 | h438
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h439 | h439
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h440 | h440
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h441 | h441
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h442 | h442
                          · linarith only [h0, h386, h442, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h444 | h444
                            · linarith only [h0, h387, h444, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h0, h387, h438, h439, h442, h444, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h0, h387, h438, h441, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                      · linarith only [h0, h387, h440, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                    · linarith only [h0, h387, h438, h439, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h450 | h450
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h451 | h451
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h452 | h452
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h453 | h453
                          · linarith only [h0, h386, h453, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h455 | h455
                            · linarith only [h0, h387, h438, h455, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h457 | h457
                              · linarith only [h386, h392, h450, h457, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h459 | h459
                                · linarith only [h387, h438, h451, h459, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h461 | h461
                                  · linarith only [h387, h438, h450, h453, h461, hc34, hlam, hphi, ht23, u2ehi2]
                                  · linarith only [h386, h392, h450, h461, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h0, h386, h450, h452, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h0, h386, h450, h451, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h387, h389, h450, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
            · linarith only [h389, h391, hc25, hlam, hphi, u2ehi2]
          · linarith only [h389, h390, hc24, hlam, hphi, u2ehi2]
        · linarith only [h0, h386, h389, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h470 | h470
        · rcases m.htr 0 2 4 (by decide) (by decide) with h471 | h471
          · rcases m.htr 0 2 5 (by decide) (by decide) with h472 | h472
            · rcases m.htr 0 3 4 (by decide) (by decide) with h473 | h473
              · rcases m.htr 0 3 5 (by decide) (by decide) with h474 | h474
                · linarith only [h386, h388, h474, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h476 | h476
                  · linarith only [h386, h388, h473, h476, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h478 | h478
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h479 | h479
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h480 | h480
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h481 | h481
                          · linarith only [h386, h388, h481, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h473, h474, h481, hc13, hc35, hlam, hphi]
                        · linarith only [h0, h387, h472, h479, h480, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h0, h472, h479, hc24, hlam, hphi, u2ehi4]
                    · linarith only [h0, h471, h478, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h487 | h487
                · linarith only [h387, h388, h473, h487, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h489 | h489
                  · linarith only [h387, h388, h489, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h491 | h491
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h492 | h492
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h493 | h493
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h494 | h494
                          · linarith only [h386, h388, h473, h493, h494, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h496 | h496
                            · linarith only [h387, h388, h489, h493, h496, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                            · linarith only [h387, h388, h491, h494, h496, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h0, h387, h492, h493, hc25, hlam, hphi, u2ehi3]
                      · linarith only [h0, h386, h491, h492, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h471, h491, hc23, hlam, hphi, u2ehi3]
            · linarith only [h470, h472, hc25, hlam, hphi, u2ehi2]
          · linarith only [h470, h471, hc24, hlam, hphi, u2ehi2]
        · linarith only [h0, h386, h470, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h505 | h505
      · rcases m.htr 0 2 3 (by decide) (by decide) with h506 | h506
        · rcases m.htr 0 2 4 (by decide) (by decide) with h507 | h507
          · rcases m.htr 0 2 5 (by decide) (by decide) with h508 | h508
            · rcases m.htr 0 3 4 (by decide) (by decide) with h509 | h509
              · linarith only [h386, h387, h509, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h511 | h511
                · rcases m.htr 0 4 5 (by decide) (by decide) with h512 | h512
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h513 | h513
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h514 | h514
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h515 | h515
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h516 | h516
                          · linarith only [h386, h387, h509, h514, h516, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h386, h387, h513, h516, hc34, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h386, h387, h513, h514, h515, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h0, h386, h507, h513, h514, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h507, h513, hc23, hlam, hphi, u2ehi3]
                  · linarith only [h386, h387, h511, h512, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h523 | h523
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h524 | h524
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h525 | h525
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h526 | h526
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h527 | h527
                          · linarith only [h386, h387, h525, h527, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h386, h387, h524, h527, hc34, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h386, h387, h524, h525, h526, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h0, h386, h524, h525, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h507, h524, hc23, hlam, hphi, u2ehi3]
                  · linarith only [h387, h505, h523, hlam]
            · linarith only [h506, h508, hc25, hlam, hphi, u2ehi2]
          · linarith only [h506, h507, hc24, hlam, hphi, u2ehi2]
        · linarith only [h0, h386, h506, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h537 | h537
        · rcases m.htr 0 2 4 (by decide) (by decide) with h538 | h538
          · rcases m.htr 0 2 5 (by decide) (by decide) with h539 | h539
            · rcases m.htr 0 3 4 (by decide) (by decide) with h540 | h540
              · linarith only [h386, h387, h540, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h542 | h542
                · linarith only [h386, h505, h542, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h544 | h544
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h545 | h545
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h546 | h546
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h547 | h547
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h548 | h548
                          · linarith only [h386, h387, h540, h546, h548, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h386, h387, h545, h548, hc34, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h386, h387, h539, h545, h546, h547, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h538, h546, hlam]
                    · linarith only [h0, h538, h545, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h554 | h554
                    · linarith only [h386, h387, h544, h554, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h0, h537, h554, hlam]
            · linarith only [h538, h539, hc25, hlam, hphi, u2ehi3]
          · linarith only [h537, h538, hc24, hlam, hphi, u2ehi2]
        · linarith only [h0, h386, h537, hlam]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h560 | h560
    · rcases m.htr 0 1 5 (by decide) (by decide) with h561 | h561
      · rcases m.htr 0 2 3 (by decide) (by decide) with h562 | h562
        · rcases m.htr 0 2 4 (by decide) (by decide) with h563 | h563
          · rcases m.htr 0 2 5 (by decide) (by decide) with h564 | h564
            · rcases m.htr 0 3 4 (by decide) (by decide) with h565 | h565
              · rcases m.htr 0 3 5 (by decide) (by decide) with h566 | h566
                · rcases m.htr 0 4 5 (by decide) (by decide) with h567 | h567
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h568 | h568
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h569 | h569
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h570 | h570
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h571 | h571
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h572 | h572
                            · linarith only [h386, h560, h568, h572, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h386, h560, h567, h568, h572, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                          · linarith only [h386, h561, h570, h571, hc34, hlam, hphi, ht23, u2ehi4]
                        · linarith only [h386, h560, h568, h569, h570, hc25, hlam, hphi, u2ehi3]
                      · linarith only [h386, h560, h568, h569, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                    · linarith only [h0, h560, h568, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h579 | h579
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h580 | h580
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h581 | h581
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h582 | h582
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h583 | h583
                            · linarith only [h560, h567, h583, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h585 | h585
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h586 | h586
                                · linarith only [h560, h567, h580, h586, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h588 | h588
                                  · linarith only [h560, h567, h580, h585, h588, hlam]
                                  · rcases h0bigk with h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c | h590c
                                    · have p590_0 := h590c.1
                                      have p590_1 := h590c.2.1
                                      have p590_2 := h590c.2.2.1
                                      have p590_3 := h590c.2.2.2
                                      linarith only [hlam, p590_0]
                                    · have p590_0 := h590c.1
                                      have p590_1 := h590c.2.1
                                      have p590_2 := h590c.2.2.1
                                      have p590_3 := h590c.2.2.2
                                      linarith only [h0, hlam, p590_1]
                                    · have p590_0 := h590c.1
                                      have p590_1 := h590c.2.1
                                      have p590_2 := h590c.2.2.1
                                      have p590_3 := h590c.2.2.2
                                      linarith only [h386, hlam, p590_0]
                                    · have p590_0 := h590c.1
                                      have p590_1 := h590c.2.1
                                      have p590_2 := h590c.2.2.1
                                      have p590_3 := h590c.2.2.2
                                      linarith only [h386, h560, h579, h580, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p590_1, u2ehi3]
                                    · have p590_0 := h590c.1
                                      have p590_1 := h590c.2.1
                                      have p590_2 := h590c.2.2.1
                                      have p590_3 := h590c.2.2.2
                                      linarith only [h386, h579, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p590_1]
                                    · have p590_0 := h590c.1
                                      have p590_1 := h590c.2.1
                                      have p590_2 := h590c.2.2.1
                                      have p590_3 := h590c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p590_1]
                                    · have p590_0 := h590c.1
                                      have p590_1 := h590c.2.1
                                      have p590_2 := h590c.2.2.1
                                      have p590_3 := h590c.2.2.2
                                      linarith only [hlam, p590_0]
                                    · have p590_0 := h590c.1
                                      have p590_1 := h590c.2.1
                                      have p590_2 := h590c.2.2.1
                                      have p590_3 := h590c.2.2.2
                                      linarith only [h0, h386, h561, h581, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p590_1, u2ehi4]
                                    · have p590_0 := h590c.1
                                      have p590_1 := h590c.2.1
                                      have p590_2 := h590c.2.2.1
                                      have p590_3 := h590c.2.2.2
                                      linarith only [h0, h560, h580, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p590_1, u2ehi3]
                                    · have p590_0 := h590c.1
                                      have p590_1 := h590c.2.1
                                      have p590_2 := h590c.2.2.1
                                      have p590_3 := h590c.2.2.2
                                      linarith only [h0, h561, h581, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p590_1, u2ehi4]
                                    · have p590_0 := h590c.1
                                      have p590_1 := h590c.2.1
                                      have p590_2 := h590c.2.2.1
                                      have p590_3 := h590c.2.2.2
                                      linarith only [h561, h581, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p590_1, u2ehi4]
                                    · have p590_0 := h590c.1
                                      have p590_1 := h590c.2.1
                                      have p590_2 := h590c.2.2.1
                                      have p590_3 := h590c.2.2.2
                                      linarith only [h562, hlam, p590_1]
                                    · have p590_0 := h590c.1
                                      have p590_1 := h590c.2.1
                                      have p590_2 := h590c.2.2.1
                                      have p590_3 := h590c.2.2.2
                                      linarith only [hlam, p590_0]
                                    · have p590_0 := h590c.1
                                      have p590_1 := h590c.2.1
                                      have p590_2 := h590c.2.2.1
                                      have p590_3 := h590c.2.2.2
                                      linarith only [h386, h560, h579, h580, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p590_1, u2ehi3]
                                    · have p590_0 := h590c.1
                                      have p590_1 := h590c.2.1
                                      have p590_2 := h590c.2.2.1
                                      have p590_3 := h590c.2.2.2
                                      linarith only [h386, h561, h579, h581, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p590_1, u2ehi4]
                                    · have p590_0 := h590c.1
                                      have p590_1 := h590c.2.1
                                      have p590_2 := h590c.2.2.1
                                      have p590_3 := h590c.2.2.2
                                      linarith only [h560, hlam, p590_0]
                                    · have p590_0 := h590c.1
                                      have p590_1 := h590c.2.1
                                      have p590_2 := h590c.2.2.1
                                      have p590_3 := h590c.2.2.2
                                      linarith only [h563, hlam, p590_0]
                                    · have p590_0 := h590c.1
                                      have p590_1 := h590c.2.1
                                      have p590_2 := h590c.2.2.1
                                      have p590_3 := h590c.2.2.2
                                      linarith only [h565, hlam, p590_0]
                                    · have p590_0 := h590c.1
                                      have p590_1 := h590c.2.1
                                      have p590_2 := h590c.2.2.1
                                      have p590_3 := h590c.2.2.2
                                      linarith only [hlam, p590_0]
                                    · have p590_0 := h590c.1
                                      have p590_1 := h590c.2.1
                                      have p590_2 := h590c.2.2.1
                                      have p590_3 := h590c.2.2.2
                                      linarith only [h567, hlam, p590_0]
                                    · have p590_0 := h590c.1
                                      have p590_1 := h590c.2.1
                                      have p590_2 := h590c.2.2.1
                                      have p590_3 := h590c.2.2.2
                                      linarith only [h561, hlam, p590_0]
                                    · have p590_0 := h590c.1
                                      have p590_1 := h590c.2.1
                                      have p590_2 := h590c.2.2.1
                                      have p590_3 := h590c.2.2.2
                                      linarith only [h564, hlam, p590_1]
                                    · have p590_0 := h590c.1
                                      have p590_1 := h590c.2.1
                                      have p590_2 := h590c.2.2.1
                                      have p590_3 := h590c.2.2.2
                                      linarith only [h566, hlam, p590_0]
                                    · have p590_0 := h590c.1
                                      have p590_1 := h590c.2.1
                                      have p590_2 := h590c.2.2.1
                                      have p590_3 := h590c.2.2.2
                                      linarith only [h560, h580, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p590_1, u2ehi3]
                                    · have p590_0 := h590c.1
                                      have p590_1 := h590c.2.1
                                      have p590_2 := h590c.2.2.1
                                      have p590_3 := h590c.2.2.2
                                      linarith only [hlam, p590_0]
                              · linarith only [h565, h567, h585, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                          · linarith only [h386, h565, h567, h582, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h386, h560, h579, h580, h581, hc25, hlam, hphi, u2ehi3]
                      · linarith only [h386, h560, h579, h580, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                    · linarith only [h0, h560, h562, h579, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                · linarith only [h386, h561, h566, hlam]
              · linarith only [h386, h560, h565, hlam]
            · linarith only [h562, h564, hc25, hlam, hphi, u2ehi2]
          · linarith only [h562, h563, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h625 | h625
          · linarith only [h562, h625, hc23, hlam, hphi, u2ehi3]
          · linarith only [h0, h560, h625, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h628 | h628
        · rcases m.htr 0 2 4 (by decide) (by decide) with h629 | h629
          · rcases m.htr 0 2 5 (by decide) (by decide) with h630 | h630
            · rcases m.htr 0 3 4 (by decide) (by decide) with h631 | h631
              · rcases m.htr 0 3 5 (by decide) (by decide) with h632 | h632
                · rcases m.htr 0 4 5 (by decide) (by decide) with h633 | h633
                  · linarith only [h560, h561, h633, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h635 | h635
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h636 | h636
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h637 | h637
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h638 | h638
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h639 | h639
                            · linarith only [h560, h633, h639, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                            · linarith only [h560, h561, h636, h639, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                          · linarith only [h386, h560, h636, h638, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h0, h630, h637, hlam]
                      · linarith only [h386, h560, h635, h636, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                    · linarith only [h0, h560, h635, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h646 | h646
                  · linarith only [h386, h560, h632, h646, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h648 | h648
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h649 | h649
                      · linarith only [h386, h560, h632, h649, hc35, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h386, h560, h648, h649, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                    · linarith only [h0, h560, h628, h648, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
              · linarith only [h386, h560, h631, hlam]
            · linarith only [h628, h630, hc25, hlam, hphi, u2ehi2]
          · linarith only [h628, h629, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h656 | h656
          · linarith only [h628, h656, hc23, hlam, hphi, u2ehi3]
          · linarith only [h0, h560, h656, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h659 | h659
      · rcases m.htr 0 2 3 (by decide) (by decide) with h660 | h660
        · rcases m.htr 0 2 4 (by decide) (by decide) with h661 | h661
          · rcases m.htr 0 2 5 (by decide) (by decide) with h662 | h662
            · rcases m.htr 0 3 4 (by decide) (by decide) with h663 | h663
              · rcases m.htr 0 3 5 (by decide) (by decide) with h664 | h664
                · rcases m.htr 0 4 5 (by decide) (by decide) with h665 | h665
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h666 | h666
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h667 | h667
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h668 | h668
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h669 | h669
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h670 | h670
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h671 | h671
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h672 | h672
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h673 | h673
                                  · linarith only [h660, h671, h673, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                  · linarith only [h0, h661, h672, h673, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                                · linarith only [h560, h659, h669, h670, h672, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h677 | h677
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h678 | h678
                                  · rcases h0bigk with h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c | h679c
                                    · have p679_0 := h679c.1
                                      have p679_1 := h679c.2.1
                                      have p679_2 := h679c.2.2.1
                                      have p679_3 := h679c.2.2.2
                                      linarith only [hlam, p679_0]
                                    · have p679_0 := h679c.1
                                      have p679_1 := h679c.2.1
                                      have p679_2 := h679c.2.2.1
                                      have p679_3 := h679c.2.2.2
                                      linarith only [h0, hlam, p679_1]
                                    · have p679_0 := h679c.1
                                      have p679_1 := h679c.2.1
                                      have p679_2 := h679c.2.2.1
                                      have p679_3 := h679c.2.2.2
                                      linarith only [h386, hlam, p679_0]
                                    · have p679_0 := h679c.1
                                      have p679_1 := h679c.2.1
                                      have p679_2 := h679c.2.2.1
                                      have p679_3 := h679c.2.2.2
                                      linarith only [h560, hlam, p679_1]
                                    · have p679_0 := h679c.1
                                      have p679_1 := h679c.2.1
                                      have p679_2 := h679c.2.2.1
                                      have p679_3 := h679c.2.2.2
                                      linarith only [h560, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p679_1]
                                    · have p679_0 := h679c.1
                                      have p679_1 := h679c.2.1
                                      have p679_2 := h679c.2.2.1
                                      have p679_3 := h679c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p679_1]
                                    · have p679_0 := h679c.1
                                      have p679_1 := h679c.2.1
                                      have p679_2 := h679c.2.2.1
                                      have p679_3 := h679c.2.2.2
                                      linarith only [hlam, p679_0]
                                    · have p679_0 := h679c.1
                                      have p679_1 := h679c.2.1
                                      have p679_2 := h679c.2.2.1
                                      have p679_3 := h679c.2.2.2
                                      linarith only [h0, h663, h671, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p679_1]
                                    · have p679_0 := h679c.1
                                      have p679_1 := h679c.2.1
                                      have p679_2 := h679c.2.2.1
                                      have p679_3 := h679c.2.2.2
                                      linarith only [h0, h560, h659, h668, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p679_1, u2ehi4]
                                    · have p679_0 := h679c.1
                                      have p679_1 := h679c.2.1
                                      have p679_2 := h679c.2.2.1
                                      have p679_3 := h679c.2.2.2
                                      linarith only [h0, h659, h668, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p679_1, u2ehi4]
                                    · have p679_0 := h679c.1
                                      have p679_1 := h679c.2.1
                                      have p679_2 := h679c.2.2.1
                                      have p679_3 := h679c.2.2.2
                                      linarith only [h659, h668, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p679_1, u2ehi4]
                                    · have p679_0 := h679c.1
                                      have p679_1 := h679c.2.1
                                      have p679_2 := h679c.2.2.1
                                      have p679_3 := h679c.2.2.2
                                      linarith only [h660, hlam, p679_1]
                                    · have p679_0 := h679c.1
                                      have p679_1 := h679c.2.1
                                      have p679_2 := h679c.2.2.1
                                      have p679_3 := h679c.2.2.2
                                      linarith only [hlam, p679_0]
                                    · have p679_0 := h679c.1
                                      have p679_1 := h679c.2.1
                                      have p679_2 := h679c.2.2.1
                                      have p679_3 := h679c.2.2.2
                                      linarith only [h386, h560, h659, h666, h668, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p679_1, u2ehi4]
                                    · have p679_0 := h679c.1
                                      have p679_1 := h679c.2.1
                                      have p679_2 := h679c.2.2.1
                                      have p679_3 := h679c.2.2.2
                                      linarith only [h386, h659, h666, h668, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p679_1, u2ehi4]
                                    · have p679_0 := h679c.1
                                      have p679_1 := h679c.2.1
                                      have p679_2 := h679c.2.2.1
                                      have p679_3 := h679c.2.2.2
                                      linarith only [h659, h668, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p679_1, u2ehi4]
                                    · have p679_0 := h679c.1
                                      have p679_1 := h679c.2.1
                                      have p679_2 := h679c.2.2.1
                                      have p679_3 := h679c.2.2.2
                                      linarith only [h661, hlam, p679_0]
                                    · have p679_0 := h679c.1
                                      have p679_1 := h679c.2.1
                                      have p679_2 := h679c.2.2.1
                                      have p679_3 := h679c.2.2.2
                                      linarith only [h663, hlam, p679_0]
                                    · have p679_0 := h679c.1
                                      have p679_1 := h679c.2.1
                                      have p679_2 := h679c.2.2.1
                                      have p679_3 := h679c.2.2.2
                                      linarith only [hlam, p679_0]
                                    · have p679_0 := h679c.1
                                      have p679_1 := h679c.2.1
                                      have p679_2 := h679c.2.2.1
                                      have p679_3 := h679c.2.2.2
                                      linarith only [h386, h659, h663, h666, h668, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p679_1, u2ehi4]
                                    · have p679_0 := h679c.1
                                      have p679_1 := h679c.2.1
                                      have p679_2 := h679c.2.2.1
                                      have p679_3 := h679c.2.2.2
                                      linarith only [h659, hlam, p679_0]
                                    · have p679_0 := h679c.1
                                      have p679_1 := h679c.2.1
                                      have p679_2 := h679c.2.2.1
                                      have p679_3 := h679c.2.2.2
                                      linarith only [h662, hlam, p679_1]
                                    · have p679_0 := h679c.1
                                      have p679_1 := h679c.2.1
                                      have p679_2 := h679c.2.2.1
                                      have p679_3 := h679c.2.2.2
                                      linarith only [h664, hlam, p679_0]
                                    · have p679_0 := h679c.1
                                      have p679_1 := h679c.2.1
                                      have p679_2 := h679c.2.2.1
                                      have p679_3 := h679c.2.2.2
                                      linarith only [h665, hlam, p679_1]
                                    · have p679_0 := h679c.1
                                      have p679_1 := h679c.2.1
                                      have p679_2 := h679c.2.2.1
                                      have p679_3 := h679c.2.2.2
                                      linarith only [hlam, p679_0]
                                  · linarith only [h671, h677, h678, hc24, hlam, hphi, u2ehi2]
                                · linarith only [h0, h659, h670, h677, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · linarith only [h560, h659, h662, h670, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                          · linarith only [h386, h663, h669, hlam]
                        · linarith only [h0, h660, h668, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h0, h660, h667, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h660, h666, hlam]
                  · linarith only [h560, h659, h665, hlam]
                · linarith only [h386, h659, h664, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h714 | h714
                · rcases m.htr 0 4 5 (by decide) (by decide) with h715 | h715
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h716 | h716
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h717 | h717
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h718 | h718
                        · linarith only [h386, h659, h663, h718, hc34, hlam, hphi, ht23, u2ehi4]
                        · linarith only [h0, h661, h718, hc25, hlam, hphi, u2ehi3]
                      · linarith only [h0, h661, h717, hlam]
                    · linarith only [h0, h661, h716, hc23, hlam, hphi, u2ehi3]
                  · linarith only [h386, h659, h663, h715, hlam]
                · linarith only [h386, h659, h714, hlam]
            · linarith only [h661, h662, hc25, hlam, hphi, u2ehi3]
          · linarith only [h660, h661, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h727 | h727
          · linarith only [h660, h727, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h729 | h729
            · linarith only [h660, h729, hc23, hlam, hphi, u2ehi4]
            · linarith only [h0, h659, h729, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h732 | h732
        · rcases m.htr 0 2 4 (by decide) (by decide) with h733 | h733
          · rcases m.htr 0 2 5 (by decide) (by decide) with h734 | h734
            · rcases m.htr 0 3 4 (by decide) (by decide) with h735 | h735
              · rcases m.htr 0 3 5 (by decide) (by decide) with h736 | h736
                · rcases m.htr 0 4 5 (by decide) (by decide) with h737 | h737
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h738 | h738
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h739 | h739
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h740 | h740
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h741 | h741
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h742 | h742
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h743 | h743
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h744 | h744
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h745 | h745
                                  · linarith only [h732, h743, h745, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                  · linarith only [h0, h733, h744, h745, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h748 | h748
                                  · linarith only [h744, h748, hc34, hlam, hphi, ht23, u2ehi3]
                                  · rcases h0bigk with h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c | h750c
                                    · have p750_0 := h750c.1
                                      have p750_1 := h750c.2.1
                                      have p750_2 := h750c.2.2.1
                                      have p750_3 := h750c.2.2.2
                                      linarith only [hlam, p750_0]
                                    · have p750_0 := h750c.1
                                      have p750_1 := h750c.2.1
                                      have p750_2 := h750c.2.2.1
                                      have p750_3 := h750c.2.2.2
                                      linarith only [h0, hlam, p750_1]
                                    · have p750_0 := h750c.1
                                      have p750_1 := h750c.2.1
                                      have p750_2 := h750c.2.2.1
                                      have p750_3 := h750c.2.2.2
                                      linarith only [h386, hlam, p750_0]
                                    · have p750_0 := h750c.1
                                      have p750_1 := h750c.2.1
                                      have p750_2 := h750c.2.2.1
                                      have p750_3 := h750c.2.2.2
                                      linarith only [h560, hlam, p750_1]
                                    · have p750_0 := h750c.1
                                      have p750_1 := h750c.2.1
                                      have p750_2 := h750c.2.2.1
                                      have p750_3 := h750c.2.2.2
                                      linarith only [h659, hlam, p750_1]
                                    · have p750_0 := h750c.1
                                      have p750_1 := h750c.2.1
                                      have p750_2 := h750c.2.2.1
                                      have p750_3 := h750c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p750_1]
                                    · have p750_0 := h750c.1
                                      have p750_1 := h750c.2.1
                                      have p750_2 := h750c.2.2.1
                                      have p750_3 := h750c.2.2.2
                                      linarith only [hlam, p750_0]
                                    · have p750_0 := h750c.1
                                      have p750_1 := h750c.2.1
                                      have p750_2 := h750c.2.2.1
                                      have p750_3 := h750c.2.2.2
                                      linarith only [h0, h735, h737, h744, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p750_1, u2ehi3]
                                    · have p750_0 := h750c.1
                                      have p750_1 := h750c.2.1
                                      have p750_2 := h750c.2.2.1
                                      have p750_3 := h750c.2.2.2
                                      linarith only [h0, h737, h744, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p750_1, u2ehi3]
                                    · have p750_0 := h750c.1
                                      have p750_1 := h750c.2.1
                                      have p750_2 := h750c.2.2.1
                                      have p750_3 := h750c.2.2.2
                                      linarith only [h0, h659, hc01, hc12, hlam, hphi, p750_1]
                                    · have p750_0 := h750c.1
                                      have p750_1 := h750c.2.1
                                      have p750_2 := h750c.2.2.1
                                      have p750_3 := h750c.2.2.2
                                      linarith only [h386, h738, hc01, hc12, hlam, hphi, p750_1]
                                    · have p750_0 := h750c.1
                                      have p750_1 := h750c.2.1
                                      have p750_2 := h750c.2.2.1
                                      have p750_3 := h750c.2.2.2
                                      linarith only [h732, hlam, p750_1]
                                    · have p750_0 := h750c.1
                                      have p750_1 := h750c.2.1
                                      have p750_2 := h750c.2.2.1
                                      have p750_3 := h750c.2.2.2
                                      linarith only [hlam, p750_0]
                                    · have p750_0 := h750c.1
                                      have p750_1 := h750c.2.1
                                      have p750_2 := h750c.2.2.1
                                      have p750_3 := h750c.2.2.2
                                      linarith only [h386, h737, h738, h744, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p750_1, u2ehi3]
                                    · have p750_0 := h750c.1
                                      have p750_1 := h750c.2.1
                                      have p750_2 := h750c.2.2.1
                                      have p750_3 := h750c.2.2.2
                                      linarith only [h386, h734, h738, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p750_1, u2ehi4]
                                    · have p750_0 := h750c.1
                                      have p750_1 := h750c.2.1
                                      have p750_2 := h750c.2.2.1
                                      have p750_3 := h750c.2.2.2
                                      linarith only [h560, h738, h741, hc01, hc12, hlam, hphi, p750_1]
                                    · have p750_0 := h750c.1
                                      have p750_1 := h750c.2.1
                                      have p750_2 := h750c.2.2.1
                                      have p750_3 := h750c.2.2.2
                                      linarith only [h733, hlam, p750_0]
                                    · have p750_0 := h750c.1
                                      have p750_1 := h750c.2.1
                                      have p750_2 := h750c.2.2.1
                                      have p750_3 := h750c.2.2.2
                                      linarith only [h735, hlam, p750_0]
                                    · have p750_0 := h750c.1
                                      have p750_1 := h750c.2.1
                                      have p750_2 := h750c.2.2.1
                                      have p750_3 := h750c.2.2.2
                                      linarith only [hlam, p750_0]
                                    · have p750_0 := h750c.1
                                      have p750_1 := h750c.2.1
                                      have p750_2 := h750c.2.2.1
                                      have p750_3 := h750c.2.2.2
                                      linarith only [h560, h734, h738, h741, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p750_1, u2ehi4]
                                    · have p750_0 := h750c.1
                                      have p750_1 := h750c.2.1
                                      have p750_2 := h750c.2.2.1
                                      have p750_3 := h750c.2.2.2
                                      linarith only [h659, h738, h741, h742, hc01, hc12, hlam, hphi, p750_1]
                                    · have p750_0 := h750c.1
                                      have p750_1 := h750c.2.1
                                      have p750_2 := h750c.2.2.1
                                      have p750_3 := h750c.2.2.2
                                      linarith only [h734, hlam, p750_1]
                                    · have p750_0 := h750c.1
                                      have p750_1 := h750c.2.1
                                      have p750_2 := h750c.2.2.1
                                      have p750_3 := h750c.2.2.2
                                      linarith only [h736, hlam, p750_0]
                                    · have p750_0 := h750c.1
                                      have p750_1 := h750c.2.1
                                      have p750_2 := h750c.2.2.1
                                      have p750_3 := h750c.2.2.2
                                      linarith only [h737, hlam, p750_1]
                                    · have p750_0 := h750c.1
                                      have p750_1 := h750c.2.1
                                      have p750_2 := h750c.2.2.1
                                      have p750_3 := h750c.2.2.2
                                      linarith only [hlam, p750_0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h776 | h776
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h777 | h777
                                  · rcases h0bigk with h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c | h778c
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [hlam, p778_0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h0, hlam, p778_1]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h386, hlam, p778_0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h560, hlam, p778_1]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h659, hlam, p778_1]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p778_1]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [hlam, p778_0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h0, h735, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p778_1, u4ehi3]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p778_1, u4ehi0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h0, h659, hc01, hc12, hlam, hphi, p778_1]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h386, h738, hc01, hc12, hlam, hphi, p778_1]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h732, hlam, p778_1]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [hlam, p778_0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h386, h733, h738, h776, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p778_1, u4ehi4]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h386, h734, h738, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p778_1, u2ehi4]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h560, h738, h741, hc01, hc12, hlam, hphi, p778_1]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h733, hlam, p778_0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h735, hlam, p778_0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [hlam, p778_0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h560, h734, h738, h741, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p778_1, u2ehi4]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h659, h738, h741, h742, hc01, hc12, hlam, hphi, p778_1]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h734, hlam, p778_1]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h736, hlam, p778_0]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [h737, hlam, p778_1]
                                    · have p778_0 := h778c.1
                                      have p778_1 := h778c.2.1
                                      have p778_2 := h778c.2.2.1
                                      have p778_3 := h778c.2.2.2
                                      linarith only [hlam, p778_0]
                                  · linarith only [h743, h776, h777, hc24, hlam, hphi, u2ehi2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h805 | h805
                                  · linarith only [h386, h735, h738, h776, h805, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                                  · linarith only [h743, h805, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                            · linarith only [h560, h737, h742, hlam]
                          · linarith only [h386, h735, h741, hlam]
                        · linarith only [h0, h732, h740, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h0, h733, h739, hlam]
                    · linarith only [h0, h732, h738, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h813 | h813
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h814 | h814
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h815 | h815
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h816 | h816
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h817 | h817
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h818 | h818
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h819 | h819
                                · linarith only [h733, h737, h819, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h821 | h821
                                  · linarith only [h732, h733, h737, h818, h821, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                  · rcases h0bigk with h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c | h823c
                                    · have p823_0 := h823c.1
                                      have p823_1 := h823c.2.1
                                      have p823_2 := h823c.2.2.1
                                      have p823_3 := h823c.2.2.2
                                      linarith only [hlam, p823_0]
                                    · have p823_0 := h823c.1
                                      have p823_1 := h823c.2.1
                                      have p823_2 := h823c.2.2.1
                                      have p823_3 := h823c.2.2.2
                                      linarith only [h0, hlam, p823_1]
                                    · have p823_0 := h823c.1
                                      have p823_1 := h823c.2.1
                                      have p823_2 := h823c.2.2.1
                                      have p823_3 := h823c.2.2.2
                                      linarith only [h386, hlam, p823_0]
                                    · have p823_0 := h823c.1
                                      have p823_1 := h823c.2.1
                                      have p823_2 := h823c.2.2.1
                                      have p823_3 := h823c.2.2.2
                                      linarith only [h560, hlam, p823_1]
                                    · have p823_0 := h823c.1
                                      have p823_1 := h823c.2.1
                                      have p823_2 := h823c.2.2.1
                                      have p823_3 := h823c.2.2.2
                                      linarith only [h659, hlam, p823_1]
                                    · have p823_0 := h823c.1
                                      have p823_1 := h823c.2.1
                                      have p823_2 := h823c.2.2.1
                                      have p823_3 := h823c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p823_1]
                                    · have p823_0 := h823c.1
                                      have p823_1 := h823c.2.1
                                      have p823_2 := h823c.2.2.1
                                      have p823_3 := h823c.2.2.2
                                      linarith only [hlam, p823_0]
                                    · have p823_0 := h823c.1
                                      have p823_1 := h823c.2.1
                                      have p823_2 := h823c.2.2.1
                                      have p823_3 := h823c.2.2.2
                                      linarith only [h0, h732, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p823_1, u2ehi2]
                                    · have p823_0 := h823c.1
                                      have p823_1 := h823c.2.1
                                      have p823_2 := h823c.2.2.1
                                      have p823_3 := h823c.2.2.2
                                      linarith only [h0, h733, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p823_1, u2ehi3]
                                    · have p823_0 := h823c.1
                                      have p823_1 := h823c.2.1
                                      have p823_2 := h823c.2.2.1
                                      have p823_3 := h823c.2.2.2
                                      linarith only [h0, h734, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p823_1, u2ehi4]
                                    · have p823_0 := h823c.1
                                      have p823_1 := h823c.2.1
                                      have p823_2 := h823c.2.2.1
                                      have p823_3 := h823c.2.2.2
                                      linarith only [h386, hc01, hc13, hlam, hphi, p823_1]
                                    · have p823_0 := h823c.1
                                      have p823_1 := h823c.2.1
                                      have p823_2 := h823c.2.2.1
                                      have p823_3 := h823c.2.2.2
                                      linarith only [h732, hlam, p823_1]
                                    · have p823_0 := h823c.1
                                      have p823_1 := h823c.2.1
                                      have p823_2 := h823c.2.2.1
                                      have p823_3 := h823c.2.2.2
                                      linarith only [hlam, p823_0]
                                    · have p823_0 := h823c.1
                                      have p823_1 := h823c.2.1
                                      have p823_2 := h823c.2.2.1
                                      have p823_3 := h823c.2.2.2
                                      linarith only [h0, h732, h733, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p823_1, u2ehi3]
                                    · have p823_0 := h823c.1
                                      have p823_1 := h823c.2.1
                                      have p823_2 := h823c.2.2.1
                                      have p823_3 := h823c.2.2.2
                                      linarith only [h0, h732, h734, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p823_1, u2ehi4]
                                    · have p823_0 := h823c.1
                                      have p823_1 := h823c.2.1
                                      have p823_2 := h823c.2.2.1
                                      have p823_3 := h823c.2.2.2
                                      linarith only [h737, h817, hc01, hc14, hlam, hphi, p823_1]
                                    · have p823_0 := h823c.1
                                      have p823_1 := h823c.2.1
                                      have p823_2 := h823c.2.2.1
                                      have p823_3 := h823c.2.2.2
                                      linarith only [h733, hlam, p823_0]
                                    · have p823_0 := h823c.1
                                      have p823_1 := h823c.2.1
                                      have p823_2 := h823c.2.2.1
                                      have p823_3 := h823c.2.2.2
                                      linarith only [h735, hlam, p823_0]
                                    · have p823_0 := h823c.1
                                      have p823_1 := h823c.2.1
                                      have p823_2 := h823c.2.2.1
                                      have p823_3 := h823c.2.2.2
                                      linarith only [hlam, p823_0]
                                    · have p823_0 := h823c.1
                                      have p823_1 := h823c.2.1
                                      have p823_2 := h823c.2.2.1
                                      have p823_3 := h823c.2.2.2
                                      linarith only [h737, hlam, p823_0]
                                    · have p823_0 := h823c.1
                                      have p823_1 := h823c.2.1
                                      have p823_2 := h823c.2.2.1
                                      have p823_3 := h823c.2.2.2
                                      linarith only [h659, h817, hc01, hc14, hlam, hphi, p823_1]
                                    · have p823_0 := h823c.1
                                      have p823_1 := h823c.2.1
                                      have p823_2 := h823c.2.2.1
                                      have p823_3 := h823c.2.2.2
                                      linarith only [h734, hlam, p823_1]
                                    · have p823_0 := h823c.1
                                      have p823_1 := h823c.2.1
                                      have p823_2 := h823c.2.2.1
                                      have p823_3 := h823c.2.2.2
                                      linarith only [h736, hlam, p823_0]
                                    · have p823_0 := h823c.1
                                      have p823_1 := h823c.2.1
                                      have p823_2 := h823c.2.2.1
                                      have p823_3 := h823c.2.2.2
                                      linarith only [h737, h817, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p823_1, u4ehi0]
                                    · have p823_0 := h823c.1
                                      have p823_1 := h823c.2.1
                                      have p823_2 := h823c.2.2.1
                                      have p823_3 := h823c.2.2.2
                                      linarith only [hlam, p823_0]
                              · linarith only [h735, h737, h813, h816, h817, h818, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h850 | h850
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h851 | h851
                                · linarith only [h560, h817, h851, hc01, hc24, hlam, hphi, ht12]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h853 | h853
                                  · linarith only [h560, h733, h817, h850, h853, hc23, hlam, hphi, u2ehi3]
                                  · rcases h0bigk with h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c | h855c
                                    · have p855_0 := h855c.1
                                      have p855_1 := h855c.2.1
                                      have p855_2 := h855c.2.2.1
                                      have p855_3 := h855c.2.2.2
                                      linarith only [hlam, p855_0]
                                    · have p855_0 := h855c.1
                                      have p855_1 := h855c.2.1
                                      have p855_2 := h855c.2.2.1
                                      have p855_3 := h855c.2.2.2
                                      linarith only [h0, hlam, p855_1]
                                    · have p855_0 := h855c.1
                                      have p855_1 := h855c.2.1
                                      have p855_2 := h855c.2.2.1
                                      have p855_3 := h855c.2.2.2
                                      linarith only [h386, hlam, p855_0]
                                    · have p855_0 := h855c.1
                                      have p855_1 := h855c.2.1
                                      have p855_2 := h855c.2.2.1
                                      have p855_3 := h855c.2.2.2
                                      linarith only [h560, hlam, p855_1]
                                    · have p855_0 := h855c.1
                                      have p855_1 := h855c.2.1
                                      have p855_2 := h855c.2.2.1
                                      have p855_3 := h855c.2.2.2
                                      linarith only [h659, hlam, p855_1]
                                    · have p855_0 := h855c.1
                                      have p855_1 := h855c.2.1
                                      have p855_2 := h855c.2.2.1
                                      have p855_3 := h855c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p855_1]
                                    · have p855_0 := h855c.1
                                      have p855_1 := h855c.2.1
                                      have p855_2 := h855c.2.2.1
                                      have p855_3 := h855c.2.2.2
                                      linarith only [hlam, p855_0]
                                    · have p855_0 := h855c.1
                                      have p855_1 := h855c.2.1
                                      have p855_2 := h855c.2.2.1
                                      have p855_3 := h855c.2.2.2
                                      linarith only [h0, h386, hc01, hc12, hlam, hphi, p855_1]
                                    · have p855_0 := h855c.1
                                      have p855_1 := h855c.2.1
                                      have p855_2 := h855c.2.2.1
                                      have p855_3 := h855c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p855_1, u4ehi0]
                                    · have p855_0 := h855c.1
                                      have p855_1 := h855c.2.1
                                      have p855_2 := h855c.2.2.1
                                      have p855_3 := h855c.2.2.2
                                      linarith only [h0, h659, hc01, hc12, hlam, hphi, p855_1]
                                    · have p855_0 := h855c.1
                                      have p855_1 := h855c.2.1
                                      have p855_2 := h855c.2.2.1
                                      have p855_3 := h855c.2.2.2
                                      linarith only [h386, h813, hc01, hc12, hlam, hphi, p855_1]
                                    · have p855_0 := h855c.1
                                      have p855_1 := h855c.2.1
                                      have p855_2 := h855c.2.2.1
                                      have p855_3 := h855c.2.2.2
                                      linarith only [h732, hlam, p855_1]
                                    · have p855_0 := h855c.1
                                      have p855_1 := h855c.2.1
                                      have p855_2 := h855c.2.2.1
                                      have p855_3 := h855c.2.2.2
                                      linarith only [hlam, p855_0]
                                    · have p855_0 := h855c.1
                                      have p855_1 := h855c.2.1
                                      have p855_2 := h855c.2.2.1
                                      have p855_3 := h855c.2.2.2
                                      linarith only [h386, h733, h813, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p855_1, u2ehi3]
                                    · have p855_0 := h855c.1
                                      have p855_1 := h855c.2.1
                                      have p855_2 := h855c.2.2.1
                                      have p855_3 := h855c.2.2.2
                                      linarith only [h386, h734, h813, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p855_1, u2ehi4]
                                    · have p855_0 := h855c.1
                                      have p855_1 := h855c.2.1
                                      have p855_2 := h855c.2.2.1
                                      have p855_3 := h855c.2.2.2
                                      linarith only [h560, hc01, hc14, hlam, hphi, p855_1]
                                    · have p855_0 := h855c.1
                                      have p855_1 := h855c.2.1
                                      have p855_2 := h855c.2.2.1
                                      have p855_3 := h855c.2.2.2
                                      linarith only [h733, hlam, p855_0]
                                    · have p855_0 := h855c.1
                                      have p855_1 := h855c.2.1
                                      have p855_2 := h855c.2.2.1
                                      have p855_3 := h855c.2.2.2
                                      linarith only [h735, hlam, p855_0]
                                    · have p855_0 := h855c.1
                                      have p855_1 := h855c.2.1
                                      have p855_2 := h855c.2.2.1
                                      have p855_3 := h855c.2.2.2
                                      linarith only [hlam, p855_0]
                                    · have p855_0 := h855c.1
                                      have p855_1 := h855c.2.1
                                      have p855_2 := h855c.2.2.1
                                      have p855_3 := h855c.2.2.2
                                      linarith only [h737, hlam, p855_0]
                                    · have p855_0 := h855c.1
                                      have p855_1 := h855c.2.1
                                      have p855_2 := h855c.2.2.1
                                      have p855_3 := h855c.2.2.2
                                      linarith only [h659, hc01, hc15, hlam, hphi, p855_1]
                                    · have p855_0 := h855c.1
                                      have p855_1 := h855c.2.1
                                      have p855_2 := h855c.2.2.1
                                      have p855_3 := h855c.2.2.2
                                      linarith only [h734, hlam, p855_1]
                                    · have p855_0 := h855c.1
                                      have p855_1 := h855c.2.1
                                      have p855_2 := h855c.2.2.1
                                      have p855_3 := h855c.2.2.2
                                      linarith only [h736, hlam, p855_0]
                                    · have p855_0 := h855c.1
                                      have p855_1 := h855c.2.1
                                      have p855_2 := h855c.2.2.1
                                      have p855_3 := h855c.2.2.2
                                      linarith only [h737, hc45, hlam, hphi, p855_1, u4ehi0]
                                    · have p855_0 := h855c.1
                                      have p855_1 := h855c.2.1
                                      have p855_2 := h855c.2.2.1
                                      have p855_3 := h855c.2.2.2
                                      linarith only [hlam, p855_0]
                              · linarith only [h560, h735, h817, h850, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                          · linarith only [h386, h735, h737, h816, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h0, h732, h815, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h0, h734, h814, hc24, hlam, hphi, u2ehi4]
                    · linarith only [h0, h734, h813, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h886 | h886
                  · linarith only [h735, h736, h886, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h888 | h888
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h889 | h889
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h890 | h890
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h891 | h891
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h892 | h892
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h893 | h893
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h894 | h894
                                · linarith only [h733, h886, h894, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h896 | h896
                                  · linarith only [h732, h733, h886, h893, h896, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                  · linarith only [h732, h736, h893, h896, hc45, hlam, hphi, u4ehi3]
                              · linarith only [h735, h736, h893, hc23, hc35, hlam, hphi]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h900 | h900
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h901 | h901
                                · linarith only [h560, h892, h901, hc01, hc24, hlam, hphi, ht12]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h903 | h903
                                  · linarith only [h560, h732, h733, h736, h892, h900, h903, hc35, hlam, hphi, ht23, u2ehi3]
                                  · linarith only [h732, h736, h900, h903, hc45, hlam, hphi, u4ehi3]
                              · linarith only [h735, h736, h900, hc35, hlam, hphi, ht23, u2ehi2]
                          · linarith only [h735, h736, h891, hc13, hc35, hlam, hphi]
                        · linarith only [h0, h732, h890, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h0, h732, h889, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h0, h734, h888, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h911 | h911
                · rcases m.htr 0 4 5 (by decide) (by decide) with h912 | h912
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h913 | h913
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h914 | h914
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h915 | h915
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h916 | h916
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h917 | h917
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h918 | h918
                              · linarith only [h734, h735, h911, h918, hc23, hlam, hphi, u2ehi4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h920 | h920
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h921 | h921
                                  · linarith only [h735, h911, h913, h916, h921, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                                  · linarith only [h733, h735, h920, h921, hc02, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                · linarith only [h735, h911, h912, h913, h916, h920, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                            · linarith only [h735, h911, h912, h916, h917, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h926 | h926
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h927 | h927
                              · linarith only [h386, h732, h916, h927, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h929 | h929
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h930 | h930
                                  · rcases h0bigk with h931c | h931c | h931c | h931c | h931c | h931c | h931c | h931c | h931c | h931c | h931c | h931c | h931c | h931c | h931c | h931c | h931c | h931c | h931c | h931c | h931c | h931c | h931c | h931c | h931c
                                    · have p931_0 := h931c.1
                                      have p931_1 := h931c.2.1
                                      have p931_2 := h931c.2.2.1
                                      have p931_3 := h931c.2.2.2
                                      linarith only [hlam, p931_0]
                                    · have p931_0 := h931c.1
                                      have p931_1 := h931c.2.1
                                      have p931_2 := h931c.2.2.1
                                      have p931_3 := h931c.2.2.2
                                      linarith only [h0, hlam, p931_1]
                                    · have p931_0 := h931c.1
                                      have p931_1 := h931c.2.1
                                      have p931_2 := h931c.2.2.1
                                      have p931_3 := h931c.2.2.2
                                      linarith only [h386, hlam, p931_0]
                                    · have p931_0 := h931c.1
                                      have p931_1 := h931c.2.1
                                      have p931_2 := h931c.2.2.1
                                      have p931_3 := h931c.2.2.2
                                      linarith only [h560, hlam, p931_1]
                                    · have p931_0 := h931c.1
                                      have p931_1 := h931c.2.1
                                      have p931_2 := h931c.2.2.1
                                      have p931_3 := h931c.2.2.2
                                      linarith only [h659, hlam, p931_1]
                                    · have p931_0 := h931c.1
                                      have p931_1 := h931c.2.1
                                      have p931_2 := h931c.2.2.1
                                      have p931_3 := h931c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p931_1]
                                    · have p931_0 := h931c.1
                                      have p931_1 := h931c.2.1
                                      have p931_2 := h931c.2.2.1
                                      have p931_3 := h931c.2.2.2
                                      linarith only [hlam, p931_0]
                                    · have p931_0 := h931c.1
                                      have p931_1 := h931c.2.1
                                      have p931_2 := h931c.2.2.1
                                      have p931_3 := h931c.2.2.2
                                      linarith only [h0, h911, h930, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p931_1, u4ehi4]
                                    · have p931_0 := h931c.1
                                      have p931_1 := h931c.2.1
                                      have p931_2 := h931c.2.2.1
                                      have p931_3 := h931c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p931_1, u4ehi0]
                                    · have p931_0 := h931c.1
                                      have p931_1 := h931c.2.1
                                      have p931_2 := h931c.2.2.1
                                      have p931_3 := h931c.2.2.2
                                      linarith only [h0, h386, h734, h911, h916, h930, hc12, hc34, hlam, hphi, ht01, ht0b, ht23, ht45, ht5b, p931_1, u2ehi4, u4ehi4]
                                    · have p931_0 := h931c.1
                                      have p931_1 := h931c.2.1
                                      have p931_2 := h931c.2.2.1
                                      have p931_3 := h931c.2.2.2
                                      linarith only [h386, h916, hc01, hc34, hlam, hphi, ht12, ht23, p931_1]
                                    · have p931_0 := h931c.1
                                      have p931_1 := h931c.2.1
                                      have p931_2 := h931c.2.2.1
                                      have p931_3 := h931c.2.2.2
                                      linarith only [h732, hlam, p931_1]
                                    · have p931_0 := h931c.1
                                      have p931_1 := h931c.2.1
                                      have p931_2 := h931c.2.2.1
                                      have p931_3 := h931c.2.2.2
                                      linarith only [hlam, p931_0]
                                    · have p931_0 := h931c.1
                                      have p931_1 := h931c.2.1
                                      have p931_2 := h931c.2.2.1
                                      have p931_3 := h931c.2.2.2
                                      linarith only [h735, hlam, p931_1]
                                    · have p931_0 := h931c.1
                                      have p931_1 := h931c.2.1
                                      have p931_2 := h931c.2.2.1
                                      have p931_3 := h931c.2.2.2
                                      linarith only [h386, h734, h916, hc34, hlam, hphi, ht23, p931_1, u2ehi4]
                                    · have p931_0 := h931c.1
                                      have p931_1 := h931c.2.1
                                      have p931_2 := h931c.2.2.1
                                      have p931_3 := h931c.2.2.2
                                      linarith only [h560, h916, hc01, hc34, hlam, hphi, ht12, ht23, p931_1]
                                    · have p931_0 := h931c.1
                                      have p931_1 := h931c.2.1
                                      have p931_2 := h931c.2.2.1
                                      have p931_3 := h931c.2.2.2
                                      linarith only [h733, hlam, p931_0]
                                    · have p931_0 := h931c.1
                                      have p931_1 := h931c.2.1
                                      have p931_2 := h931c.2.2.1
                                      have p931_3 := h931c.2.2.2
                                      linarith only [h560, h911, h916, h930, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p931_1, u4ehi4]
                                    · have p931_0 := h931c.1
                                      have p931_1 := h931c.2.1
                                      have p931_2 := h931c.2.2.1
                                      have p931_3 := h931c.2.2.2
                                      linarith only [hlam, p931_0]
                                    · have p931_0 := h931c.1
                                      have p931_1 := h931c.2.1
                                      have p931_2 := h931c.2.2.1
                                      have p931_3 := h931c.2.2.2
                                      linarith only [h560, h734, h916, hc34, hlam, hphi, ht23, p931_1, u2ehi4]
                                    · have p931_0 := h931c.1
                                      have p931_1 := h931c.2.1
                                      have p931_2 := h931c.2.2.1
                                      have p931_3 := h931c.2.2.2
                                      linarith only [h659, hc01, hc15, hlam, hphi, p931_1]
                                    · have p931_0 := h931c.1
                                      have p931_1 := h931c.2.1
                                      have p931_2 := h931c.2.2.1
                                      have p931_3 := h931c.2.2.2
                                      linarith only [h734, hlam, p931_1]
                                    · have p931_0 := h931c.1
                                      have p931_1 := h931c.2.1
                                      have p931_2 := h931c.2.2.1
                                      have p931_3 := h931c.2.2.2
                                      linarith only [h911, hlam, p931_0]
                                    · have p931_0 := h931c.1
                                      have p931_1 := h931c.2.1
                                      have p931_2 := h931c.2.2.1
                                      have p931_3 := h931c.2.2.2
                                      linarith only [h912, hlam, p931_1]
                                    · have p931_0 := h931c.1
                                      have p931_1 := h931c.2.1
                                      have p931_2 := h931c.2.2.1
                                      have p931_3 := h931c.2.2.2
                                      linarith only [hlam, p931_0]
                                  · linarith only [h386, h916, h929, h930, hc01, hc24, hlam, hphi, ht12]
                                · linarith only [h386, h911, h912, h916, h929, hc34, hlam, hphi, ht23, u2ehi3]
                            · linarith only [h386, h560, h911, h912, h916, h926, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h734, h735, h911, h915, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h0, h733, h914, hlam]
                    · linarith only [h0, h732, h913, hlam]
                  · linarith only [h735, h911, h912, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h964 | h964
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h965 | h965
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h966 | h966
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h967 | h967
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h968 | h968
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h969 | h969
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h970 | h970
                              · linarith only [h732, h735, h970, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h972 | h972
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h973 | h973
                                  · rcases h0bigk with h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c | h974c
                                    · have p974_0 := h974c.1
                                      have p974_1 := h974c.2.1
                                      have p974_2 := h974c.2.2.1
                                      have p974_3 := h974c.2.2.2
                                      linarith only [hlam, p974_0]
                                    · have p974_0 := h974c.1
                                      have p974_1 := h974c.2.1
                                      have p974_2 := h974c.2.2.1
                                      have p974_3 := h974c.2.2.2
                                      linarith only [h0, hlam, p974_1]
                                    · have p974_0 := h974c.1
                                      have p974_1 := h974c.2.1
                                      have p974_2 := h974c.2.2.1
                                      have p974_3 := h974c.2.2.2
                                      linarith only [h386, hlam, p974_0]
                                    · have p974_0 := h974c.1
                                      have p974_1 := h974c.2.1
                                      have p974_2 := h974c.2.2.1
                                      have p974_3 := h974c.2.2.2
                                      linarith only [h560, hlam, p974_1]
                                    · have p974_0 := h974c.1
                                      have p974_1 := h974c.2.1
                                      have p974_2 := h974c.2.2.1
                                      have p974_3 := h974c.2.2.2
                                      linarith only [h659, hlam, p974_1]
                                    · have p974_0 := h974c.1
                                      have p974_1 := h974c.2.1
                                      have p974_2 := h974c.2.2.1
                                      have p974_3 := h974c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p974_1]
                                    · have p974_0 := h974c.1
                                      have p974_1 := h974c.2.1
                                      have p974_2 := h974c.2.2.1
                                      have p974_3 := h974c.2.2.2
                                      linarith only [hlam, p974_0]
                                    · have p974_0 := h974c.1
                                      have p974_1 := h974c.2.1
                                      have p974_2 := h974c.2.2.1
                                      have p974_3 := h974c.2.2.2
                                      linarith only [h0, h732, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p974_1, u2ehi2]
                                    · have p974_0 := h974c.1
                                      have p974_1 := h974c.2.1
                                      have p974_2 := h974c.2.2.1
                                      have p974_3 := h974c.2.2.2
                                      linarith only [h0, h733, h972, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p974_1, u4ehi4]
                                    · have p974_0 := h974c.1
                                      have p974_1 := h974c.2.1
                                      have p974_2 := h974c.2.2.1
                                      have p974_3 := h974c.2.2.2
                                      linarith only [h0, h732, h911, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p974_1, u2ehi2]
                                    · have p974_0 := h974c.1
                                      have p974_1 := h974c.2.1
                                      have p974_2 := h974c.2.2.1
                                      have p974_3 := h974c.2.2.2
                                      linarith only [h386, h965, hc01, hc12, hlam, hphi, p974_1]
                                    · have p974_0 := h974c.1
                                      have p974_1 := h974c.2.1
                                      have p974_2 := h974c.2.2.1
                                      have p974_3 := h974c.2.2.2
                                      linarith only [h732, hlam, p974_1]
                                    · have p974_0 := h974c.1
                                      have p974_1 := h974c.2.1
                                      have p974_2 := h974c.2.2.1
                                      have p974_3 := h974c.2.2.2
                                      linarith only [hlam, p974_0]
                                    · have p974_0 := h974c.1
                                      have p974_1 := h974c.2.1
                                      have p974_2 := h974c.2.2.1
                                      have p974_3 := h974c.2.2.2
                                      linarith only [h735, hlam, p974_1]
                                    · have p974_0 := h974c.1
                                      have p974_1 := h974c.2.1
                                      have p974_2 := h974c.2.2.1
                                      have p974_3 := h974c.2.2.2
                                      linarith only [h911, hlam, p974_1]
                                    · have p974_0 := h974c.1
                                      have p974_1 := h974c.2.1
                                      have p974_2 := h974c.2.2.1
                                      have p974_3 := h974c.2.2.2
                                      linarith only [h560, hc01, hc14, hlam, hphi, p974_1]
                                    · have p974_0 := h974c.1
                                      have p974_1 := h974c.2.1
                                      have p974_2 := h974c.2.2.1
                                      have p974_3 := h974c.2.2.2
                                      linarith only [h733, hlam, p974_0]
                                    · have p974_0 := h974c.1
                                      have p974_1 := h974c.2.1
                                      have p974_2 := h974c.2.2.1
                                      have p974_3 := h974c.2.2.2
                                      linarith only [h735, h965, h968, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p974_1]
                                    · have p974_0 := h974c.1
                                      have p974_1 := h974c.2.1
                                      have p974_2 := h974c.2.2.1
                                      have p974_3 := h974c.2.2.2
                                      linarith only [hlam, p974_0]
                                    · have p974_0 := h974c.1
                                      have p974_1 := h974c.2.1
                                      have p974_2 := h974c.2.2.1
                                      have p974_3 := h974c.2.2.2
                                      linarith only [h735, h965, h968, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p974_1]
                                    · have p974_0 := h974c.1
                                      have p974_1 := h974c.2.1
                                      have p974_2 := h974c.2.2.1
                                      have p974_3 := h974c.2.2.2
                                      linarith only [h659, hc01, hc15, hlam, hphi, p974_1]
                                    · have p974_0 := h974c.1
                                      have p974_1 := h974c.2.1
                                      have p974_2 := h974c.2.2.1
                                      have p974_3 := h974c.2.2.2
                                      linarith only [h734, hlam, p974_1]
                                    · have p974_0 := h974c.1
                                      have p974_1 := h974c.2.1
                                      have p974_2 := h974c.2.2.1
                                      have p974_3 := h974c.2.2.2
                                      linarith only [h732, h911, h965, h968, h973, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p974_1, u2ehi2]
                                    · have p974_0 := h974c.1
                                      have p974_1 := h974c.2.1
                                      have p974_2 := h974c.2.2.1
                                      have p974_3 := h974c.2.2.2
                                      linarith only [h964, hlam, p974_1]
                                    · have p974_0 := h974c.1
                                      have p974_1 := h974c.2.1
                                      have p974_2 := h974c.2.2.1
                                      have p974_3 := h974c.2.2.2
                                      linarith only [hlam, p974_0]
                                  · linarith only [h0, h733, h735, h972, h973, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                                · linarith only [h735, h964, h970, h972, hc34, hlam, hphi, ht23, u2ehi2]
                            · linarith only [h735, h964, h965, h968, h969, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1003 | h1003
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1004 | h1004
                              · linarith only [h1004, h386, h968, hc01, hc23, hlam, hphi, ht12]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1006 | h1006
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1007 | h1007
                                  · rcases h0bigk with h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c | h1008c
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [hlam, p1008_0]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h0, hlam, p1008_1]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h386, hlam, p1008_0]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h560, hlam, p1008_1]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h659, hlam, p1008_1]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p1008_1]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [hlam, p1008_0]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h0, h732, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1008_1, u2ehi2]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1008_1, u4ehi0]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h0, h659, hc01, hc12, hlam, hphi, p1008_1]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h911, hc01, hc35, hlam, hphi, ht12, ht23, p1008_1]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h732, hlam, p1008_1]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [hlam, p1008_0]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h735, hlam, p1008_1]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h911, hlam, p1008_1]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h560, hc01, hc14, hlam, hphi, p1008_1]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h733, hlam, p1008_0]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h560, h732, h968, hc34, hlam, hphi, ht23, p1008_1, u2ehi2]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [hlam, p1008_0]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h560, h732, h911, h968, hc34, hlam, hphi, ht23, p1008_1, u2ehi2]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h1003, h659, h968, hc01, hc34, hlam, hphi, ht12, ht23, p1008_1]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h734, hlam, p1008_1]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h1003, h659, h732, h968, hc34, hlam, hphi, ht23, p1008_1, u2ehi2]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [h964, hlam, p1008_1]
                                    · have p1008_0 := h1008c.1
                                      have p1008_1 := h1008c.2.1
                                      have p1008_2 := h1008c.2.2.1
                                      have p1008_3 := h1008c.2.2.2
                                      linarith only [hlam, p1008_0]
                                  · linarith only [h1006, h1007, h560, h968, hc01, hc24, hlam, hphi, ht12]
                                · linarith only [h1006, h560, h964, h968, hc34, hlam, hphi, ht23, u2ehi3]
                            · linarith only [h1003, h560, h964, hlam]
                        · linarith only [h0, h732, h967, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h0, h734, h966, hc24, hlam, hphi, u2ehi4]
                    · linarith only [h0, h734, h965, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1040 | h1040
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1041 | h1041
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1042 | h1042
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1043 | h1043
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1044 | h1044
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1045 | h1045
                              · linarith only [h1040, h1043, h1044, h1045, h732, h735, h964, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1047 | h1047
                                · linarith only [h1047, h733, h964, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1049 | h1049
                                  · linarith only [h1049, h732, h735, h964, hc34, hlam, hphi, ht23, u2ehi2]
                                  · linarith only [h1040, h1043, h1044, h1049, h732, h735, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h1043, h1044, h732, h735, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1053 | h1053
                            · linarith only [h1043, h1053, h732, h735, h964, hc34, hlam, hphi, ht23, u2ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1055 | h1055
                              · linarith only [h1043, h1053, h1055, h386, h732, hc45, hlam, hphi, u4ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1057 | h1057
                                · linarith only [h1043, h1053, h1057, h386, h732, hc24, hlam, hphi, u2ehi2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1059 | h1059
                                  · linarith only [h1053, h1059, h560, h733, hc34, hlam, hphi, ht23, u2ehi3]
                                  · linarith only [h1059, h732, h735, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h0, h1042, h732, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h0, h1041, h733, hlam]
                    · linarith only [h0, h1040, h732, hlam]
            · linarith only [h732, h734, hc25, hlam, hphi, u2ehi2]
          · linarith only [h732, h733, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1067 | h1067
          · linarith only [h1067, h732, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1069 | h1069
            · linarith only [h1069, h732, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1071 | h1071
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1072 | h1072
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1073 | h1073
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1074 | h1074
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1075 | h1075
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1076 | h1076
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1077 | h1077
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1078 | h1078
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1079 | h1079
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1080 | h1080
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1081 | h1081
                                  · linarith only [h1071, h1074, h1081, h732, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                                  · linarith only [h1071, h1073, h1074, h1081, h732, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                                · linarith only [h1071, h1073, h1074, h1080, h732, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                              · linarith only [h1079, h732, hc34, hlam, hphi, ht23, u2ehi0]
                            · linarith only [h1067, h1071, h1073, h1075, h1078, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                          · linarith only [h1071, h1074, h1077, h386, h732, hc01, hc12, hlam, hphi]
                        · linarith only [h1071, h1074, h1076, h732, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                      · linarith only [h1074, h1075, h732, hc24, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1090 | h1090
                      · linarith only [h1074, h1090, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1092 | h1092
                        · linarith only [h1074, h1092, hc23, hlam, hphi, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1094 | h1094
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1095 | h1095
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1096 | h1096
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1097 | h1097
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1098 | h1098
                                  · rcases h0bigk with h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c | h1099c
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [hlam, p1099_0]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h0, hlam, p1099_1]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h386, hlam, p1099_0]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h560, hlam, p1099_1]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h659, hlam, p1099_1]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h0, h1092, h1096, h1097, hc01, hc23, hlam, hphi, ht12, p1099_1]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [hlam, p1099_0]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h732, hlam, p1099_0]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h1067, hlam, p1099_1]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h1069, hlam, p1099_0]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h1074, h386, hc01, hc23, hlam, hphi, ht12, p1099_1]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h1074, h386, hc23, hlam, hphi, p1099_1, u2ehi0]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [hlam, p1099_0]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h1071, h1074, h1098, h386, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1099_1, u4ehi4]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h1074, h386, h659, hc01, hc23, hlam, hphi, ht12, p1099_1]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h560, hc01, hc14, hlam, hphi, p1099_1]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h1067, h1096, hc23, hlam, hphi, p1099_1, u2ehi0]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h1071, hlam, p1099_0]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [hlam, p1099_0]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h1069, h1071, h1074, h386, hc23, hlam, hphi, p1099_1, u2ehi0]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h659, hc01, hc15, hlam, hphi, p1099_1]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h1069, h1096, h1097, hc23, hlam, hphi, p1099_1, u2ehi0]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h1072, hlam, p1099_0]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [h1073, hlam, p1099_1]
                                    · have p1099_0 := h1099c.1
                                      have p1099_1 := h1099c.2.1
                                      have p1099_2 := h1099c.2.2.1
                                      have p1099_3 := h1099c.2.2.2
                                      linarith only [hlam, p1099_0]
                                  · rcases h0bigk with h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c | h1125c
                                    · have p1125_0 := h1125c.1
                                      have p1125_1 := h1125c.2.1
                                      have p1125_2 := h1125c.2.2.1
                                      have p1125_3 := h1125c.2.2.2
                                      linarith only [hlam, p1125_0]
                                    · have p1125_0 := h1125c.1
                                      have p1125_1 := h1125c.2.1
                                      have p1125_2 := h1125c.2.2.1
                                      have p1125_3 := h1125c.2.2.2
                                      linarith only [h0, hlam, p1125_1]
                                    · have p1125_0 := h1125c.1
                                      have p1125_1 := h1125c.2.1
                                      have p1125_2 := h1125c.2.2.1
                                      have p1125_3 := h1125c.2.2.2
                                      linarith only [h386, hlam, p1125_0]
                                    · have p1125_0 := h1125c.1
                                      have p1125_1 := h1125c.2.1
                                      have p1125_2 := h1125c.2.2.1
                                      have p1125_3 := h1125c.2.2.2
                                      linarith only [h560, hlam, p1125_1]
                                    · have p1125_0 := h1125c.1
                                      have p1125_1 := h1125c.2.1
                                      have p1125_2 := h1125c.2.2.1
                                      have p1125_3 := h1125c.2.2.2
                                      linarith only [h659, hlam, p1125_1]
                                    · have p1125_0 := h1125c.1
                                      have p1125_1 := h1125c.2.1
                                      have p1125_2 := h1125c.2.2.1
                                      have p1125_3 := h1125c.2.2.2
                                      linarith only [h0, h1092, h1096, h1097, hc01, hc23, hlam, hphi, ht12, p1125_1]
                                    · have p1125_0 := h1125c.1
                                      have p1125_1 := h1125c.2.1
                                      have p1125_2 := h1125c.2.2.1
                                      have p1125_3 := h1125c.2.2.2
                                      linarith only [hlam, p1125_0]
                                    · have p1125_0 := h1125c.1
                                      have p1125_1 := h1125c.2.1
                                      have p1125_2 := h1125c.2.2.1
                                      have p1125_3 := h1125c.2.2.2
                                      linarith only [h732, hlam, p1125_0]
                                    · have p1125_0 := h1125c.1
                                      have p1125_1 := h1125c.2.1
                                      have p1125_2 := h1125c.2.2.1
                                      have p1125_3 := h1125c.2.2.2
                                      linarith only [h1067, hlam, p1125_1]
                                    · have p1125_0 := h1125c.1
                                      have p1125_1 := h1125c.2.1
                                      have p1125_2 := h1125c.2.2.1
                                      have p1125_3 := h1125c.2.2.2
                                      linarith only [h1069, hlam, p1125_0]
                                    · have p1125_0 := h1125c.1
                                      have p1125_1 := h1125c.2.1
                                      have p1125_2 := h1125c.2.2.1
                                      have p1125_3 := h1125c.2.2.2
                                      linarith only [h1074, h386, hc01, hc23, hlam, hphi, ht12, p1125_1]
                                    · have p1125_0 := h1125c.1
                                      have p1125_1 := h1125c.2.1
                                      have p1125_2 := h1125c.2.2.1
                                      have p1125_3 := h1125c.2.2.2
                                      linarith only [h1074, h386, hc23, hlam, hphi, p1125_1, u2ehi0]
                                    · have p1125_0 := h1125c.1
                                      have p1125_1 := h1125c.2.1
                                      have p1125_2 := h1125c.2.2.1
                                      have p1125_3 := h1125c.2.2.2
                                      linarith only [hlam, p1125_0]
                                    · have p1125_0 := h1125c.1
                                      have p1125_1 := h1125c.2.1
                                      have p1125_2 := h1125c.2.2.1
                                      have p1125_3 := h1125c.2.2.2
                                      linarith only [h1074, h386, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1125_1, u4ehi0]
                                    · have p1125_0 := h1125c.1
                                      have p1125_1 := h1125c.2.1
                                      have p1125_2 := h1125c.2.2.1
                                      have p1125_3 := h1125c.2.2.2
                                      linarith only [h1069, h1074, h386, hc23, hlam, hphi, p1125_1, u2ehi0]
                                    · have p1125_0 := h1125c.1
                                      have p1125_1 := h1125c.2.1
                                      have p1125_2 := h1125c.2.2.1
                                      have p1125_3 := h1125c.2.2.2
                                      linarith only [h1090, h1096, h560, hc01, hc23, hlam, hphi, ht12, p1125_1]
                                    · have p1125_0 := h1125c.1
                                      have p1125_1 := h1125c.2.1
                                      have p1125_2 := h1125c.2.2.1
                                      have p1125_3 := h1125c.2.2.2
                                      linarith only [h1090, h1096, h560, hc23, hlam, hphi, p1125_1, u2ehi0]
                                    · have p1125_0 := h1125c.1
                                      have p1125_1 := h1125c.2.1
                                      have p1125_2 := h1125c.2.2.1
                                      have p1125_3 := h1125c.2.2.2
                                      linarith only [h1071, hlam, p1125_0]
                                    · have p1125_0 := h1125c.1
                                      have p1125_1 := h1125c.2.1
                                      have p1125_2 := h1125c.2.2.1
                                      have p1125_3 := h1125c.2.2.2
                                      linarith only [hlam, p1125_0]
                                    · have p1125_0 := h1125c.1
                                      have p1125_1 := h1125c.2.1
                                      have p1125_2 := h1125c.2.2.1
                                      have p1125_3 := h1125c.2.2.2
                                      linarith only [h1069, h1090, h1096, h560, hc23, hlam, hphi, p1125_1, u2ehi0]
                                    · have p1125_0 := h1125c.1
                                      have p1125_1 := h1125c.2.1
                                      have p1125_2 := h1125c.2.2.1
                                      have p1125_3 := h1125c.2.2.2
                                      linarith only [h1092, h1096, h1097, h659, hc01, hc23, hlam, hphi, ht12, p1125_1]
                                    · have p1125_0 := h1125c.1
                                      have p1125_1 := h1125c.2.1
                                      have p1125_2 := h1125c.2.2.1
                                      have p1125_3 := h1125c.2.2.2
                                      linarith only [h1092, h1096, h1097, h659, hc23, hlam, hphi, p1125_1, u2ehi0]
                                    · have p1125_0 := h1125c.1
                                      have p1125_1 := h1125c.2.1
                                      have p1125_2 := h1125c.2.2.1
                                      have p1125_3 := h1125c.2.2.2
                                      linarith only [h1072, hlam, p1125_0]
                                    · have p1125_0 := h1125c.1
                                      have p1125_1 := h1125c.2.1
                                      have p1125_2 := h1125c.2.2.1
                                      have p1125_3 := h1125c.2.2.2
                                      linarith only [h1073, hlam, p1125_1]
                                    · have p1125_0 := h1125c.1
                                      have p1125_1 := h1125c.2.1
                                      have p1125_2 := h1125c.2.2.1
                                      have p1125_3 := h1125c.2.2.2
                                      linarith only [hlam, p1125_0]
                                · linarith only [h1067, h1097, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                              · linarith only [h0, h1074, h1096, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h1073, h1095, h560, hlam]
                          · linarith only [h1071, h1094, h386, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1155 | h1155
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1156 | h1156
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1157 | h1157
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1158 | h1158
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1159 | h1159
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1160 | h1160
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1161 | h1161
                                · linarith only [h1067, h1073, h1155, h1160, h1161, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                                · linarith only [h1067, h1161, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                              · linarith only [h1160, h732, hc34, hlam, hphi, ht23, u2ehi0]
                            · linarith only [h1067, h1156, h1159, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                          · linarith only [h1071, h1155, h1158, h386, h732, hc01, hc12, hlam, hphi]
                        · linarith only [h1071, h1155, h1157, h732, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                      · linarith only [h1155, h1156, h732, hc24, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1169 | h1169
                      · linarith only [h1155, h1169, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1171 | h1171
                        · linarith only [h1155, h1171, hc23, hlam, hphi, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1173 | h1173
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1174 | h1174
                            · linarith only [h1067, h1073, h1169, h1174, hc24, hlam, hphi, u2ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1176 | h1176
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1177 | h1177
                                · linarith only [h1169, h1174, h1176, h1177, hc23, hlam, hphi, u2ehi1]
                                · linarith only [h1067, h1177, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                              · linarith only [h1071, h1176, h386, h732, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                          · linarith only [h1071, h1173, h386, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1182 | h1182
                  · linarith only [h1071, h1072, h1182, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1184 | h1184
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1185 | h1185
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1186 | h1186
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1187 | h1187
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1188 | h1188
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1189 | h1189
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1190 | h1190
                                · linarith only [h1067, h1182, h1189, h1190, hc23, hlam, hphi, u2ehi0]
                                · linarith only [h1067, h1187, h1188, h1190, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                              · linarith only [h1071, h1189, h732, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                            · linarith only [h1067, h1185, h1188, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                          · linarith only [h1071, h1072, h1187, hc13, hc35, hlam, hphi]
                        · linarith only [h1184, h1186, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h1184, h1185, h732, hc24, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1198 | h1198
                      · linarith only [h1184, h1198, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1200 | h1200
                        · linarith only [h1184, h1200, hc23, hlam, hphi, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1202 | h1202
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1203 | h1203
                            · linarith only [h1067, h1182, h1184, h1202, h1203, hc23, hlam, hphi, u2ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1205 | h1205
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1206 | h1206
                                · linarith only [h1067, h1203, h1206, h560, hc24, hlam, hphi, u2ehi0]
                                · linarith only [h1067, h1206, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                              · linarith only [h1071, h1072, h1203, h1205, h659, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                          · linarith only [h1071, h1072, h1202, hc13, hc35, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1211 | h1211
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1212 | h1212
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1213 | h1213
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1214 | h1214
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1215 | h1215
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1216 | h1216
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1217 | h1217
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1218 | h1218
                              · linarith only [h1071, h1218, h732, hc23, hlam, hphi, u2ehi0]
                              · linarith only [h1213, h1216, h1218, h732, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                            · linarith only [h1212, h1217, h560, hlam]
                          · linarith only [h1213, h1216, h732, hc34, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h1214, h1215, hc25, hlam, hphi, u2ehi3]
                      · linarith only [h1213, h1214, h732, hc24, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1225 | h1225
                      · linarith only [h1213, h1225, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1227 | h1227
                        · linarith only [h1213, h1227, hc23, hlam, hphi, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1229 | h1229
                          · linarith only [h1071, h1213, h1229, h732, hc23, hlam, hphi, u2ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1231 | h1231
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1232 | h1232
                              · linarith only [h1213, h1229, h1232, hc23, hlam, hphi, u2ehi1]
                              · linarith only [h1232, h732, hc34, hlam, hphi, ht23, u2ehi0]
                            · linarith only [h1212, h1231, h560, hlam]
                  · linarith only [h1071, h1211, h1212, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1237 | h1237
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1238 | h1238
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1239 | h1239
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1240 | h1240
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1241 | h1241
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1242 | h1242
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1243 | h1243
                              · linarith only [h1071, h1238, h1243, h732, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                              · linarith only [h1243, h732, hc34, hlam, hphi, ht23, u2ehi0]
                            · linarith only [h1237, h1242, h560, hlam]
                          · linarith only [h1238, h1241, h732, hc34, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h1239, h1240, hc25, hlam, hphi, u2ehi3]
                      · linarith only [h1238, h1239, h732, hc24, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1250 | h1250
                      · linarith only [h1238, h1250, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1252 | h1252
                        · linarith only [h1238, h1252, hc23, hlam, hphi, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1254 | h1254
                          · linarith only [h1071, h1238, h1254, h732, hc23, hlam, hphi, u2ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1256 | h1256
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1257 | h1257
                              · linarith only [h1238, h1254, h1257, hc23, hlam, hphi, u2ehi1]
                              · linarith only [h1257, h732, hc34, hlam, hphi, ht23, u2ehi0]
                            · linarith only [h1237, h1256, h560, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1261 | h1261
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1262 | h1262
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1263 | h1263
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1264 | h1264
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1265 | h1265
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1266 | h1266
                              · linarith only [h1071, h1261, h1266, h732, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                              · linarith only [h1266, h732, hc34, hlam, hphi, ht23, u2ehi0]
                            · linarith only [h1067, h1262, h1265, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                          · linarith only [h1261, h1264, h732, hc34, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h1261, h1263, h732, hc25, hlam, hphi, u2ehi0]
                      · linarith only [h1261, h1262, h732, hc24, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1273 | h1273
                      · linarith only [h1261, h1273, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1275 | h1275
                        · linarith only [h1261, h1275, hc23, hlam, hphi, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1277 | h1277
                          · linarith only [h1071, h1261, h1277, h732, hc23, hlam, hphi, u2ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1279 | h1279
                            · linarith only [h1071, h1237, h1273, h1279, h732, hc24, hlam, hphi, u2ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1281 | h1281
                              · linarith only [h1071, h1281, h732, hc23, hlam, hphi, u2ehi0]
                              · linarith only [h1281, h732, hc34, hlam, hphi, ht23, u2ehi0]

theorem r1l7_20_12_14_H_I_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h2ehi := hb2.1
  have h4ehi := hb4.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_14_H_I_L_R_L_R_x0 m hb0 hb2 hb4 h0
  · exact r1l7_20_12_14_H_I_L_R_L_R_x1 m hb0 hb2 hb4 h0

end R2N4
