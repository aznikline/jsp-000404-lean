import Jsp000404.GlobalFiveLowStrongModel

namespace Jsp404.GlobalFiveLowTerminal

set_option maxHeartbeats 32000000 in
theorem model_impossible_1 {n delta : ℝ} (m : FiveModel n delta 1) : False := by
  have hn := m.hn
  obtain ⟨hdelta0, hdelta1⟩ := m.hdelta
  obtain ⟨h010, h011⟩ := m.range 0 1 (by decide)
  obtain ⟨h020, h021⟩ := m.range 0 2 (by decide)
  obtain ⟨h030, h031⟩ := m.range 0 3 (by decide)
  obtain ⟨h040, h041⟩ := m.range 0 4 (by decide)
  obtain ⟨h120, h121⟩ := m.range 1 2 (by decide)
  obtain ⟨h130, h131⟩ := m.range 1 3 (by decide)
  obtain ⟨h140, h141⟩ := m.range 1 4 (by decide)
  obtain ⟨h230, h231⟩ := m.range 2 3 (by decide)
  obtain ⟨h240, h241⟩ := m.range 2 4 (by decide)
  obtain ⟨h340, h341⟩ := m.range 3 4 (by decide)
  have hc10 := m.symm 1 0
  have hc20 := m.symm 2 0
  have hc30 := m.symm 3 0
  have hc40 := m.symm 4 0
  have hc21 := m.symm 2 1
  have hc31 := m.symm 3 1
  have hc41 := m.symm 4 1
  have hc32 := m.symm 3 2
  have hc42 := m.symm 4 2
  have hc43 := m.symm 4 3
  rcases m.triangle 0 1 2 (by decide) (by decide) with ⟨ht012a,ht012b,ht012c,ht012d,ht012e⟩ | ⟨ht012a,ht012b,ht012c,ht012d,ht012e⟩
  ·
    rcases m.triangle 0 1 3 (by decide) (by decide) with ⟨ht013a,ht013b,ht013c,ht013d,ht013e⟩ | ⟨ht013a,ht013b,ht013c,ht013d,ht013e⟩
    ·
      rcases m.triangle 0 1 4 (by decide) (by decide) with ⟨ht014a,ht014b,ht014c,ht014d,ht014e⟩ | ⟨ht014a,ht014b,ht014c,ht014d,ht014e⟩
      ·
        rcases m.triangle 0 2 3 (by decide) (by decide) with ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩ | ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 0 1 3 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h010, h341, ht012b, ht123a, ht234a, hbg2]
                      ·
                        linarith only [hdelta1, h010, ht012a, h341, ht234a, hbg2]
                      ·
                        linarith only [hdelta1, h010, ht012a, h241, ht123a, hbg2]
                      ·
                        have hb0 := m.budget 0 (by decide) 1 2 3 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                        ·
                          linarith only [hdelta1, h010, h341, ht012c, ht123a, ht234a, hbg0]
                        ·
                          linarith only [hn, hdelta1, ht014c, ht034b, ht124c, hbg0, hbg2]
                        ·
                          linarith only [hn, hdelta1, ht014c, ht023b, ht124c, hbg0, hbg2]
                        ·
                          have hb3 := m.budget 3 (by decide) 0 1 2 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc31, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, ht023b, ht123c, ht234b, hbg2, hbg3]
                          ·
                            linarith only [hdelta1, h010, h341, ht013a, ht234a, hbg3]
                          ·
                            linarith only [hdelta1, h010, ht012a, h341, ht123a, hbg3]
                          ·
                            linarith only [hdelta1, ht012a, ht034b, ht123a, ht234a, hbg0, hbg3]
                          ·
                            linarith only [hdelta1, ht023b, ht234b, hbg2, hbg3b, hbg3a]
                          ·
                            linarith only [hdelta1, ht023b, ht123c, ht234b, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, ht023b, ht123c, ht234b, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, ht013c, ht023b, ht234b, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, ht013c, ht023b, ht234b, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, ht012a, ht034b, ht123a, hbg3c, hbg0]
                        ·
                          linarith only [hdelta1, ht014c, ht034b, ht124c, hbg2, hbg0b]
                        ·
                          linarith only [hdelta1, ht014c, ht023b, ht124c, hbg2, hbg0b]
                        ·
                          have hb3 := m.budget 3 (by decide) 0 1 2 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc31, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h010, h131, ht023b, hbg3, hbg0a]
                          ·
                            linarith only [hdelta1, h010, h231, ht013c, ht023b, hbg3, hbg0a]
                          ·
                            linarith only [hdelta1, h010, h341, ht023a, hbg3, hbg0a]
                          ·
                            linarith only [hdelta1, ht012c, ht034b, ht123a, ht234a, hbg3, hbg0c]
                          ·
                            linarith only [hdelta1, ht023b, ht124c, hbg3a, ht134b, hbg2]
                          ·
                            linarith only [hdelta1, ht023b, ht124c, hbg3a, ht134b, hbg2]
                          ·
                            linarith only [hdelta1, ht023b, ht124c, hbg3a, ht134b, hbg2]
                          ·
                            linarith only [hdelta1, ht013c, ht023b, hbg3a, ht234b, hbg2]
                          ·
                            linarith only [hdelta1, ht013c, ht023b, hbg3a, ht234b, hbg2]
                          ·
                            linarith only [hdelta1, ht023a, ht034b, hbg3c, hbg0c]
                        ·
                          linarith only [hdelta1, ht014c, ht124c, hbg0b, hbg2, hbg0a]
                        ·
                          linarith only [hdelta1, ht023c, ht234b, hbg2, hbg0a]
                        ·
                          linarith only [hdelta1, ht014c, ht023b, ht124c, hbg2, hbg0a]
                      ·
                        linarith only [hdelta1, h010, h341, ht012b, ht234a, hbg2c]
                      ·
                        linarith only [hdelta1, h010, h341, ht012b, ht123a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, h010, ht012a, h341, ht234c, hbg2c]
                      ·
                        have hb0 := m.budget 0 (by decide) 1 2 3 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                        ·
                          linarith only [hdelta1, h010, h231, ht012c, hbg0, hbg2a]
                        ·
                          linarith only [hdelta1, ht014c, ht034b, ht124c, hbg0, hbg2b]
                        ·
                          linarith only [hdelta1, ht014c, ht023b, ht124c, hbg0, hbg2b]
                        ·
                          have hb3 := m.budget 3 (by decide) 0 1 2 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc31, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h010, ht012a, h341, ht023b, ht134a, ht234b, hbg2c, hbg3]
                          ·
                            linarith only [hdelta1, h010, h341, ht013a, ht234a, hbg3]
                          ·
                            linarith only [hdelta1, h010, ht012a, h341, hbg3, hbg2a]
                          ·
                            linarith only [hdelta1, ht012a, ht034b, ht234a, hbg0, hbg3, hbg2a]
                          ·
                            linarith only [hdelta1, ht023b, ht234b, hbg3c, hbg2b]
                          ·
                            linarith only [hdelta1, h010, ht012a, h341, ht023b, ht123c, ht234b, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht134a, hbg3c]
                          ·
                            linarith only [hdelta1, h010, ht012a, h341, ht123b, hbg3c]
                          ·
                            linarith only [hdelta1, ht013c, ht234a, hbg3c]
                          ·
                            linarith only [hdelta1, ht012a, ht034b, hbg0, hbg3c, hbg2a]
                        ·
                          linarith only [hdelta1, ht013d, hbg0c]
                        ·
                          linarith only [hdelta1, ht014d, ht023b, hbg0c]
                        ·
                          have hb3 := m.budget 3 (by decide) 0 1 2 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc31, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h010, h131, ht023b, hbg3, hbg0a]
                          ·
                            linarith only [hdelta1, h010, h231, ht013c, ht023b, hbg3, hbg0a]
                          ·
                            linarith only [hdelta1, h010, h341, ht012c, hbg3, hbg2a, hbg0a]
                          ·
                            linarith only [hdelta1, ht012c, ht034b, ht234a, hbg3, hbg2a, hbg0c]
                          ·
                            linarith only [hdelta1, h030, h341, ht234a, hbg3c]
                          ·
                            linarith only [hdelta1, h010, h341, ht023b, ht123c, hbg3c, hbg0a]
                          ·
                            linarith only [hdelta1, ht134a, hbg3c]
                          ·
                            linarith only [hdelta1, h010, h341, ht013a, hbg3c]
                          ·
                            linarith only [hdelta1, ht013c, ht234a, hbg3c]
                          ·
                            linarith only [hdelta1, ht023a, ht034b, hbg3c, hbg0c]
                        ·
                          linarith only [hdelta1, h020, h341, ht012c, ht014c, ht124c, ht234a, hbg2c, hbg0c]
                        ·
                          linarith only [hdelta1, ht012a, ht034b, ht234b, hbg2c, hbg0c]
                        ·
                          linarith only [hdelta1, ht012a, ht023b, ht234b, hbg2c, hbg0c]
                      ·
                        linarith only [hdelta1, ht012c, ht123a, hbg2c]
                    ·
                      have hb3 := m.budget 3 (by decide) 0 1 4 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc30, hc31, hc32] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht023e, ht134a, ht234a, hbg3]
                      ·
                        linarith only [hdelta1, h010, h231, ht013a, ht234a, hbg3]
                      ·
                        linarith only [hdelta1, ht023e, ht034a, hbg3]
                      ·
                        linarith only [hdelta1, ht013c, ht134a, ht234a, hbg3]
                      ·
                        linarith only [hdelta1, h030, h231, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, ht023e, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht134a, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, h010, h231, ht013a, hbg3c]
                      ·
                        linarith only [hdelta1, ht013c, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, hbg3c]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht123c, ht134a, ht234a]
                    ·
                      have hb3 := m.budget 3 (by decide) 0 4 1 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc30, hc31, hc32] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht013e, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht023e, ht034a, ht123c, hbg3]
                      ·
                        linarith only [hdelta1, ht023e, ht034a, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht034a, ht123c, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht023e, ht123c, hbg3c]
                      ·
                        linarith only [hdelta1, ht023e, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht123c, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht023e, ht034a, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht123c, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht134a, hbg3c]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht123b, ht124c, ht134b]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht123c, ht134a, ht234a]
                    ·
                      have hb2 := m.budget 2 (by decide) 0 4 1 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h010, h231, ht012b, ht123a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, h010, h231, ht012b, ht024a, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, ht023e, ht034a, ht124a, hbg2, ht234b]
                      ·
                        linarith only [hdelta1, ht023b, ht034a, ht123a, ht124a, hbg2, ht234b]
                      ·
                        linarith only [hdelta1, h010, h231, ht012b, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, h010, h231, ht012b, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht123a, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, h030, h231, ht034a, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, ht023b, ht034a, ht123a, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, ht023b, ht034a, ht124a, ht234b, hbg2c]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 0 3 1 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h010, h241, ht012b, ht123a, hbg2, ht124a]
                      ·
                        linarith only [hdelta1, h010, h341, ht012b, ht023a, ht234c, hbg2, ht124a]
                      ·
                        linarith only [hdelta1, h010, h341, ht012b, ht023a, ht123a, ht234c, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht123a, hbg2, ht124a]
                      ·
                        linarith only [hdelta1, h010, h341, ht012b, ht234c, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, h010, h341, ht012b, ht123a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht123a, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, h010, h341, ht012b, ht023a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht123a, hbg2c]
                    ·
                      linarith only [ht134a, ht123b, ht234a]
                  ·
                    linarith only [ht123c, ht134c, ht124b]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 0 3 4 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, ht012e, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, ht012e, ht023a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht012e, ht024a, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, ht012e, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012e, hbg2c, ht234b]
                      ·
                        linarith only [hdelta1, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012e, ht023a, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, hbg2c]
                    ·
                      linarith only [ht134a, ht123b, ht234a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 0 3 4 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, ht012e, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, ht012e, ht023a, ht134a, ht123c, ht234c, hbg2]
                      ·
                        linarith only [hdelta1, ht012e, ht024a, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht134a, ht123c, hbg2, ht234a]
                      ·
                        linarith only [hdelta1, ht012e, ht134a, ht123c, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht012e, hbg2c, ht234b]
                      ·
                        linarith only [hdelta1, ht134a, ht123c, ht234a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012e, ht023a, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht134a, ht123c, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, hbg2c]
                    ·
                      have hb2 := m.budget 2 (by decide) 0 4 3 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, ht012e, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht012e, ht024a, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, ht012e, ht023b, ht034a, hbg2, ht234a]
                      ·
                        linarith only [hdelta1, ht023b, ht034a, ht123a, hbg2, ht234a]
                      ·
                        linarith only [hdelta1, ht012e, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012e, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht123a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, h010, h121, ht012b, ht023b, ht034a, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, ht023b, ht034a, ht123a, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, hbg2c]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht034a, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht013c, ht034a, ht123c, ht234a]
                    ·
                      have hb2 := m.budget 2 (by decide) 0 1 4 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc30, hc31, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, ht012b, ht013d, ht124a, ht234d, hbg3, hbg2]
                        ·
                          linarith only [hdelta1, h010, h231, ht012b, ht034a, ht123c, ht124a, ht234d, hbg3, hbg2]
                        ·
                          linarith only [hdelta1, h010, h231, ht012b, ht013c, ht034a, ht124a, ht234d, hbg3, hbg2]
                        ·
                          linarith only [hdelta1, ht012b, ht013d, ht034a, ht123a, hbg3, hbg2]
                        ·
                          linarith only [hdelta1, h010, h231, ht012b, ht123c, ht124a, ht234d, hbg3c, hbg2]
                        ·
                          linarith only [hdelta1, h010, h231, ht012b, ht123b, hbg3b, hbg2]
                        ·
                          linarith only [hdelta1, ht012b, ht013d, ht124a, ht234c, hbg3c, hbg2]
                        ·
                          linarith only [hdelta1, h010, h231, ht012b, ht123b, hbg3b, hbg2]
                        ·
                          linarith only [hdelta1, h010, h131, ht012b, ht034a, ht124a, ht234c, hbg3c, hbg2]
                        ·
                          linarith only [hdelta1, h010, h231, ht012b, ht123b, hbg3a, hbg2]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc30, hc31, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, ht012a, ht013d, ht234d, hbg3, hbg2]
                        ·
                          linarith only [hdelta1, h010, ht012a, h131, ht034a, ht234d, hbg3, hbg2]
                        ·
                          linarith only [hdelta1, h010, ht012a, h231, ht013c, ht034a, ht234d, hbg3, hbg2]
                        ·
                          linarith only [hdelta1, ht012a, ht013d, ht034a, ht234c, hbg3, hbg2]
                        ·
                          linarith only [hdelta1, h010, ht012a, h231, ht123c, ht234d, hbg3c, hbg2]
                        ·
                          linarith only [hdelta1, h010, ht012a, h231, ht013c, ht234d, hbg3c, hbg2]
                        ·
                          linarith only [hdelta1, ht012a, ht013d, ht234c, hbg3c, hbg2]
                        ·
                          linarith only [hdelta1, ht023e, hbg3c]
                        ·
                          linarith only [hdelta1, h010, ht012a, h131, ht034a, ht234c, hbg3c, hbg2]
                        ·
                          linarith only [hdelta1, ht013c, ht034a, hbg3c]
                      ·
                        linarith only [hdelta1, h010, ht012a, h231, ht124a, hbg2]
                      ·
                        have hb0 := m.budget 0 (by decide) 1 2 4 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                        ·
                          have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc31, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht013d, ht024a, ht234d, hbg0, hbg3]
                          ·
                            linarith only [hn, hdelta1, h010, h231, ht023b, ht123c, hbg0, hbg3]
                          ·
                            linarith only [hn, hdelta1, h010, h231, ht013c, ht034c, hbg0, ht024b, hbg3]
                          ·
                            linarith only [hdelta1, ht013d, ht023a, ht034a, hbg0, hbg3]
                          ·
                            linarith only [hdelta1, h010, h131, ht023b, hbg0, hbg3b]
                          ·
                            linarith only [hdelta1, h010, h231, ht013c, ht034c, hbg0, ht024b, hbg3b]
                          ·
                            linarith only [hdelta1, ht012c, ht013d, ht124a, ht234c, hbg0, hbg3c]
                          ·
                            linarith only [hdelta1, h010, h131, ht023b, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, h010, h131, ht023b, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, h010, h231, ht013c, ht034c, hbg0, ht024b, hbg3a]
                        ·
                          linarith only [hn, hdelta1, ht023c, ht034c, hbg0, hbg2]
                        ·
                          linarith only [hn, hdelta1, ht013c, ht123c, hbg0, ht024b, hbg2]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc31, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012a, ht124a, ht234d, hbg0, hbg3]
                          ·
                            linarith only [hn, hdelta1, ht023b, ht123c, hbg3, hbg2]
                          ·
                            linarith only [hn, hdelta1, ht013c, ht034c, ht024b, hbg3, hbg2]
                          ·
                            linarith only [hdelta1, ht012a, ht034a, ht124a, ht234c, hbg0, hbg3]
                          ·
                            linarith only [hdelta1, ht023b, ht123c, hbg3b, hbg2]
                          ·
                            linarith only [hdelta1, ht013c, ht023b, hbg3b, hbg2]
                          ·
                            linarith only [hdelta1, ht012a, ht124a, ht234c, hbg0, hbg3c]
                          ·
                            linarith only [hdelta1, ht023b, hbg3a, hbg2, hbg3b]
                          ·
                            linarith only [hdelta1, ht034c, ht123c, ht024b, hbg3a, hbg2]
                          ·
                            linarith only [hdelta1, ht013c, ht034c, ht024b, hbg3a, hbg2]
                        ·
                          linarith only [hdelta1, ht023c, ht034c, hbg0b, hbg2]
                        ·
                          linarith only [hdelta1, ht023c, ht024b, hbg0b, hbg2]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc31, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht024a, ht234d, hbg0c, hbg3]
                          ·
                            linarith only [hdelta1, h010, h231, ht023b, ht123c, hbg0a, hbg3]
                          ·
                            linarith only [hdelta1, ht013a, ht034c, ht024b, hbg0b, hbg3, hbg2]
                          ·
                            linarith only [hdelta1, ht012c, ht034a, ht124a, ht234c, hbg0c, hbg3]
                          ·
                            linarith only [hdelta1, ht023b, ht123c, hbg3b, hbg2]
                          ·
                            linarith only [hdelta1, ht013c, ht023b, hbg3b, hbg2]
                          ·
                            linarith only [hdelta1, ht012c, ht124a, ht234c, hbg0c, hbg3c]
                          ·
                            linarith only [hdelta1, ht034c, hbg3b, ht024b, hbg3a, hbg2]
                          ·
                            linarith only [hdelta1, ht034c, ht123c, ht024b, hbg3a, hbg2]
                          ·
                            linarith only [hdelta1, ht013c, ht034c, ht024b, hbg3a, hbg2]
                        ·
                          linarith only [hdelta1, ht023c, hbg0b, hbg0a, hbg2]
                        ·
                          linarith only [hdelta1, ht023c, ht034c, hbg0a, hbg2]
                        ·
                          linarith only [hdelta1, ht023c, ht024b, hbg0a, hbg2]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc30, hc31, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, ht012b, ht013d, ht234d, hbg3, hbg2c]
                        ·
                          linarith only [hdelta1, h010, h131, ht012b, ht034a, ht234d, hbg3, hbg2c]
                        ·
                          linarith only [hdelta1, h010, h231, ht012b, ht013c, ht034a, ht234d, hbg3, hbg2c]
                        ·
                          linarith only [hdelta1, ht012b, ht013d, ht034a, ht234c, hbg3, hbg2c]
                        ·
                          linarith only [hdelta1, h010, h231, ht012b, ht123c, ht234d, hbg2c, hbg3c]
                        ·
                          linarith only [hdelta1, h010, h231, ht012b, ht013c, ht234d, hbg2c, hbg3c]
                        ·
                          linarith only [hdelta1, ht012b, ht013d, ht234c, hbg2c, hbg3c]
                        ·
                          linarith only [hdelta1, ht023e, hbg3c]
                        ·
                          linarith only [hdelta1, ht034a, ht123c, hbg3c]
                        ·
                          linarith only [hdelta1, ht013c, ht034a, hbg3c]
                      ·
                        linarith only [hdelta1, h010, h231, ht012b, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, h010, ht012a, h231, hbg2c]
                      ·
                        have hb0 := m.budget 0 (by decide) 1 2 4 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                        ·
                          linarith only [hdelta1, h010, h231, ht012c, ht234c, hbg2a, hbg0]
                        ·
                          linarith only [hdelta1, ht024c, ht234c, hbg2b, hbg0]
                        ·
                          linarith only [hdelta1, ht023c, ht024b, hbg2b, hbg0]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc31, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012a, h231, h340, ht234c, hbg3, hbg2a, hbg0]
                          ·
                            linarith only [hdelta1, ht034c, ht123c, ht024b, hbg3, hbg2b]
                          ·
                            linarith only [hdelta1, ht013a, ht034c, ht024b, hbg3, hbg2b, hbg0]
                          ·
                            linarith only [hdelta1, ht012a, ht034a, ht234c, hbg3, hbg2a, hbg0]
                          ·
                            linarith only [hdelta1, ht012c, ht123c, ht234d, hbg2c, hbg3c]
                          ·
                            linarith only [hdelta1, ht012c, ht013c, ht234d, hbg2c, hbg3c]
                          ·
                            linarith only [hdelta1, ht012a, ht123a, hbg3c, hbg0]
                          ·
                            linarith only [hdelta1, h010, ht012a, h241, ht034c, ht024b, hbg2c, hbg3c]
                          ·
                            linarith only [hdelta1, ht034a, ht123c, hbg3c]
                          ·
                            linarith only [hdelta1, ht013c, ht034a, hbg3c]
                        ·
                          linarith only [hdelta1, ht013d, ht034c, hbg0c]
                        ·
                          linarith only [hdelta1, ht013d, ht024b, hbg0c]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc31, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h231, h340, ht012c, ht234c, hbg2a, hbg3, hbg0c]
                          ·
                            linarith only [hdelta1, h010, h231, ht023b, ht123c, hbg0a, hbg3]
                          ·
                            linarith only [hdelta1, h010, h231, ht013c, ht034c, ht024b, hbg0a, hbg3]
                          ·
                            linarith only [hdelta1, ht012c, ht034a, ht234c, hbg2a, hbg3, hbg0c]
                          ·
                            linarith only [hdelta1, ht012c, ht123c, ht234d, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht012c, ht013c, ht234d, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht023a, hbg3c, hbg0c]
                          ·
                            linarith only [hdelta1, h010, h231, ht023b, hbg0a, hbg3c]
                          ·
                            linarith only [hdelta1, ht034a, ht123c, hbg3c]
                          ·
                            linarith only [hdelta1, ht013c, ht034a, hbg3c]
                        ·
                          linarith only [hdelta1, h010, ht012a, h031, ht234c, hbg2c, hbg0c]
                        ·
                          linarith only [hdelta1, ht012a, ht034c, ht234c, hbg2c, hbg0c]
                        ·
                          linarith only [hdelta1, ht012a, ht234c, ht024b, hbg2c, hbg0c]
                      ·
                        linarith only [hdelta1, ht012c, ht124a, hbg2c]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht034a, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht023c, ht034a, ht234a]
                    ·
                      have hb2 := m.budget 2 (by decide) 0 4 1 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h010, h231, ht012b, ht123a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, h010, h231, ht012b, ht024a, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, h010, h231, ht012b, ht024a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht024a, ht123a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, h010, h231, ht012b, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, h010, h231, ht012b, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht123a, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, h010, h231, ht012b, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, ht124a, hbg2c]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht023c, ht034a, ht123b, ht134a]
                  ·
                    linarith only [ht124b, ht134c, ht123c]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht034a, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht023c, ht034a, ht234a]
                    ·
                      have hb2 := m.budget 2 (by decide) 0 4 3 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, ht012e, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht012e, ht024a, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, ht012e, ht023a, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, ht012e, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012e, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht123a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht012e, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, hbg2c]
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              linarith only [ht023b, ht024c, ht034b]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  linarith only [ht012c, ht024a, ht124a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht034a, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht023a, ht024c, ht034b, ht234a]
                    ·
                      have hb2 := m.budget 2 (by decide) 4 0 1 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, ht012c, ht123a, ht234e, hbg2]
                      ·
                        linarith only [hdelta1, ht024a, ht123a, ht234e, hbg2]
                      ·
                        linarith only [hdelta1, ht012c, ht024a, ht234e, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, hbg2]
                      ·
                        linarith only [hdelta1, ht123a, ht234e, hbg2c]
                      ·
                        linarith only [hdelta1, ht012c, ht234e, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, hbg2c]
                      ·
                        linarith only [hdelta1, h231, h340, ht024a, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012c, ht024a, hbg2c]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  linarith only [ht012c, ht024a, ht124a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht034a, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht023a, ht024c, ht034b, ht234a]
                    ·
                      have hb2 := m.budget 2 (by decide) 4 0 3 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h121, h340, ht023a, ht123a, ht234b, hbg2]
                      ·
                        linarith only [hdelta1, ht012e, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, h121, h340, ht023a, ht024a, ht234b, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, h121, h340, ht123a, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, h121, h340, ht023a, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012e, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, hbg2c]
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                linarith only [ht012c, ht023a, ht123a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 3 0 1 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, ht012c, ht234d, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht234d, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht012c, ht023a, ht234d, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, hbg2]
                      ·
                        linarith only [hdelta1, h230, h241, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012c, ht234d, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, h230, h241, ht023a, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012c, ht023a, hbg2c]
                    ·
                      linarith only [ht023b, ht034a, ht234a]
                  ·
                    linarith only [ht123c, ht124b, ht134c]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 3 0 4 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h121, h230, ht024a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht012e, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, h121, h230, ht023a, ht024a, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, h121, h230, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, h121, h230, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012e, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, hbg2c]
                    ·
                      linarith only [ht014c, ht023a, ht024b, ht134c, ht234a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 3 0 4 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h121, h230, ht024a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht123d, ht234c, hbg2, ht134a]
                      ·
                        linarith only [hdelta1, h121, h230, ht023a, ht024a, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, ht123c, ht234c, hbg2, ht134a]
                      ·
                        linarith only [hdelta1, ht123d, ht234c, ht134a, hbg2c]
                      ·
                        linarith only [hdelta1, h121, h230, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, ht123c, ht234c, ht134a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012e, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht123c, ht234c, ht134a, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, hbg2c]
                    ·
                      linarith only [ht023b, ht034a, ht234a]
            ·
              linarith only [ht023c, ht024b, ht034c]
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                linarith only [ht012c, ht023a, ht123a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  linarith only [ht012c, ht024a, ht124a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb0 := m.budget 0 (by decide) 1 3 4 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                      ·
                        have hb4 := m.budget 4 (by decide) 2 0 1 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc42, hc40, hc41, hc43] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, ht014d, ht034a, ht234e, hbg0, hbg4]
                        ·
                          linarith only [hn, hdelta1, h010, h141, ht034b, hbg0, hbg4]
                        ·
                          linarith only [hn, hdelta1, h010, h341, ht014c, ht034b, hbg0, hbg4]
                        ·
                          linarith only [hdelta1, ht012d, ht024a, ht034a, hbg0, hbg4]
                        ·
                          linarith only [hdelta1, h010, h141, ht034b, hbg4b, hbg0]
                        ·
                          linarith only [hdelta1, h010, h341, ht014c, ht034b, hbg4b, hbg0]
                        ·
                          linarith only [hdelta1, ht012d, ht013c, ht024c, ht134a, hbg4c, hbg0]
                        ·
                          linarith only [hdelta1, h010, h141, ht034b, hbg4a, hbg0]
                        ·
                          linarith only [hdelta1, h010, h141, ht034b, hbg4a, hbg0]
                        ·
                          linarith only [hdelta1, h010, h341, ht014c, ht034b, hbg4a, hbg0]
                      ·
                        have hb2 := m.budget 2 (by decide) 3 4 0 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc20, hc21] at hb2
                        rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                        ·
                          have hb3 := m.budget 3 (by decide) 2 0 1 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc30, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, h041, h230, hbg0, hbg3]
                          ·
                            linarith only [hdelta1, ht012d, ht013b, ht024a, ht123d, hbg2, hbg3]
                          ·
                            linarith only [hdelta1, h230, h341, ht012d, ht013a, ht024a, hbg2, hbg3]
                          ·
                            linarith only [hdelta1, ht012d, ht013b, ht024a, ht034a, hbg2, hbg3]
                          ·
                            linarith only [hdelta1, h021, h230, ht024c, hbg3a, hbg0]
                          ·
                            linarith only [hdelta1, h021, h230, ht024c, hbg3a, hbg0]
                          ·
                            linarith only [hdelta1, h021, h230, ht024c, hbg3a, hbg0]
                          ·
                            linarith only [hdelta1, h230, h341, ht012d, ht013b, ht024a, hbg3c, hbg2]
                          ·
                            linarith only [hdelta1, ht024b, ht034c, hbg3b, hbg2]
                          ·
                            linarith only [hdelta1, ht012d, ht013b, ht014c, ht024a, ht134c, hbg3b, hbg0, hbg2]
                        ·
                          have hb3 := m.budget 3 (by decide) 2 0 1 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc30, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, h041, h230, hbg3, hbg0]
                          ·
                            linarith only [hdelta1, ht012d, ht013b, ht134a, ht234e, hbg3, hbg2]
                          ·
                            linarith only [hdelta1, ht012d, ht013a, ht234e, hbg3, hbg2]
                          ·
                            linarith only [hn, hdelta1, ht023b, ht034c, hbg3, hbg0]
                          ·
                            linarith only [hdelta1, h121, h230, ht012c, ht024c, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, h121, h230, ht012c, ht024c, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, h121, h230, ht012c, ht024c, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, ht012d, ht013b, ht234e, hbg2, hbg3c]
                          ·
                            linarith only [hdelta1, ht023b, ht034c, hbg0, hbg3b]
                          ·
                            linarith only [hdelta1, ht014c, ht023b, ht134c, hbg0, hbg3b]
                        ·
                          linarith only [hn, hdelta1, h010, h121, ht013b, ht024c, hbg0, hbg2]
                        ·
                          linarith only [hn, hdelta1, ht012c, ht023b, ht024c, hbg0, hbg2]
                        ·
                          have hb3 := m.budget 3 (by decide) 2 0 1 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc30, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, h041, h230, hbg3, hbg0]
                          ·
                            linarith only [hdelta1, h230, h341, ht012d, ht013b, ht134a, hbg3, hbg2c]
                          ·
                            linarith only [hdelta1, h230, h341, ht012d, ht013a, hbg3, hbg2c]
                          ·
                            linarith only [hdelta1, ht012d, ht013b, ht034a, hbg3, hbg2c]
                          ·
                            linarith only [hdelta1, h021, h230, ht024c, hbg3a, hbg0]
                          ·
                            linarith only [hdelta1, h021, h230, ht024c, hbg3a, hbg0]
                          ·
                            linarith only [hdelta1, h021, h230, ht024c, hbg3a, hbg0]
                          ·
                            linarith only [hdelta1, h230, h341, ht012d, ht013b, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht012d, ht013b, ht014c, ht134c, hbg0, hbg3b, hbg2c]
                          ·
                            linarith only [hdelta1, ht012d, ht013b, ht014c, ht134c, hbg0, hbg3b, hbg2c]
                        ·
                          linarith only [hdelta1, h010, h121, ht013b, ht024c, hbg2b, hbg0]
                        ·
                          linarith only [hdelta1, ht012c, ht023b, ht024c, hbg2b, hbg0]
                        ·
                          linarith only [hdelta1, h010, h121, ht013b, ht024c, hbg2b, hbg0]
                        ·
                          linarith only [hdelta1, ht012c, ht023b, ht024c, hbg2b, hbg0]
                        ·
                          linarith only [hdelta1, h010, h121, ht013b, ht024c, hbg0, hbg2a]
                      ·
                        have hb3 := m.budget 3 (by decide) 2 0 1 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc30, hc31] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hn, hdelta1, h121, h230, ht012c, ht034b, hbg3, hbg0]
                        ·
                          linarith only [hdelta1, ht012d, ht013b, ht034e, ht134a, hbg3, hbg0]
                        ·
                          linarith only [hdelta1, ht012d, ht013a, ht024b, ht234e, hbg3, hbg0]
                        ·
                          linarith only [hdelta1, ht012d, ht013a, ht023b, ht034b, ht134a, hbg3, hbg0]
                        ·
                          linarith only [hdelta1, h121, h230, ht012c, ht034b, hbg0, hbg3a]
                        ·
                          linarith only [hdelta1, h121, h230, ht012c, ht034b, hbg0, hbg3a]
                        ·
                          linarith only [hdelta1, h121, h230, ht012c, ht034b, hbg0, hbg3a]
                        ·
                          linarith only [hdelta1, ht012d, ht013b, ht024b, ht234e, hbg0, hbg3c]
                        ·
                          linarith only [hdelta1, ht023b, ht134a, hbg3c]
                        ·
                          linarith only [hdelta1, ht012d, ht013a, ht023b, ht034b, hbg0, hbg3c]
                      ·
                        have hb3 := m.budget 3 (by decide) 2 0 1 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc30, hc31] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          have hb2 := m.budget 2 (by decide) 3 4 0 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc20, hc21] at hb2
                          rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                          ·
                            linarith only [hdelta1, ht013a, ht024a, ht123d, hbg2, hbg0]
                          ·
                            linarith only [hdelta1, ht013a, ht134a, hbg2, ht234e, hbg0]
                          ·
                            linarith only [hn, hdelta1, h121, h230, ht024c, ht034b, hbg2, hbg3]
                          ·
                            linarith only [hn, hdelta1, ht012c, ht024c, ht034b, hbg2, hbg3]
                          ·
                            linarith only [hdelta1, h230, h341, ht013a, ht134a, hbg0, hbg2c]
                          ·
                            linarith only [hdelta1, h121, h230, ht023c, hbg3, hbg2b]
                          ·
                            linarith only [hdelta1, ht012a, ht024c, ht034b, hbg3, hbg0, hbg2b]
                          ·
                            linarith only [hdelta1, h121, h230, ht024c, ht034b, hbg3, hbg2b]
                          ·
                            linarith only [hdelta1, ht012a, ht024c, ht034b, hbg3, hbg0, hbg2b]
                          ·
                            linarith only [hdelta1, h121, h230, ht024c, ht034b, hbg2a, hbg3]
                        ·
                          linarith only [hdelta1, ht013b, ht024a, ht134a, ht234e, hbg3, hbg0]
                        ·
                          linarith only [hdelta1, ht013a, ht024a, ht234e, hbg3, hbg0]
                        ·
                          linarith only [hdelta1, ht013a, ht023a, ht134a, hbg3, hbg0]
                        ·
                          linarith only [hdelta1, h230, h341, ht134a, hbg3c]
                        ·
                          have hb2 := m.budget 2 (by decide) 3 4 0 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc20, hc21] at hb2
                          rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                          ·
                            linarith only [hdelta1, h230, h341, ht013a, ht024a, hbg3b, hbg0, hbg2]
                          ·
                            linarith only [hdelta1, h240, h341, ht013a, hbg3b, hbg0, hbg2]
                          ·
                            linarith only [hdelta1, h121, h230, ht023c, hbg3a, hbg2]
                          ·
                            linarith only [hdelta1, ht012c, ht024c, ht034b, hbg3a, hbg2]
                          ·
                            linarith only [hdelta1, h230, h341, ht013a, hbg3b, hbg0, hbg2c]
                          ·
                            linarith only [hdelta1, h121, h230, ht024a, hbg2c]
                          ·
                            linarith only [hdelta1, ht012a, ht024a, hbg0, hbg2c]
                          ·
                            linarith only [hdelta1, h121, h230, ht013c, ht234e, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht012c, ht013c, ht234e, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht023a, hbg2c]
                        ·
                          linarith only [hdelta1, ht034a, hbg3c]
                        ·
                          linarith only [hdelta1, ht013b, ht024a, ht234e, hbg3c, hbg0]
                        ·
                          linarith only [hdelta1, ht023b, ht134a, hbg3c]
                        ·
                          linarith only [hdelta1, ht013a, ht023a, hbg3c, hbg0]
                      ·
                        linarith only [hdelta1, ht012d, ht024c, hbg0c]
                      ·
                        linarith only [hdelta1, ht012d, ht034b, hbg0c]
                      ·
                        have hb4 := m.budget 4 (by decide) 2 0 1 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc42, hc40, hc41, hc43] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, ht013c, ht024c, ht134a, ht234e, hbg4, hbg0c]
                        ·
                          linarith only [hdelta1, h010, h141, ht034b, hbg4, hbg0a]
                        ·
                          linarith only [hdelta1, h010, h341, ht014c, ht034b, hbg4, hbg0a]
                        ·
                          linarith only [hdelta1, ht013c, ht024a, ht134a, hbg4, hbg0c]
                        ·
                          linarith only [hdelta1, ht134c, ht234e, hbg4c]
                        ·
                          linarith only [hdelta1, ht014c, ht234e, hbg4c]
                        ·
                          linarith only [hdelta1, ht013c, ht024c, ht134a, hbg0c, hbg4c]
                        ·
                          linarith only [hdelta1, h010, h341, ht034b, hbg0a, hbg4c]
                        ·
                          linarith only [hdelta1, ht024a, ht034b, ht134c, hbg0c, hbg4c]
                        ·
                          linarith only [hdelta1, ht014c, ht024a, ht034b, hbg0c, hbg4c]
                      ·
                        linarith only [hdelta1, ht012d, ht013b, hbg0c]
                      ·
                        have hb3 := m.budget 3 (by decide) 2 0 1 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc30, hc31] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h041, h230, hbg3, hbg0a]
                        ·
                          have hb2 := m.budget 2 (by decide) 3 4 0 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc20, hc21] at hb2
                          rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                          ·
                            linarith only [hdelta1, h131, h230, ht013b, ht024a, hbg2, hbg3, hbg0b]
                          ·
                            linarith only [hdelta1, h240, h341, ht013b, ht134a, hbg2, hbg3, hbg0b]
                          ·
                            linarith only [hdelta1, h010, h121, ht013b, ht024c, hbg2, hbg0a]
                          ·
                            linarith only [hdelta1, ht012c, ht023b, ht024c, hbg2, hbg0a]
                          ·
                            linarith only [hdelta1, h230, h341, ht013b, ht134a, hbg3, hbg0b, hbg2c]
                          ·
                            linarith only [hdelta1, h121, h230, ht024a, hbg2c]
                          ·
                            linarith only [hdelta1, ht023b, ht123c, hbg3, hbg2b]
                          ·
                            linarith only [hdelta1, h010, h121, ht013b, ht134a, hbg3, ht234e, hbg2c]
                          ·
                            linarith only [hdelta1, ht023b, ht123c, hbg3, hbg2b]
                          ·
                            linarith only [hdelta1, ht023b, ht123c, hbg3, hbg2b]
                        ·
                          have hb4 := m.budget 4 (by decide) 2 0 1 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc42, hc40, hc41, hc43] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h240, h341, ht013a, ht024c, hbg3, hbg0b, hbg4]
                          ·
                            linarith only [hdelta1, h030, h141, hbg0a, hbg4]
                          ·
                            linarith only [hdelta1, h010, h341, ht013b, ht014c, hbg0a, hbg4]
                          ·
                            linarith only [hdelta1, ht013a, ht024a, hbg3, hbg0b, hbg4]
                          ·
                            linarith only [hdelta1, ht134c, ht234e, hbg4c]
                          ·
                            linarith only [hdelta1, ht014c, ht234e, hbg4c]
                          ·
                            linarith only [hdelta1, ht013a, ht014d, hbg3, hbg4c]
                          ·
                            linarith only [hdelta1, h230, h341, ht013b, ht023a, hbg0c, hbg4c]
                          ·
                            linarith only [hdelta1, ht013b, ht024a, ht134c, hbg0c, hbg4c]
                          ·
                            linarith only [hdelta1, ht013b, ht014c, ht024a, hbg0c, hbg4c]
                        ·
                          linarith only [hdelta1, ht023b, ht034c, hbg3, hbg0a]
                        ·
                          linarith only [hdelta1, h230, h341, ht134a, hbg3c]
                        ·
                          linarith only [hdelta1, h230, h341, ht013a, ht024c, hbg3c, hbg0c]
                        ·
                          linarith only [hdelta1, ht014c, ht134c, hbg3c, hbg0a]
                        ·
                          have hb2 := m.budget 2 (by decide) 3 4 0 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc20, hc21] at hb2
                          rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                          ·
                            linarith only [hdelta1, h230, h341, ht013b, ht024a, hbg0b, hbg3c, hbg2]
                          ·
                            linarith only [hdelta1, h240, h341, ht013b, hbg0b, hbg3c, hbg2]
                          ·
                            linarith only [hdelta1, h030, h121, ht024a, ht234e, hbg3c, hbg2]
                          ·
                            linarith only [hdelta1, ht012c, ht023b, ht024a, ht234e, hbg3c, hbg2]
                          ·
                            linarith only [hdelta1, h230, h341, ht013b, hbg0b, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, h121, h230, ht024a, hbg2c]
                          ·
                            linarith only [hdelta1, ht012c, ht024a, hbg2c]
                          ·
                            linarith only [hdelta1, h010, h121, ht013b, ht234e, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht012c, ht023b, ht234e, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht023a, hbg2c]
                        ·
                          linarith only [hdelta1, ht023b, ht134a, hbg3c]
                        ·
                          linarith only [hdelta1, ht013a, ht023b, ht024c, hbg0c, hbg3c]
                      ·
                        have hb3 := m.budget 3 (by decide) 2 0 1 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc30, hc31] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h121, h230, ht012c, ht034b, hbg0a, hbg3]
                        ·
                          linarith only [hdelta1, ht013b, ht034e, ht134a, hbg3, hbg0c]
                        ·
                          linarith only [hdelta1, ht013a, ht024b, ht234e, hbg3, hbg0c]
                        ·
                          linarith only [hdelta1, ht013a, ht023b, ht034b, ht134a, hbg3, hbg0c]
                        ·
                          linarith only [hdelta1, h230, h341, ht134a, hbg3c]
                        ·
                          linarith only [hdelta1, h230, h341, ht013a, ht034b, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, ht034a, hbg3c]
                        ·
                          linarith only [hdelta1, ht013b, ht024b, ht234e, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, ht023b, ht134a, hbg3c]
                        ·
                          linarith only [hdelta1, ht013a, ht023b, ht034b, hbg0c, hbg3c]
                    ·
                      linarith only [ht023b, ht034a, ht234a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb3 := m.budget 3 (by decide) 2 0 4 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc32, hc30, hc31] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht034a, ht123d, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht013e, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht023b, ht034a, ht123d, hbg3]
                      ·
                        linarith only [hdelta1, ht023b, ht034a, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht123d, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht123d, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht013e, hbg3c]
                      ·
                        linarith only [hdelta1, ht023b, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht023b, ht034a, hbg3c]
                    ·
                      linarith only [ht023b, ht034a, ht234a]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                linarith only [ht012c, ht023a, ht123a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  linarith only [ht012c, ht024a, ht124a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht034a, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb3 := m.budget 3 (by decide) 2 4 0 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc32, hc30, hc31] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht013c, ht034a, ht123d, hbg3]
                      ·
                        linarith only [hdelta1, ht013c, ht123d, ht234a, hbg3]
                      ·
                        linarith only [hdelta1, ht034a, ht123d, ht234a, hbg3]
                      ·
                        linarith only [hdelta1, ht013c, ht034a, ht234a, hbg3]
                      ·
                        linarith only [hdelta1, ht013c, ht123d, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht123d, hbg3c]
                      ·
                        linarith only [hdelta1, ht013c, ht034a, hbg3c]
                      ·
                        linarith only [hdelta1, ht123d, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, ht013c, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht234a, hbg3c]
                    ·
                      have hb2 := m.budget 2 (by decide) 4 3 0 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        have hb3 := m.budget 3 (by decide) 4 2 0 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc30, hc31] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          have hb0 := m.budget 0 (by decide) 1 4 3 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                          ·
                            linarith only [hdelta1, ht012d, ht023a, ht024d, hbg2, hbg0]
                          ·
                            have hb4 := m.budget 4 (by decide) 3 2 0 1 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc43, hc42, hc40, hc41] at hb4
                            rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                            ·
                              linarith only [hn, hdelta1, h121, h340, ht012c, ht023a, hbg2, hbg4]
                            ·
                              linarith only [hn, hdelta1, h121, h240, ht012c, ht023c, hbg0, hbg4]
                            ·
                              linarith only [hdelta1, ht012d, ht014b, ht023a, ht234b, ht134d, hbg2, hbg4]
                            ·
                              linarith only [hdelta1, ht012d, ht014a, ht023a, ht234b, hbg2, hbg4]
                            ·
                              linarith only [hdelta1, h121, h340, ht012c, ht023a, hbg4a, hbg2]
                            ·
                              linarith only [hdelta1, h121, h340, ht012c, ht023a, hbg4a, hbg2]
                            ·
                              linarith only [hdelta1, h121, h340, ht012c, ht023a, hbg4a, hbg2]
                            ·
                              linarith only [hdelta1, h021, h340, ht023c, ht234b, hbg4a, hbg0]
                            ·
                              linarith only [hdelta1, h021, h340, ht023c, ht234b, hbg4a, hbg0]
                            ·
                              linarith only [hdelta1, ht012d, ht014b, ht023a, ht234b, hbg2, hbg4c]
                          ·
                            linarith only [hn, hdelta1, h021, h340, ht023b, ht234b, hbg2, hbg0]
                          ·
                            linarith only [hdelta1, ht014a, ht023a, ht234b, ht134d, hbg2, hbg0]
                          ·
                            linarith only [hdelta1, ht012d, ht023c, hbg0c]
                          ·
                            linarith only [hdelta1, h121, h340, ht012c, ht023b, ht234b, hbg2, hbg0b]
                          ·
                            linarith only [hdelta1, ht023a, ht024d, hbg2, hbg0c]
                          ·
                            linarith only [hdelta1, h121, h240, ht012c, ht023b, hbg2, hbg0b]
                          ·
                            have hb4 := m.budget 4 (by decide) 3 2 0 1 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc43, hc42, hc40, hc41] at hb4
                            rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                            ·
                              linarith only [hn, hdelta1, h121, h340, ht012c, ht023a, hbg2, hbg4]
                            ·
                              linarith only [hdelta1, h121, h240, ht012c, ht023c, hbg4, hbg0a]
                            ·
                              linarith only [hdelta1, ht014b, ht023a, ht234b, ht134d, hbg2, hbg0b, hbg4]
                            ·
                              linarith only [hdelta1, ht014a, ht023a, ht234b, hbg2, hbg0b, hbg4]
                            ·
                              linarith only [hdelta1, h121, h340, ht012c, ht023a, hbg2, hbg4a]
                            ·
                              linarith only [hdelta1, h121, h340, ht012c, ht023a, hbg2, hbg4a]
                            ·
                              linarith only [hdelta1, h121, h340, ht012c, ht023a, hbg2, hbg4a]
                            ·
                              linarith only [hdelta1, ht234b, ht134d, hbg4c]
                            ·
                              linarith only [hdelta1, ht014a, ht023c, ht234b, hbg0c, hbg4c]
                            ·
                              linarith only [hdelta1, ht014b, ht023a, ht234b, hbg2, hbg0b, hbg4c]
                          ·
                            linarith only [hdelta1, h021, h340, ht023b, ht234b, hbg2, hbg0a]
                        ·
                          linarith only [hn, hdelta1, h031, h340, ht234b, hbg2, hbg3]
                        ·
                          linarith only [hn, hdelta1, h121, h340, ht023b, ht234b, ht123c, hbg2, hbg3]
                        ·
                          linarith only [hn, hdelta1, ht013c, ht023b, ht234b, hbg2, hbg3]
                        ·
                          linarith only [hdelta1, h031, h340, ht234b, hbg2, hbg3b]
                        ·
                          linarith only [hdelta1, h131, h340, ht023b, ht234b, hbg2, hbg3b]
                        ·
                          linarith only [hdelta1, ht013c, ht023b, ht234b, hbg2, hbg3b]
                        ·
                          linarith only [hdelta1, h031, h340, ht234b, hbg2, hbg3a]
                        ·
                          linarith only [hdelta1, h031, h340, ht234b, hbg2, hbg3a]
                        ·
                          linarith only [hdelta1, h131, h340, ht023b, ht234b, hbg2, hbg3a]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 2 0 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc30, hc31] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hn, hdelta1, h021, h340, hbg2, hbg3]
                        ·
                          have hb0 := m.budget 0 (by decide) 1 4 3 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                          ·
                            linarith only [hdelta1, ht012d, ht023c, ht034d, hbg3, ht234a, hbg0]
                          ·
                            have hb4 := m.budget 4 (by decide) 3 2 0 1 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc43, hc42, hc40, hc41] at hb4
                            rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                            ·
                              linarith only [hn, hdelta1, h021, h340, ht023c, ht234c, hbg3, hbg4]
                            ·
                              linarith only [hn, hdelta1, h121, h340, ht012c, ht023c, ht234b, hbg4, hbg0]
                            ·
                              linarith only [hdelta1, ht012d, ht014b, ht023c, ht134d, hbg3, ht234a, hbg4]
                            ·
                              linarith only [hdelta1, ht012d, ht014a, ht023c, hbg3, ht234a, hbg4]
                            ·
                              linarith only [hdelta1, h121, h340, ht012c, ht023c, ht234c, hbg3, hbg4a]
                            ·
                              linarith only [hdelta1, h121, h340, ht012c, ht023c, ht234c, hbg3, hbg4a]
                            ·
                              linarith only [hdelta1, h121, h340, ht012c, ht023c, ht234c, hbg3, hbg4a]
                            ·
                              linarith only [hdelta1, h121, h240, ht012c, ht023c, hbg4a, hbg0]
                            ·
                              linarith only [hdelta1, h121, h240, ht012c, ht023c, hbg4a, hbg0]
                            ·
                              linarith only [hdelta1, ht012d, ht014b, hbg4c, hbg2, ht234a]
                          ·
                            linarith only [hn, hdelta1, h021, h340, hbg3, ht234a, hbg0]
                          ·
                            linarith only [hdelta1, ht014a, ht023c, ht134d, hbg3, ht234a, hbg0]
                          ·
                            linarith only [hdelta1, ht012d, ht023c, hbg0c]
                          ·
                            linarith only [hdelta1, h021, h340, hbg3, ht234a, hbg0b]
                          ·
                            linarith only [hdelta1, ht014c, ht134d, hbg2, ht234a, hbg0c]
                          ·
                            linarith only [hdelta1, h121, h230, ht012c, hbg3, hbg0b]
                          ·
                            have hb4 := m.budget 4 (by decide) 3 2 0 1 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc43, hc42, hc40, hc41] at hb4
                            rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                            ·
                              linarith only [hdelta1, h121, h340, ht012c, ht023c, ht024b, hbg0a, hbg4]
                            ·
                              linarith only [hdelta1, h121, h240, ht012c, ht023c, hbg0a, hbg4]
                            ·
                              linarith only [hdelta1, ht014b, ht023c, ht123d, hbg3, ht134c, hbg4, hbg0b]
                            ·
                              linarith only [hdelta1, ht014a, ht023c, hbg3, ht234a, hbg4, hbg0b]
                            ·
                              linarith only [hdelta1, h121, h340, ht012c, ht234c, hbg2, hbg4a]
                            ·
                              linarith only [hdelta1, h021, h340, ht234c, hbg2, hbg4a]
                            ·
                              linarith only [hdelta1, h021, h340, ht234c, hbg2, hbg4a]
                            ·
                              linarith only [hdelta1, ht124d, hbg4c]
                            ·
                              linarith only [hdelta1, ht014a, ht023c, ht234b, hbg0c, hbg4c]
                            ·
                              linarith only [hdelta1, ht014b, ht023c, hbg3, ht234a, hbg0b, hbg4c]
                          ·
                            linarith only [hdelta1, h021, h340, hbg3, hbg0a, ht234a]
                        ·
                          have hb4 := m.budget 4 (by decide) 3 2 0 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc43, hc42, hc40, hc41] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hn, hdelta1, h121, h340, ht024b, ht034c, ht123c, hbg3, hbg4]
                          ·
                            linarith only [hn, hdelta1, h121, h240, ht034c, ht123c, hbg3, hbg4]
                          ·
                            linarith only [hdelta1, ht012d, ht014b, ht134d, hbg2, ht234a, hbg4]
                          ·
                            linarith only [hdelta1, ht012d, ht014a, hbg2, ht234a, hbg4]
                          ·
                            linarith only [hdelta1, h121, h340, ht034c, ht123c, hbg3, hbg4a, hbg4b]
                          ·
                            linarith only [hdelta1, h121, h340, ht024b, ht034c, ht123c, hbg3, hbg4a]
                          ·
                            linarith only [hdelta1, h121, h340, ht024b, ht034c, ht123c, hbg3, hbg4a]
                          ·
                            linarith only [hdelta1, h121, h240, ht034c, ht123c, hbg3, hbg4a]
                          ·
                            linarith only [hdelta1, h121, h240, ht034c, ht123c, hbg3, hbg4a]
                          ·
                            linarith only [hdelta1, ht012d, ht014b, hbg2, ht234a, hbg4c]
                        ·
                          linarith only [hdelta1, ht012d, ht013a, hbg2, hbg3, ht234a]
                        ·
                          linarith only [hdelta1, h021, h340, hbg2, hbg3a]
                        ·
                          linarith only [hdelta1, h021, h340, hbg2, hbg3a]
                        ·
                          linarith only [hdelta1, h021, h340, hbg2, hbg3a]
                        ·
                          linarith only [hdelta1, h121, h340, ht123c, ht234a, hbg3c]
                        ·
                          linarith only [hdelta1, ht013c, ht234a, hbg3c]
                        ·
                          linarith only [hdelta1, ht023b, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, h121, h340, ht023a, hbg2, ht234a]
                      ·
                        have hb0 := m.budget 0 (by decide) 1 4 3 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                        ·
                          have hb3 := m.budget 3 (by decide) 4 2 0 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc30, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012d, ht023a, ht034d, hbg3, hbg0]
                          ·
                            linarith only [hn, hdelta1, ht012c, ht023c, ht234c, hbg2, hbg3]
                          ·
                            linarith only [hn, hdelta1, ht023b, ht123c, ht234c, hbg2, hbg3]
                          ·
                            linarith only [hdelta1, ht012d, ht013c, ht023a, ht034c, hbg3, ht234a, hbg0]
                          ·
                            linarith only [hdelta1, ht012c, ht023c, ht234c, hbg2, hbg3b]
                          ·
                            linarith only [hdelta1, h010, h131, ht034c, hbg0, hbg3b]
                          ·
                            linarith only [hdelta1, ht012d, ht013c, ht023a, ht034c, hbg3c, hbg0]
                          ·
                            linarith only [hdelta1, h010, h131, ht034c, hbg0, hbg3b]
                          ·
                            linarith only [hdelta1, ht013c, ht123c, ht234c, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, ht012d, ht024a, ht034c, ht123c, hbg2, hbg0, hbg3a]
                        ·
                          linarith only [hn, hdelta1, ht013c, ht024b, ht123c, hbg2, hbg0]
                        ·
                          linarith only [hn, hdelta1, ht012c, ht023b, ht234c, hbg2, hbg0]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 2 0 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc30, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht014a, ht023a, ht134d, hbg0, hbg3]
                          ·
                            linarith only [hn, hdelta1, ht013c, ht123c, ht234c, hbg2, hbg3]
                          ·
                            linarith only [hn, hdelta1, ht013b, ht023a, ht123c, ht234c, hbg2, hbg0, hbg3]
                          ·
                            linarith only [hdelta1, ht013a, ht023a, ht234a, hbg0, hbg3]
                          ·
                            linarith only [hdelta1, ht012a, ht023c, ht234c, hbg2, hbg0, hbg3b]
                          ·
                            linarith only [hdelta1, ht023b, ht123c, ht234c, hbg2, hbg3b]
                          ·
                            linarith only [hdelta1, ht014a, ht023a, hbg3c, ht134c, hbg0]
                          ·
                            linarith only [hdelta1, ht012a, ht023c, ht234c, hbg2, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, ht012a, ht023c, ht234c, hbg2, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, ht014b, ht023a, ht034c, ht123c, ht234c, hbg2, hbg0, hbg3a]
                        ·
                          linarith only [hdelta1, ht013c, ht024b, ht123c, hbg2, hbg0b]
                        ·
                          linarith only [hdelta1, ht012c, ht024b, ht034c, hbg2, hbg0b]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 2 0 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc30, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht023a, ht034d, hbg3, hbg0c]
                          ·
                            linarith only [hn, hdelta1, ht013c, ht123c, ht234c, hbg2, hbg3]
                          ·
                            linarith only [hdelta1, h010, h121, ht034c, ht123c, hbg0a, hbg3]
                          ·
                            linarith only [hdelta1, ht013c, ht023a, ht034c, hbg3, ht234a, hbg0c]
                          ·
                            linarith only [hdelta1, ht012c, ht023c, ht234c, hbg2, hbg3b]
                          ·
                            linarith only [hdelta1, ht023b, ht123c, ht234c, hbg2, hbg3b]
                          ·
                            linarith only [hdelta1, ht013c, ht023a, ht034c, hbg0c, hbg3c]
                          ·
                            linarith only [hdelta1, ht012c, ht023c, ht234c, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, ht012c, ht023c, ht234c, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, ht023b, ht123c, ht234c, hbg2, hbg3a]
                        ·
                          linarith only [hdelta1, ht012c, ht023b, ht234c, hbg2, hbg0b]
                        ·
                          linarith only [hdelta1, ht013c, ht024b, ht123c, hbg2, hbg0a]
                        ·
                          linarith only [hdelta1, ht012c, ht023b, ht234c, hbg2, hbg0a]
                      ·
                        have hb4 := m.budget 4 (by decide) 3 2 0 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc43, hc42, hc40, hc41] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, h121, h340, ht012c, hbg2a, hbg4, hbg2b]
                        ·
                          have hb0 := m.budget 0 (by decide) 1 4 3 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                          ·
                            linarith only [hdelta1, ht012d, ht014c, ht234b, ht134d, hbg0, hbg2c]
                          ·
                            linarith only [hn, hdelta1, h021, h340, ht023c, ht234b, hbg0, hbg4]
                          ·
                            linarith only [hdelta1, h121, h340, ht012c, ht023b, ht234b, hbg2a, hbg0]
                          ·
                            linarith only [hdelta1, ht014a, ht234b, ht134d, hbg0, hbg2c]
                          ·
                            linarith only [hdelta1, h031, h340, ht234b, hbg4, hbg0b]
                          ·
                            linarith only [hdelta1, h121, h240, ht012c, ht034c, hbg4, hbg0b]
                          ·
                            linarith only [hdelta1, ht014c, ht234b, ht134d, hbg0c, hbg2c]
                          ·
                            linarith only [hdelta1, h021, h340, ht234b, hbg0b, hbg4, hbg0a]
                          ·
                            linarith only [hdelta1, h031, h340, ht234b, hbg4, hbg0a]
                          ·
                            linarith only [hdelta1, h121, h340, ht012c, ht034c, ht234b, hbg4, hbg0a]
                        ·
                          linarith only [hdelta1, ht012d, ht014b, ht234b, ht134d, hbg4, hbg2c]
                        ·
                          linarith only [hdelta1, ht012d, ht014a, ht234b, hbg4, hbg2c]
                        ·
                          linarith only [hdelta1, h021, h340, hbg4a, hbg2c]
                        ·
                          linarith only [hdelta1, h021, h340, hbg4a, hbg2c]
                        ·
                          linarith only [hdelta1, h021, h340, hbg4a, hbg2c]
                        ·
                          linarith only [hdelta1, ht124d, hbg4c]
                        ·
                          have hb0 := m.budget 0 (by decide) 1 4 3 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                          ·
                            linarith only [hdelta1, ht012d, ht014c, ht234b, hbg4b, hbg0, hbg2c]
                          ·
                            linarith only [hdelta1, h031, h340, ht234b, hbg4a, hbg0]
                          ·
                            linarith only [hdelta1, h121, h340, ht012c, ht023b, ht234b, hbg2a, hbg0]
                          ·
                            linarith only [hdelta1, ht014a, ht234b, hbg4b, hbg0, hbg2c]
                          ·
                            linarith only [hdelta1, ht012d, ht023c, hbg0c]
                          ·
                            linarith only [hdelta1, ht012d, ht034c, hbg0c]
                          ·
                            linarith only [hdelta1, ht024d, hbg2c, hbg0c]
                          ·
                            linarith only [hdelta1, ht012d, ht014b, hbg0c]
                          ·
                            linarith only [hdelta1, ht014a, ht023c, ht234b, hbg4c, hbg0c]
                          ·
                            linarith only [hdelta1, ht014a, ht034c, ht234b, hbg4c, hbg0c]
                        ·
                          linarith only [hdelta1, ht012d, ht014b, ht234b, hbg4c, hbg2c]
                      ·
                        linarith only [hdelta1, h121, h340, ht023a, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, ht012c, ht023a, hbg2c]
                      ·
                        linarith only [hdelta1, h121, h340, ht234a, hbg2c]
                      ·
                        have hb4 := m.budget 4 (by decide) 3 2 0 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc43, hc42, hc40, hc41] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, h121, h340, ht012c, ht234c, hbg4, hbg2a]
                        ·
                          linarith only [hdelta1, ht012c, ht024c, hbg2b, hbg4]
                        ·
                          linarith only [hdelta1, ht024b, ht123c, hbg2b, hbg4, ht134c]
                        ·
                          have hb0 := m.budget 0 (by decide) 1 4 3 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                          ·
                            linarith only [hdelta1, ht012d, ht014c, ht234a, hbg4, hbg0, hbg2a]
                          ·
                            linarith only [hdelta1, ht013c, ht024b, ht123c, hbg2b, hbg0]
                          ·
                            linarith only [hdelta1, ht012c, ht023b, ht234c, hbg2b, hbg0]
                          ·
                            linarith only [hdelta1, ht014a, ht234a, hbg4, hbg0, hbg2a]
                          ·
                            linarith only [hdelta1, ht012d, ht023c, hbg0c]
                          ·
                            linarith only [hdelta1, ht012d, ht014c, ht023b, ht234a, hbg4, hbg0c]
                          ·
                            linarith only [hdelta1, ht014c, ht234a, hbg4, hbg0c, hbg2a]
                          ·
                            linarith only [hdelta1, ht012d, ht014b, hbg0c]
                          ·
                            have hb3 := m.budget 3 (by decide) 4 2 0 1 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc32, hc30, hc31] at hb3
                            rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                              ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                              ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                            ·
                              linarith only [hdelta1, ht014a, hbg0b, hbg4, hbg3, hbg2a]
                            ·
                              linarith only [hdelta1, ht014a, ht023c, hbg0b, ht234a, hbg4, hbg3]
                            ·
                              linarith only [hdelta1, ht014a, ht024b, ht123c, hbg0b, ht234a, hbg4, hbg3, hbg0c, hbg2a, hbg2c]
                            ·
                              linarith only [hdelta1, ht012c, ht013c, ht014a, ht024b, ht234a, hbg4, hbg3, hbg0c, hbg2a, hbg2c]
                            ·
                              linarith only [hdelta1, ht012c, ht014c, ht024b, hbg3a, hbg4, hbg2c]
                            ·
                              linarith only [hdelta1, ht012c, ht014c, ht024b, hbg3a, hbg4, hbg2c]
                            ·
                              linarith only [hdelta1, ht012c, ht014c, ht024b, hbg3a, hbg4, hbg2c]
                            ·
                              linarith only [hdelta1, ht014a, ht024b, ht123c, ht234a, hbg4, hbg3b, hbg0c, hbg2c]
                            ·
                              linarith only [hdelta1, ht013c, ht234a, hbg3c]
                            ·
                              linarith only [hdelta1, ht014a, ht024b, ht123c, ht234a, hbg4, hbg3a, hbg0c, hbg2c]
                          ·
                            linarith only [hdelta1, ht014a, ht023b, ht234a, hbg4, hbg0c]
                        ·
                          linarith only [hdelta1, ht014c, ht134d, hbg4c]
                        ·
                          linarith only [hdelta1, ht024b, ht134d, hbg4c]
                        ·
                          have hb0 := m.budget 0 (by decide) 1 4 3 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                          ·
                            linarith only [hdelta1, ht012d, ht014c, ht234c, hbg4c, hbg0, hbg2a]
                          ·
                            linarith only [hdelta1, h021, h340, ht023c, ht024b, hbg0, hbg4a]
                          ·
                            linarith only [hdelta1, h121, h340, ht012c, ht023b, ht234c, hbg0, hbg4a]
                          ·
                            linarith only [hdelta1, ht014a, ht234c, hbg4c, hbg0, hbg2a]
                          ·
                            linarith only [hdelta1, ht012d, ht023c, hbg0c]
                          ·
                            linarith only [hdelta1, ht012d, ht034c, hbg0c]
                          ·
                            linarith only [hdelta1, ht014c, ht234c, hbg4c, hbg0c, hbg2a]
                          ·
                            linarith only [hdelta1, h121, h340, ht012c, ht024b, hbg4a, hbg0c]
                          ·
                            linarith only [hdelta1, ht014a, ht023c, ht024b, hbg4c, hbg0c]
                          ·
                            linarith only [hdelta1, ht014a, ht024b, ht034c, hbg4c, hbg0c]
                        ·
                          linarith only [hdelta1, ht012c, ht123d, hbg4c, ht134c, hbg2c]
                        ·
                          linarith only [hdelta1, ht012c, ht014c, ht234a, hbg4c, hbg2c]
                        ·
                          linarith only [hdelta1, ht012c, ht024b, ht234a, hbg4c, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, hbg2c]
      ·
        rcases m.triangle 0 2 3 (by decide) (by decide) with ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩ | ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            linarith only [ht012b, ht014c, ht024b]
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              linarith only [ht012b, ht014c, ht023b, ht034b]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  linarith only [ht012c, ht024a, ht124a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013a, ht014c, ht034b, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht012b, ht014a, ht023a, ht234a, ht134b]
                    ·
                      have hb2 := m.budget 2 (by decide) 4 0 1 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, ht012c, ht123a, ht234e, hbg2]
                      ·
                        linarith only [hdelta1, h140, h231, ht012b, ht014a, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, ht124b, ht234e, hbg2]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, ht123a, ht124b, hbg2]
                      ·
                        linarith only [hdelta1, ht123a, ht234e, hbg2c]
                      ·
                        linarith only [hdelta1, ht012c, ht234e, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, hbg2c]
                      ·
                        linarith only [hdelta1, h140, h231, ht012b, ht014a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012b, ht014a, ht123a, ht124b, hbg2c]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, ht124b, hbg2c]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  linarith only [ht023a, ht024a, ht123a, ht124a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht034a, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht012b, ht014a, ht023a, ht234a, ht134b]
                    ·
                      have hb2 := m.budget 2 (by decide) 4 0 3 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h121, h340, ht023a, ht123a, ht234b, hbg2]
                      ·
                        linarith only [hdelta1, ht012e, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, ht012b, ht014a, ht023a, ht124e, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, h121, h340, ht123a, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, h121, h340, ht023a, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, h121, h140, ht012b, ht014a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012b, ht014a, ht123a, ht124b, hbg2c]
                      ·
                        linarith only [hdelta1, ht013b, ht014a, ht023c, ht124b, hbg2c]
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            linarith only [ht013b, ht014c, ht023c, ht024b]
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              linarith only [ht013b, ht014c, ht034b]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                linarith only [ht012c, ht023a, ht123a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  linarith only [ht013a, ht014c, ht024b, ht124a, ht123c]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht034a, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb3 := m.budget 3 (by decide) 2 4 0 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc32, hc30, hc31] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht013a, ht014a, ht123d, hbg3, ht134b]
                      ·
                        linarith only [hdelta1, ht013c, ht123d, ht234a, hbg3]
                      ·
                        linarith only [hdelta1, ht013b, ht014a, ht123d, ht234a, hbg3, ht134b]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, ht234a, hbg3, ht134b]
                      ·
                        linarith only [hdelta1, ht013c, ht123d, hbg3c]
                      ·
                        linarith only [hdelta1, ht013b, ht014a, ht123d, ht134b, hbg3c]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, ht134b, hbg3c]
                      ·
                        linarith only [hdelta1, ht123d, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, ht013c, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht234a, hbg3c]
                    ·
                      have hb0 := m.budget 0 (by decide) 4 1 3 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                      ·
                        linarith only [hdelta1, ht013a, ht014b, ht123c, ht124e, hbg0]
                      ·
                        linarith only [hdelta1, ht012c, ht014a, ht023c, ht124e, hbg0]
                      ·
                        linarith only [hdelta1, ht012c, ht013b, ht014a, ht124e, hbg0]
                      ·
                        have hb2 := m.budget 2 (by decide) 4 3 0 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc20, hc21] at hb2
                        rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                        ·
                          have hb4 := m.budget 4 (by decide) 3 2 1 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc43, hc42, hc41, hc40] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hn, hdelta1, h021, h340, ht023a, hbg2, hbg4]
                          ·
                            linarith only [hdelta1, h121, h240, ht013a, ht014a, ht123c, hbg4]
                          ·
                            linarith only [hdelta1, ht013a, ht014c, ht123c, hbg4, ht124e]
                          ·
                            linarith only [hn, hdelta1, ht023a, ht234b, hbg2, hbg4, hbg0]
                          ·
                            linarith only [hdelta1, h021, h340, ht023a, hbg2, hbg4a]
                          ·
                            linarith only [hdelta1, h021, h340, ht023a, hbg2, hbg4a]
                          ·
                            linarith only [hdelta1, h021, h340, ht023a, hbg2, hbg4a]
                          ·
                            linarith only [hdelta1, h121, h240, ht013a, ht014c, ht123c, hbg4c]
                          ·
                            linarith only [hdelta1, ht023a, ht234b, hbg4b, hbg2, hbg0]
                          ·
                            linarith only [hdelta1, ht023a, ht234b, hbg4b, hbg2, hbg0]
                        ·
                          have hb4 := m.budget 4 (by decide) 3 2 1 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc43, hc42, hc41, hc40] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h131, h340, ht013a, ht014a, ht124b, hbg4]
                          ·
                            linarith only [hdelta1, h121, h240, ht013a, ht014a, ht123c, hbg4]
                          ·
                            linarith only [hdelta1, ht013a, ht014c, ht123c, hbg4, ht124e]
                          ·
                            linarith only [hn, hdelta1, ht234a, hbg4, hbg2, hbg0]
                          ·
                            linarith only [hdelta1, h021, h340, ht234c, hbg2, hbg4a]
                          ·
                            linarith only [hdelta1, h021, h340, ht234c, hbg2, hbg4a]
                          ·
                            linarith only [hdelta1, h021, h340, ht234c, hbg2, hbg4a]
                          ·
                            linarith only [hdelta1, h121, h240, ht013a, ht014c, ht123c, hbg4c]
                          ·
                            linarith only [hdelta1, ht234a, hbg2, hbg0, hbg4b]
                          ·
                            linarith only [hdelta1, ht234a, hbg2, hbg0, hbg4b]
                        ·
                          linarith only [hdelta1, h121, h340, ht023a, ht234a, hbg2]
                        ·
                          linarith only [hdelta1, ht013a, ht014a, ht124b, ht123c, hbg2]
                        ·
                          have hb4 := m.budget 4 (by decide) 3 2 1 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc43, hc42, hc41, hc40] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hn, hdelta1, h021, h340, hbg2c, hbg4]
                          ·
                            linarith only [hdelta1, h121, h240, ht013a, ht014a, ht123c, hbg4]
                          ·
                            linarith only [hdelta1, ht013a, ht014c, ht123c, ht124e, hbg4]
                          ·
                            linarith only [hdelta1, ht234b, hbg2b, hbg4, hbg2a, hbg0]
                          ·
                            linarith only [hdelta1, h121, h340, ht012c, hbg2c, hbg4a]
                          ·
                            linarith only [hdelta1, h121, h340, ht012c, hbg2c, hbg4a]
                          ·
                            linarith only [hdelta1, hbg4b, hbg2c, hbg4a, hbg0]
                          ·
                            linarith only [hdelta1, h121, h240, ht013a, ht014c, ht123c, hbg4c]
                          ·
                            linarith only [hdelta1, ht234b, hbg4b, hbg2c, hbg0]
                          ·
                            linarith only [hdelta1, ht234b, hbg4b, hbg2c, hbg0]
                        ·
                          linarith only [hdelta1, h121, h340, ht023a, ht234b, hbg2c]
                        ·
                          linarith only [hdelta1, ht012c, ht023a, hbg2c]
                        ·
                          linarith only [hdelta1, h121, h340, ht234a, hbg2c]
                        ·
                          have hb4 := m.budget 4 (by decide) 3 2 1 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc43, hc42, hc41, hc40] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h121, h340, ht013a, ht014a, ht124b, ht123c, hbg4]
                          ·
                            linarith only [hdelta1, ht013a, ht014a, ht123c, hbg2b, hbg4]
                          ·
                            linarith only [hdelta1, ht013a, ht014c, ht124b, ht123c, hbg2b, hbg4]
                          ·
                            linarith only [hdelta1, ht234a, hbg2a, hbg0, hbg4]
                          ·
                            linarith only [hdelta1, h121, h340, ht013a, ht014a, ht123c, hbg4c]
                          ·
                            linarith only [hdelta1, h121, h340, ht013a, ht014c, ht124b, ht123c, hbg4c]
                          ·
                            linarith only [hdelta1, ht234c, hbg2a, hbg4c, hbg0]
                          ·
                            linarith only [hdelta1, ht012a, h121, h240, ht014c, hbg4c]
                          ·
                            linarith only [hdelta1, ht012c, ht014b, ht234a, hbg2c, hbg4c]
                          ·
                            linarith only [hdelta1, ht012c, ht124b, ht234a, hbg2c, hbg4c]
                        ·
                          linarith only [hdelta1, ht013b, ht014a, ht023c, ht124b, hbg2c]
                      ·
                        linarith only [hdelta1, ht023c, ht024e, hbg0c]
                      ·
                        linarith only [hdelta1, ht012c, ht013b, ht014b, hbg0c, ht124e]
                      ·
                        have hb2 := m.budget 2 (by decide) 4 3 0 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc20, hc21] at hb2
                        rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                        ·
                          linarith only [hdelta1, h121, h340, ht013a, ht023a, ht123c, ht234b, hbg2, hbg0c]
                        ·
                          linarith only [hdelta1, ht013a, ht123d, hbg2, hbg0c]
                        ·
                          linarith only [hdelta1, h040, h121, ht012b, hbg2, hbg0a]
                        ·
                          linarith only [hdelta1, ht013a, ht014b, ht124b, ht123c, hbg2, hbg0a]
                        ·
                          linarith only [hdelta1, h121, h340, ht013a, ht123c, ht234b, hbg0c, hbg2c]
                        ·
                          linarith only [hdelta1, h121, h340, ht023a, ht234b, hbg2c]
                        ·
                          linarith only [hdelta1, ht012a, ht023a, hbg0c, hbg2c]
                        ·
                          linarith only [hdelta1, h121, h340, ht234a, hbg2c]
                        ·
                          linarith only [hdelta1, ht013a, ht123c, ht234c, hbg0c, hbg2c]
                        ·
                          linarith only [hdelta1, ht013b, ht014b, ht023c, ht124b, hbg2c, hbg0a]
                      ·
                        linarith only [hdelta1, ht012d, hbg0c]
                      ·
                        have hb4 := m.budget 4 (by decide) 3 2 1 0 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc43, hc42, hc41, hc40] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, h121, h340, ht013c, ht014c, ht024b, ht123c, hbg4, hbg0a]
                        ·
                          linarith only [hdelta1, h121, h240, ht013c, ht014a, ht123c, hbg4, hbg0a]
                        ·
                          linarith only [hdelta1, h121, h140, ht013c, ht014c, ht123c, hbg4, hbg0a]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 2 0 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc30, hc31] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht023a, hbg0b, hbg3, hbg4]
                          ·
                            linarith only [hdelta1, ht023c, ht234a, hbg0b, hbg3, hbg4]
                          ·
                            linarith only [hdelta1, h010, h121, ht123c, hbg3, hbg0a]
                          ·
                            linarith only [hdelta1, ht013a, ht014a, ht124b, ht234b, hbg3]
                          ·
                            linarith only [hdelta1, ht023c, hbg3c, hbg0b, hbg4]
                          ·
                            linarith only [hdelta1, ht014a, ht023a, ht123c, hbg3c, ht124e, hbg4, hbg0c]
                          ·
                            linarith only [hdelta1, ht013c, ht014c, ht023a, hbg3c, hbg0c]
                          ·
                            linarith only [hdelta1, ht123d, hbg3c]
                          ·
                            linarith only [hdelta1, ht013c, ht234a, hbg3c]
                          ·
                            linarith only [hdelta1, ht014a, ht124b, hbg3c, ht234b, hbg0a]
                        ·
                          linarith only [hdelta1, h011, h340, ht014a, hbg4c]
                        ·
                          linarith only [hdelta1, h121, h340, ht013c, ht014c, ht124b, ht123c, hbg4c, hbg0a]
                        ·
                          linarith only [hdelta1, ht014a, ht023c, ht124b, hbg4c, hbg0c]
                        ·
                          linarith only [hdelta1, h121, h240, ht013c, ht014c, ht123c, hbg4c, hbg0a]
                        ·
                          linarith only [hdelta1, ht014a, ht023c, hbg4c, ht234b, hbg0c]
                        ·
                          have hb2 := m.budget 2 (by decide) 4 3 0 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc20, hc21] at hb2
                          rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                          ·
                            linarith only [hdelta1, ht012c, ht023a, hbg4c, ht234b, ht124e, hbg2]
                          ·
                            linarith only [hdelta1, ht012c, ht234a, hbg4c, ht124e, hbg2]
                          ·
                            linarith only [hdelta1, ht012b, ht014c, ht124e, hbg4a, hbg2]
                          ·
                            linarith only [hdelta1, ht012c, ht014c, ht023c, ht024b, hbg0a, hbg2]
                          ·
                            linarith only [hdelta1, ht012c, hbg4c, ht234b, ht124e, hbg2c]
                          ·
                            linarith only [hdelta1, ht023a, hbg4c, ht234b, ht124e, hbg2c]
                          ·
                            linarith only [hdelta1, ht012c, ht023a, hbg2c]
                          ·
                            linarith only [hdelta1, ht234a, hbg4c, ht124e, hbg2c]
                          ·
                            linarith only [hdelta1, ht012c, ht124b, ht234a, hbg4c, hbg2c]
                          ·
                            linarith only [hdelta1, ht014c, ht023c, ht124b, hbg4a, hbg2c, hbg0a]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 2 0 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc30, hc31] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h121, h340, ht012c, ht023b, hbg3, hbg0a]
                        ·
                          linarith only [hdelta1, h121, h230, ht012c, hbg3, hbg0a]
                        ·
                          linarith only [hdelta1, ht013b, ht014a, ht123c, hbg3, ht124e]
                        ·
                          linarith only [hdelta1, ht013a, ht014a, ht124b, ht234b, hbg3]
                        ·
                          linarith only [hdelta1, h121, h340, ht012c, hbg3c, hbg0a]
                        ·
                          have hb4 := m.budget 4 (by decide) 3 2 1 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc43, hc42, hc41, hc40] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h021, h340, ht013b, ht014c, ht024b, hbg0a, hbg4]
                          ·
                            linarith only [hdelta1, h121, h240, ht012c, ht013b, ht014a, hbg0a, hbg4]
                          ·
                            linarith only [hdelta1, h121, h140, ht012c, ht013b, ht014c, hbg0a, hbg4]
                          ·
                            linarith only [hdelta1, ht023b, hbg3a, hbg0c, hbg4]
                          ·
                            linarith only [hdelta1, h121, h340, ht012c, ht013b, ht014a, hbg4c, hbg0a]
                          ·
                            linarith only [hdelta1, h121, h340, ht012c, ht013b, ht014c, ht124b, hbg4c, hbg0a]
                          ·
                            linarith only [hdelta1, ht013b, ht014a, ht124b, hbg4c, hbg0c]
                          ·
                            linarith only [hdelta1, h121, h240, ht012c, ht013b, ht014c, hbg4c, hbg0a]
                          ·
                            linarith only [hdelta1, ht013b, ht014a, ht234b, hbg4c, hbg0c]
                          ·
                            linarith only [hdelta1, ht023b, ht123c, hbg4c, ht124e, hbg3c]
                        ·
                          linarith only [hdelta1, ht013a, ht014c, ht023b, hbg3c, hbg0c]
                        ·
                          linarith only [hdelta1, h131, h340, ht234a, hbg3c]
                        ·
                          linarith only [hdelta1, ht013a, ht014c, ht234a, hbg3c, hbg0c]
                        ·
                          linarith only [hdelta1, ht023b, ht234a, hbg3c]
    ·
      rcases m.triangle 0 1 4 (by decide) (by decide) with ⟨ht014a,ht014b,ht014c,ht014d,ht014e⟩ | ⟨ht014a,ht014b,ht014c,ht014d,ht014e⟩
      ·
        rcases m.triangle 0 2 3 (by decide) (by decide) with ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩ | ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩
        ·
          linarith only [ht012b, ht013c, ht023b]
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                linarith only [ht012a, ht013c, ht023b, ht123a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 3 0 1 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, ht012c, ht234d, hbg2, ht124a]
                      ·
                        linarith only [hdelta1, ht012b, ht013a, ht123b, ht234d, hbg2, ht124a]
                      ·
                        linarith only [hdelta1, ht012a, ht013a, ht123b, ht234d, hbg2]
                      ·
                        linarith only [hdelta1, ht012a, ht013a, ht123b, hbg2, ht124a]
                      ·
                        linarith only [hdelta1, ht234d, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012c, ht234d, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, h230, h241, ht012b, ht013a, ht123b, hbg2c]
                      ·
                        linarith only [hdelta1, ht012b, ht013a, ht123b, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012a, ht013a, ht123b, hbg2c]
                    ·
                      linarith only [ht013b, ht034a, ht123b, ht234a]
                  ·
                    linarith only [ht012b, ht013a, ht034c, ht024b, ht134a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 3 0 4 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc20, hc21] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h121, h230, ht024a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht012b, ht013a, ht124a, ht123e, hbg2]
                      ·
                        linarith only [hdelta1, ht013a, ht014b, ht024c, ht123e, hbg2]
                      ·
                        linarith only [hdelta1, ht012a, ht013a, ht123b, hbg2]
                      ·
                        linarith only [hdelta1, h121, h230, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, h121, h230, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012e, hbg2c]
                      ·
                        linarith only [hdelta1, ht012b, ht013a, ht124a, ht123b, hbg2c]
                      ·
                        linarith only [hdelta1, ht012b, ht013a, ht024a, ht123b, hbg2c]
                    ·
                      linarith only [ht013b, ht034a, ht123b, ht234a]
                  ·
                    linarith only [ht012b, ht013a, ht034c, ht024b, ht134a]
            ·
              linarith only [ht012b, ht013c, ht034c, ht024b]
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                linarith only [ht012c, ht023a, ht123a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  linarith only [ht012c, ht024a, ht124a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb0 := m.budget 0 (by decide) 3 1 4 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                      ·
                        linarith only [hdelta1, ht012a, ht013b, ht123e, hbg0]
                      ·
                        linarith only [hdelta1, ht012c, ht013a, ht024c, ht123e, hbg0]
                      ·
                        linarith only [hdelta1, ht012c, ht013a, ht014b, ht123e, hbg0]
                      ·
                        have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc31, hc30] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h141, h230, ht013a, ht014a, hbg3]
                        ·
                          linarith only [hdelta1, ht013c, ht014a, ht123e, ht124c, hbg3]
                        ·
                          have hb2 := m.budget 2 (by decide) 3 4 0 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc20, hc21] at hb2
                          rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                          ·
                            linarith only [hn, hdelta1, h230, h341, ht024a, hbg2, hbg3, hbg0]
                          ·
                            linarith only [hn, hdelta1, ht234e, hbg2, hbg3, hbg0]
                          ·
                            linarith only [hdelta1, ht012b, ht013a, ht123e, hbg2]
                          ·
                            linarith only [hdelta1, ht012a, ht013a, ht123b, hbg2]
                          ·
                            linarith only [hdelta1, h230, h341, hbg2a, hbg3, hbg0, hbg2b]
                          ·
                            linarith only [hdelta1, h230, h341, ht024a, hbg2a, hbg3, hbg0]
                          ·
                            linarith only [hdelta1, h230, h341, ht024a, hbg2a, hbg3, hbg0]
                          ·
                            linarith only [hdelta1, hbg2a, ht234e, hbg3, hbg0]
                          ·
                            linarith only [hdelta1, hbg2a, ht234e, hbg3, hbg0]
                          ·
                            linarith only [hdelta1, ht013a, ht014b, ht024c, ht123b, hbg2c]
                        ·
                          linarith only [hdelta1, ht013a, ht014a, ht123b, ht134c, hbg3]
                        ·
                          linarith only [hdelta1, h141, h230, ht013c, ht014a, hbg3c]
                        ·
                          have hb2 := m.budget 2 (by decide) 3 4 0 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc20, hc21] at hb2
                          rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                          ·
                            linarith only [hdelta1, h230, h341, ht024a, hbg2, hbg3b, hbg0]
                          ·
                            linarith only [hdelta1, ht234e, hbg2, hbg3b, hbg0]
                          ·
                            linarith only [hdelta1, h121, h230, ht012b, ht013a, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, ht012a, ht013a, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, h230, h341, hbg3b, hbg2c, hbg0]
                          ·
                            linarith only [hdelta1, h121, h230, ht024a, hbg2c]
                          ·
                            linarith only [hdelta1, ht012c, ht024a, hbg2c]
                          ·
                            linarith only [hdelta1, h121, h230, ht013b, ht234e, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht012c, ht013b, ht234e, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht013a, ht014b, ht024c, hbg2c, hbg3a]
                        ·
                          linarith only [hdelta1, ht013b, ht034a, hbg3c]
                        ·
                          have hb2 := m.budget 2 (by decide) 3 4 0 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc20, hc21] at hb2
                          rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                          ·
                            linarith only [hdelta1, h230, h341, ht024a, hbg2, hbg3b, hbg0]
                          ·
                            linarith only [hdelta1, ht234e, hbg2, hbg3b, hbg0]
                          ·
                            linarith only [hdelta1, ht012b, ht013c, ht123e, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, ht013c, ht014a, ht123b, ht124c, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, h230, h341, ht012c, ht123e, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, h230, h341, ht024a, ht123e, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht012c, ht024a, hbg2c]
                          ·
                            linarith only [hdelta1, ht123e, ht234e, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht012c, ht123b, ht234e, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht012b, ht013a, ht123b, hbg2c]
                        ·
                          linarith only [hdelta1, ht034a, ht123b, hbg3c]
                        ·
                          have hb2 := m.budget 2 (by decide) 3 4 0 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc20, hc21] at hb2
                          rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                          ·
                            linarith only [hn, hdelta1, ht024a, hbg2, hbg3c, hbg0]
                          ·
                            linarith only [hdelta1, ht234b, hbg2, hbg3b, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, ht013a, ht014b, ht024c, ht123e, hbg2]
                          ·
                            linarith only [hdelta1, ht012a, ht013a, ht123b, hbg2]
                          ·
                            linarith only [hdelta1, hbg2b, hbg2a, hbg3c, hbg0]
                          ·
                            linarith only [hdelta1, ht024a, hbg2a, hbg3c, hbg0]
                          ·
                            linarith only [hdelta1, ht024a, hbg2a, hbg3c, hbg0]
                          ·
                            linarith only [hdelta1, ht234b, hbg2a, hbg3c, hbg0]
                          ·
                            linarith only [hdelta1, ht234b, hbg2a, hbg3c, hbg0]
                          ·
                            linarith only [hdelta1, ht012b, ht013a, ht123b, hbg2c]
                      ·
                        linarith only [hdelta1, ht024c, ht023e, hbg0c]
                      ·
                        linarith only [hdelta1, ht012c, ht013b, ht014b, ht123e, hbg0c]
                      ·
                        have hb4 := m.budget 4 (by decide) 2 0 1 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc42, hc40, hc41, hc43] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, ht014a, ht024c, ht124d, hbg4, hbg0c]
                        ·
                          linarith only [hdelta1, h030, h121, ht014b, ht124c, hbg0a, hbg4]
                        ·
                          linarith only [hdelta1, h230, h341, ht013b, ht014a, ht123b, hbg0a, hbg4]
                        ·
                          linarith only [hdelta1, ht014a, ht024a, ht134c, hbg4, hbg0c]
                        ·
                          linarith only [hdelta1, ht124d, hbg4c]
                        ·
                          linarith only [hdelta1, ht014c, hbg4c, ht234e]
                        ·
                          linarith only [hdelta1, ht014a, ht024c, hbg4c, ht134c, hbg0c]
                        ·
                          linarith only [hdelta1, h030, h341, ht014b, hbg0a, hbg4c]
                        ·
                          linarith only [hdelta1, ht014b, ht024a, hbg4c, ht134c, hbg0c]
                        ·
                          linarith only [hdelta1, ht014a, ht024a, hbg4c, hbg0c]
                      ·
                        linarith only [hdelta1, ht012d, hbg0c]
                      ·
                        have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc31, hc30] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h041, h230, ht013a, hbg3, hbg0a]
                        ·
                          linarith only [hdelta1, h130, h341, ht013c, ht014c, ht134c, hbg3, hbg0a]
                        ·
                          have hb4 := m.budget 4 (by decide) 2 0 1 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc42, hc40, hc41, hc43] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, ht024c, hbg4, ht234e, hbg3, hbg0b]
                          ·
                            linarith only [hdelta1, h010, h141, hbg4, hbg0a]
                          ·
                            linarith only [hdelta1, h230, h341, ht013a, ht014a, ht123b, hbg4]
                          ·
                            linarith only [hdelta1, ht024a, hbg4, hbg3, hbg0b]
                          ·
                            linarith only [hdelta1, ht124d, hbg4c]
                          ·
                            linarith only [hdelta1, ht014c, ht234e, hbg4c]
                          ·
                            linarith only [hdelta1, ht024c, hbg3, hbg4c, hbg0b]
                          ·
                            linarith only [hdelta1, h230, h341, ht013a, ht123b, hbg4c, hbg0a]
                          ·
                            linarith only [hdelta1, ht013c, ht024a, ht134c, hbg0c, hbg4c]
                          ·
                            linarith only [hdelta1, ht013c, ht014c, ht024a, hbg0c, hbg4c]
                        ·
                          linarith only [hdelta1, ht013a, ht034a, ht024c, ht123b, hbg3, hbg0c]
                        ·
                          linarith only [hdelta1, h041, h230, ht013c, hbg0a, hbg3c]
                        ·
                          linarith only [hdelta1, h230, h341, ht013a, ht024c, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, ht013a, ht014c, ht134c, hbg0a, hbg3c]
                        ·
                          have hb2 := m.budget 2 (by decide) 3 4 0 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc20, hc21] at hb2
                          rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                          ·
                            linarith only [hdelta1, h230, h341, ht012c, ht024a, ht123e, hbg2, hbg3c]
                          ·
                            linarith only [hdelta1, ht012c, ht123e, ht234e, hbg2, hbg3c]
                          ·
                            linarith only [hdelta1, ht012b, ht013c, ht123e, hbg3a, hbg2]
                          ·
                            linarith only [hdelta1, ht012c, ht013c, ht024c, ht123b, hbg3a, hbg2, hbg0a]
                          ·
                            linarith only [hdelta1, h230, h341, ht012c, ht123e, hbg2c, hbg3c]
                          ·
                            linarith only [hdelta1, h230, h341, ht024a, ht123e, hbg2c, hbg3c]
                          ·
                            linarith only [hdelta1, ht012c, ht024a, hbg2c]
                          ·
                            linarith only [hdelta1, h240, h341, ht123e, hbg2c, hbg3c]
                          ·
                            linarith only [hdelta1, ht012c, ht123b, ht234e, hbg2c, hbg3c]
                          ·
                            linarith only [hdelta1, ht013c, ht024c, ht123b, hbg3a, hbg2c, hbg0a]
                        ·
                          linarith only [hdelta1, ht034a, ht123b, hbg3c]
                        ·
                          linarith only [hdelta1, ht013a, ht024c, ht123b, hbg0c, hbg3c]
                      ·
                        have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc31, hc30] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h141, h230, ht013a, ht014a, hbg3]
                        ·
                          linarith only [hdelta1, h121, h130, ht012c, ht013c, ht014b, hbg3, hbg0a]
                        ·
                          have hb4 := m.budget 4 (by decide) 2 0 1 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc42, hc40, hc41, hc43] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hn, hdelta1, h240, h341, hbg4, hbg0c, hbg3]
                          ·
                            linarith only [hdelta1, ht013a, ht014b, ht123e, ht124c, hbg4]
                          ·
                            linarith only [hdelta1, h130, h341, ht013a, ht014a, hbg4]
                          ·
                            linarith only [hdelta1, ht024b, hbg4, hbg3, hbg0b, hbg0a]
                          ·
                            linarith only [hdelta1, ht234e, hbg0c, hbg3, hbg4a]
                          ·
                            linarith only [hdelta1, ht234e, hbg0c, hbg3, hbg4a]
                          ·
                            linarith only [hdelta1, hbg0c, hbg3, hbg4a, hbg4b]
                          ·
                            linarith only [hdelta1, h230, h341, ht013a, ht014b, ht123b, hbg4c]
                          ·
                            linarith only [hdelta1, ht024b, hbg0c, hbg3, hbg4b]
                          ·
                            linarith only [hdelta1, ht024b, hbg0c, hbg3, hbg4b]
                        ·
                          linarith only [hdelta1, ht013a, ht014a, ht123b, ht134c, hbg3]
                        ·
                          linarith only [hdelta1, h121, h230, ht012c, ht013c, ht014b, hbg3c, hbg0a]
                        ·
                          linarith only [hdelta1, h230, h341, ht013a, ht014b, hbg3c, hbg0c]
                        ·
                          linarith only [hdelta1, ht013a, ht014a, hbg3c, ht134c]
                        ·
                          have hb2 := m.budget 2 (by decide) 3 4 0 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc20, hc21] at hb2
                          rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                          ·
                            linarith only [hdelta1, h021, h230, ht024b, hbg2, hbg0a]
                          ·
                            linarith only [hdelta1, ht012c, ht123e, hbg3c, ht234e, hbg2]
                          ·
                            linarith only [hdelta1, ht013c, ht014b, ht123e, hbg2, hbg3a, hbg0a]
                          ·
                            linarith only [hdelta1, ht012c, ht013c, ht014b, ht023b, hbg2, hbg0a]
                          ·
                            linarith only [hdelta1, h230, h341, ht012c, ht123e, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, h230, h341, ht024a, ht123e, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht012c, ht024b, hbg2c, hbg0a]
                          ·
                            linarith only [hdelta1, ht123e, hbg3c, ht234e, hbg2c]
                          ·
                            linarith only [hdelta1, ht012c, ht123b, hbg3c, ht234e, hbg2c]
                          ·
                            linarith only [hdelta1, ht013c, ht014b, ht123b, hbg2c, hbg3a, hbg0a]
                        ·
                          linarith only [hdelta1, ht034a, ht123b, hbg3c]
                        ·
                          linarith only [hdelta1, ht013a, ht014b, ht123b, hbg0c, hbg3c]
                    ·
                      linarith only [ht013b, ht034a, ht123b, ht234a]
                  ·
                    linarith only [ht013a, ht014b, ht034c, ht134a]
            ·
              linarith only [ht013c, ht014b, ht034c]
      ·
        rcases m.triangle 0 2 3 (by decide) (by decide) with ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩ | ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩
        ·
          linarith only [ht012b, ht013c, ht023b]
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            linarith only [ht012b, ht014c, ht024b]
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                linarith only [ht012c, ht023a, ht123a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  linarith only [ht012a, ht014c, ht124a, ht024b]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb0 := m.budget 0 (by decide) 3 4 1 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                      ·
                        linarith only [hdelta1, ht012a, ht013b, ht014c, ht123e, hbg0]
                      ·
                        linarith only [hdelta1, ht012a, ht013b, ht034b, ht123e, hbg0]
                      ·
                        linarith only [hdelta1, ht012c, ht013a, ht123e, hbg0]
                      ·
                        have hb2 := m.budget 2 (by decide) 3 4 0 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc20, hc21] at hb2
                        rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                        ·
                          linarith only [hdelta1, ht012a, h121, h230, ht014a, ht124b, hbg2]
                        ·
                          have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc31, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012a, h121, h230, ht013a, hbg3]
                          ·
                            linarith only [hdelta1, ht012a, ht013c, ht123e, hbg3]
                          ·
                            linarith only [hn, hdelta1, hbg3, hbg0, ht234e, hbg2]
                          ·
                            linarith only [hn, hdelta1, ht034a, hbg3, hbg0, ht234b, hbg2]
                          ·
                            linarith only [hdelta1, ht012a, h121, h230, ht014c, ht034b, hbg3c]
                          ·
                            linarith only [hdelta1, hbg0, ht234e, hbg3b, hbg2]
                          ·
                            linarith only [hdelta1, ht034a, hbg0, ht234b, hbg3b, hbg2]
                          ·
                            linarith only [hdelta1, hbg0, ht234e, hbg3b, hbg2]
                          ·
                            linarith only [hdelta1, ht034a, hbg0, ht234b, hbg3b, hbg2]
                          ·
                            linarith only [hdelta1, hbg0, ht234e, hbg3a, hbg2]
                        ·
                          linarith only [hdelta1, ht012b, ht013a, ht123e, hbg2]
                        ·
                          linarith only [hdelta1, ht012a, ht014a, ht123b, hbg2, ht134b]
                        ·
                          have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc31, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012a, h121, h230, ht013a, hbg3]
                          ·
                            linarith only [hdelta1, ht012a, ht013c, ht123e, hbg3]
                          ·
                            linarith only [hdelta1, h230, h341, hbg0, hbg2b, hbg3, hbg2a]
                          ·
                            linarith only [hdelta1, ht034a, hbg0, hbg2b, hbg3, hbg2a]
                          ·
                            linarith only [hdelta1, ht012a, h121, h230, ht014c, ht034b, hbg3c]
                          ·
                            linarith only [hdelta1, h230, h341, hbg0, hbg2c, hbg3b]
                          ·
                            linarith only [hdelta1, ht034a, hbg0, hbg2c, hbg3b]
                          ·
                            linarith only [hdelta1, h230, h341, hbg0, hbg2c, hbg3b]
                          ·
                            linarith only [hdelta1, ht034a, hbg0, hbg2c, hbg3b]
                          ·
                            linarith only [hdelta1, h230, h341, hbg0, hbg2c, hbg3a]
                        ·
                          linarith only [hdelta1, h121, h230, ht012b, ht014a, ht124b, hbg2c]
                        ·
                          linarith only [hdelta1, ht012a, ht014a, ht124b, hbg2c]
                        ·
                          have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc31, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012a, h121, h230, ht014a, hbg3, ht134b]
                          ·
                            linarith only [hdelta1, ht012b, ht013c, ht123e, hbg3, hbg2b]
                          ·
                            linarith only [hdelta1, hbg0, ht234e, hbg2a, hbg3]
                          ·
                            linarith only [hdelta1, ht034a, hbg0, ht234b, hbg2a, hbg3]
                          ·
                            linarith only [hdelta1, h121, h230, ht012b, ht014c, ht034b, hbg3c, hbg2b]
                          ·
                            linarith only [hdelta1, h121, h230, ht013b, ht234e, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht013b, ht034a, hbg3c]
                          ·
                            linarith only [hdelta1, h121, h130, ht234e, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht034a, ht123e, ht234b, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht013b, ht123e, ht234b, hbg3c, hbg2c]
                        ·
                          have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc31, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012a, h121, h230, ht014a, ht134b, hbg3]
                          ·
                            linarith only [hdelta1, ht012a, ht013c, ht123b, hbg2b, hbg3]
                          ·
                            linarith only [hdelta1, hbg0, ht234e, hbg3, hbg2a]
                          ·
                            linarith only [hdelta1, ht034a, hbg0, ht234b, hbg3, hbg2a]
                          ·
                            linarith only [hdelta1, ht012a, ht014c, ht034b, hbg3c, hbg2b]
                          ·
                            linarith only [hdelta1, ht012c, ht013b, ht234e, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht012b, ht014a, ht034a, hbg0, hbg3c, ht134b]
                          ·
                            linarith only [hdelta1, ht012c, ht123b, ht234e, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht034a, ht123b, hbg3c]
                          ·
                            linarith only [hdelta1, hbg0, ht234b, hbg3c, hbg2a]
                        ·
                          linarith only [hdelta1, ht012b, ht014a, ht123b, ht134b, hbg2c]
                      ·
                        linarith only [hdelta1, ht012a, ht013b, ht123e, hbg0c]
                      ·
                        linarith only [hdelta1, ht012c, ht013b, ht014c, ht123e, hbg0c]
                      ·
                        have hb2 := m.budget 2 (by decide) 3 4 0 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc20, hc21] at hb2
                        rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                        ·
                          linarith only [hdelta1, ht012a, h121, h230, ht014a, ht124b, hbg2]
                        ·
                          have hb4 := m.budget 4 (by decide) 2 1 0 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc42, hc41, hc40, hc43] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, ht012a, h121, h230, ht014a, ht234b, hbg4]
                          ·
                            linarith only [hdelta1, ht012a, ht014c, ht124e, hbg4]
                          ·
                            linarith only [hdelta1, h030, h341, hbg0a, hbg4]
                          ·
                            linarith only [hdelta1, ht034a, hbg2, hbg4, hbg0b]
                          ·
                            linarith only [hdelta1, ht012a, h121, h230, ht014c, ht234b, hbg4c]
                          ·
                            linarith only [hdelta1, ht234e, hbg2, hbg0c, hbg4b]
                          ·
                            linarith only [hdelta1, ht034c, hbg2, hbg0c, hbg4b]
                          ·
                            linarith only [hdelta1, h240, h341, hbg2, hbg0c, hbg4b]
                          ·
                            linarith only [hdelta1, ht034c, hbg2, hbg0c, hbg4b]
                          ·
                            linarith only [hdelta1, hbg2, hbg0c, hbg4a, hbg4b]
                        ·
                          linarith only [hdelta1, h121, h130, ht012b, ht013b, ht014c, hbg2, hbg0a]
                        ·
                          linarith only [hdelta1, ht012a, ht013b, ht014c, ht123b, hbg2, hbg0a]
                        ·
                          linarith only [hdelta1, ht012a, h121, h230, ht014c, hbg0c, hbg2c]
                        ·
                          linarith only [hdelta1, h121, h230, ht024a, hbg2c]
                        ·
                          linarith only [hdelta1, ht012a, ht014a, ht124b, hbg2c]
                        ·
                          have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc31, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h011, h230, ht013b, ht014c, hbg0a, hbg3]
                          ·
                            linarith only [hdelta1, ht012b, ht014c, ht123e, hbg0a, hbg3, hbg2b]
                          ·
                            linarith only [hdelta1, ht013b, ht123e, ht234e, hbg3, hbg2c]
                          ·
                            linarith only [hdelta1, ht013b, ht034a, ht123e, ht234b, hbg3, hbg2c]
                          ·
                            linarith only [hdelta1, h121, h230, ht012b, ht014c, hbg3c, hbg0a, hbg2b]
                          ·
                            linarith only [hdelta1, h121, h230, ht013b, hbg3c, ht234e, hbg2c]
                          ·
                            linarith only [hdelta1, ht013b, ht034a, hbg3c]
                          ·
                            linarith only [hdelta1, h240, h341, ht123e, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht034a, ht123e, hbg3c, ht234b, hbg2c]
                          ·
                            linarith only [hdelta1, ht013b, ht123e, hbg3c, ht234b, hbg2c]
                        ·
                          linarith only [hdelta1, ht012a, ht014c, ht234b, hbg0c, hbg2c]
                        ·
                          linarith only [hdelta1, ht012b, ht013b, ht014c, ht123b, hbg0a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012c, ht014b, ht123e, hbg0c, ht134b]
                      ·
                        have hb2 := m.budget 2 (by decide) 3 4 0 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc20, hc21] at hb2
                        rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                        ·
                          linarith only [hdelta1, ht012a, h121, h230, ht014a, ht124b, hbg2]
                        ·
                          have hb4 := m.budget 4 (by decide) 2 1 0 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc42, hc41, hc40, hc43] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, ht012a, h121, h240, ht014a, hbg4]
                          ·
                            linarith only [hdelta1, ht012a, h121, h140, hbg4, hbg0a]
                          ·
                            linarith only [hdelta1, ht034b, hbg4, ht234e, hbg0b, hbg2]
                          ·
                            linarith only [hdelta1, ht034a, hbg4, hbg0b, hbg2]
                          ·
                            linarith only [hdelta1, ht012a, h121, h230, ht234b, hbg4c, hbg0a]
                          ·
                            linarith only [hdelta1, ht014b, ht234e, hbg4c]
                          ·
                            linarith only [hdelta1, ht012b, ht014b, ht034a, hbg0c, hbg4c]
                          ·
                            linarith only [hdelta1, ht134e, hbg4c]
                          ·
                            linarith only [hdelta1, ht012a, ht034a, ht123e, hbg0c, ht134b, hbg4c, hbg2]
                          ·
                            linarith only [hdelta1, ht034b, hbg0b, hbg4c, hbg2]
                        ·
                          linarith only [hdelta1, ht012b, ht013a, ht123e, hbg2]
                        ·
                          linarith only [hdelta1, ht012a, ht023b, ht034b, hbg2, hbg0a]
                        ·
                          linarith only [hdelta1, ht012a, h121, h230, ht034b, hbg0c, hbg2c]
                        ·
                          linarith only [hdelta1, h121, h230, ht012b, ht014b, ht124b, hbg2c, hbg0a]
                        ·
                          linarith only [hdelta1, ht012a, ht014b, ht124b, hbg2c, hbg0a]
                        ·
                          have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc31, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h011, h230, ht014b, hbg3, ht134b, hbg0a]
                          ·
                            linarith only [hdelta1, ht012b, ht034b, ht123e, hbg3, hbg0a, hbg2b]
                          ·
                            linarith only [hdelta1, ht013b, ht123e, ht234e, hbg3, hbg2c]
                          ·
                            linarith only [hdelta1, ht013b, ht034a, ht123e, ht234b, hbg3, hbg2c]
                          ·
                            linarith only [hdelta1, h121, h230, ht012b, ht034b, hbg3c, hbg0a, hbg2b]
                          ·
                            linarith only [hdelta1, h121, h230, ht013b, hbg3c, ht234e, hbg2c]
                          ·
                            linarith only [hdelta1, ht013b, ht034a, hbg3c]
                          ·
                            linarith only [hdelta1, h240, h341, ht123e, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht034a, ht123e, hbg3c, ht234b, hbg2c]
                          ·
                            linarith only [hdelta1, ht013b, ht123e, hbg3c, ht234b, hbg2c]
                        ·
                          linarith only [hdelta1, ht012a, ht034b, ht234b, hbg0c, hbg2c]
                        ·
                          linarith only [hdelta1, ht023a, hbg2c]
                      ·
                        have hb4 := m.budget 4 (by decide) 2 1 0 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc42, hc41, hc40, hc43] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, h021, h240, ht014a, hbg4, hbg0a]
                        ·
                          linarith only [hdelta1, h121, h130, ht012c, ht014c, hbg4, hbg0a, ht134b]
                        ·
                          linarith only [hdelta1, ht014a, ht034b, ht124b, ht234e, hbg4, hbg0c]
                        ·
                          linarith only [hdelta1, ht014a, ht034a, ht124b, hbg4, hbg0c]
                        ·
                          linarith only [hdelta1, h121, h230, ht012c, ht014c, ht234b, hbg0a, hbg4c]
                        ·
                          linarith only [hdelta1, ht014b, ht234e, hbg4c]
                        ·
                          linarith only [hdelta1, ht014a, ht034a, hbg0c, hbg4c]
                        ·
                          linarith only [hdelta1, ht134e, hbg4c]
                        ·
                          linarith only [hdelta1, ht014c, ht034a, ht124b, hbg0c, hbg4c]
                        ·
                          linarith only [hdelta1, ht014a, ht034b, ht124b, hbg0c, hbg4c]
                    ·
                      linarith only [ht023b, ht034a, ht234a]
                  ·
                    linarith only [ht013b, ht034a, ht134a]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                linarith only [ht012c, ht023a, ht123a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  linarith only [ht012a, ht014c, ht124a, ht024b]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb3 := m.budget 3 (by decide) 2 1 4 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc32, hc31, hc30] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht012a, h121, h230, ht013a, hbg3]
                      ·
                        linarith only [hdelta1, ht012a, ht013c, ht034a, ht123e, hbg3]
                      ·
                        linarith only [hdelta1, ht012a, ht013c, ht134a, ht123e, hbg3]
                      ·
                        linarith only [hdelta1, ht034a, ht123b, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht012a, h121, h230, ht013c, ht034a, hbg3c]
                      ·
                        linarith only [hdelta1, ht012a, h121, h230, ht013c, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht012a, h121, h130, ht013c, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht123b, hbg3c]
                      ·
                        linarith only [hdelta1, ht123b, ht134a, hbg3c]
                    ·
                      linarith only [ht123b, ht134a, ht234a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb3 := m.budget 3 (by decide) 2 4 1 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc32, hc31, hc30] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht012a, h121, h230, ht013c, ht034a, hbg3]
                      ·
                        linarith only [hdelta1, ht012a, h121, h230, ht013a, hbg3, ht234a]
                      ·
                        linarith only [hdelta1, ht012a, h121, h230, ht013c, ht134a, hbg3, ht234a]
                      ·
                        linarith only [hdelta1, ht013b, ht134a, hbg3, ht234a]
                      ·
                        linarith only [hdelta1, ht012a, h121, h230, ht013a, hbg3c]
                      ·
                        linarith only [hdelta1, ht012a, h121, h230, ht013c, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht013b, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht012a, h121, h240, ht013c, ht234c, hbg3c]
                      ·
                        linarith only [hdelta1, ht013b, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, ht134a, ht234a, hbg3c]
                    ·
                      have hb3 := m.budget 3 (by decide) 4 2 1 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc32, hc31, hc30] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht012a, h121, h340, ht013a, ht123b, hbg3]
                      ·
                        linarith only [hdelta1, ht012a, h121, h230, ht013a, hbg3]
                      ·
                        linarith only [hdelta1, ht012a, h121, h340, ht013c, ht123b, ht234a, hbg3]
                      ·
                        have hb4 := m.budget 4 (by decide) 3 2 1 0 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc43, hc42, hc41, hc40] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hn, hdelta1, ht034c, hbg4, hbg3, ht024b]
                        ·
                          linarith only [hdelta1, ht012a, h121, h240, ht014a, hbg4]
                        ·
                          linarith only [hdelta1, ht012a, h121, h140, ht013a, ht034c, ht123b, ht234a, hbg4, hbg3]
                        ·
                          have hb0 := m.budget 0 (by decide) 4 3 1 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                          ·
                            linarith only [hdelta1, ht023a, ht024e, hbg0, ht234a, hbg3]
                          ·
                            linarith only [hdelta1, ht012a, h121, h340, ht013b, ht123b, hbg0, ht234a]
                          ·
                            linarith only [hdelta1, h121, h340, ht012c, ht013a, ht123b, hbg0, ht234a]
                          ·
                            have hb2 := m.budget 2 (by decide) 4 3 0 1 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc20, hc21] at hb2
                            rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                              ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                              ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                            ·
                              linarith only [hdelta1, ht012a, h121, h240, ht013a, ht123b, hbg2]
                            ·
                              linarith only [hn, hdelta1, ht034c, hbg0, ht234a, hbg3, hbg2]
                            ·
                              linarith only [hdelta1, h121, h340, ht023a, ht234a, hbg2]
                            ·
                              linarith only [hdelta1, ht012a, ht013a, ht124b, hbg2, ht134c]
                            ·
                              linarith only [hdelta1, ht013b, ht123b, hbg3, hbg2a, ht234b]
                            ·
                              linarith only [hdelta1, ht013b, ht123b, hbg3, hbg2a, ht234b]
                            ·
                              linarith only [hdelta1, ht013b, ht123b, hbg3, hbg2a, ht234b]
                            ·
                              linarith only [hdelta1, ht034c, hbg0, ht234a, hbg3, hbg2a]
                            ·
                              linarith only [hdelta1, ht034c, hbg0, ht234a, hbg3, hbg2a]
                            ·
                              linarith only [hdelta1, ht012b, ht013a, ht124b, ht134c, hbg2c]
                          ·
                            linarith only [hdelta1, ht034b, hbg0a, hbg3]
                          ·
                            linarith only [hdelta1, ht034b, hbg0a, hbg3]
                          ·
                            linarith only [hdelta1, ht034b, hbg0a, hbg3]
                          ·
                            linarith only [hdelta1, h121, h340, ht012c, ht013b, ht123b, ht234a, hbg0c]
                          ·
                            have hb2 := m.budget 2 (by decide) 4 3 0 1 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc20, hc21] at hb2
                            rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                              ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                              ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                            ·
                              linarith only [hdelta1, ht012a, h121, h240, ht023b, hbg2, hbg0a]
                            ·
                              linarith only [hdelta1, ht034c, ht234a, hbg3, hbg2, hbg0b]
                            ·
                              linarith only [hdelta1, h030, h121, ht012b, hbg2, hbg0a]
                            ·
                              linarith only [hdelta1, ht012a, ht034c, hbg2, ht024b, hbg0a]
                            ·
                              linarith only [hdelta1, ht013b, ht123b, hbg3, ht234b, hbg2a]
                            ·
                              linarith only [hdelta1, ht013b, ht123b, hbg3, ht234b, hbg2a]
                            ·
                              linarith only [hdelta1, ht013b, ht123b, hbg3, ht234b, hbg2a]
                            ·
                              linarith only [hdelta1, h121, h340, ht234a, hbg2c]
                            ·
                              linarith only [hdelta1, ht012a, ht034c, ht234c, hbg2c, hbg0c]
                            ·
                              linarith only [hdelta1, ht012b, ht014b, ht034c, ht124b, hbg2c, hbg0a]
                          ·
                            linarith only [hdelta1, ht013a, ht034c, ht134a, hbg3, hbg0c]
                        ·
                          linarith only [hdelta1, ht013b, hbg4a, hbg3, ht134c, hbg4b]
                        ·
                          linarith only [hdelta1, ht034c, hbg4a, hbg3, ht024b]
                        ·
                          linarith only [hdelta1, ht034c, hbg4a, hbg3, ht024b]
                        ·
                          linarith only [hdelta1, ht034c, ht134b, hbg3, hbg4b]
                        ·
                          linarith only [hdelta1, ht014b, ht034c, hbg4a, hbg3, ht234b]
                        ·
                          linarith only [hdelta1, ht034c, ht124b, hbg4a, hbg3, ht234b]
                      ·
                        linarith only [hdelta1, h011, h340, ht013a, hbg3c]
                      ·
                        linarith only [hdelta1, ht012a, h121, h340, ht013c, ht123b, hbg3c]
                      ·
                        have hb0 := m.budget 0 (by decide) 4 3 1 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                        ·
                          linarith only [hdelta1, ht012a, h040, h121, ht013a, ht123b, hbg3c, hbg0]
                        ·
                          linarith only [hdelta1, ht012a, h121, h340, ht013b, ht123b, hbg3a, hbg0]
                        ·
                          linarith only [hdelta1, h021, h340, ht013a, ht123b, hbg3a, hbg0]
                        ·
                          have hb2 := m.budget 2 (by decide) 4 3 0 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc20, hc21] at hb2
                          rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                          ·
                            linarith only [hdelta1, ht012a, h121, h240, ht013a, ht123b, hbg2]
                          ·
                            linarith only [hdelta1, h121, h340, ht012c, hbg3a, hbg2]
                          ·
                            linarith only [hdelta1, h121, h340, ht012b, ht013a, ht123b, hbg3a, hbg2]
                          ·
                            linarith only [hdelta1, ht012a, ht014a, ht124b, hbg2]
                          ·
                            linarith only [hdelta1, ht034c, hbg3c, hbg0, hbg2b]
                          ·
                            linarith only [hdelta1, h121, h240, ht012b, ht013a, ht123b, hbg2c]
                          ·
                            linarith only [hdelta1, ht012a, ht013a, ht123b, hbg2c]
                          ·
                            linarith only [hdelta1, ht034c, hbg3c, hbg0, hbg2a]
                          ·
                            linarith only [hdelta1, ht034c, hbg3c, hbg0, hbg2a]
                          ·
                            linarith only [hdelta1, ht012b, ht014a, ht124b, hbg2c]
                        ·
                          linarith only [hdelta1, ht012a, ht014b, ht124e, hbg0c]
                        ·
                          linarith only [hdelta1, ht012c, ht013c, ht014b, ht124e, hbg0c]
                        ·
                          linarith only [hdelta1, ht012b, ht013a, ht123b, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, h121, h340, ht012c, ht013b, ht123b, hbg0c, hbg3a]
                        ·
                          have hb2 := m.budget 2 (by decide) 4 3 0 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc20, hc21] at hb2
                          rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                          ·
                            linarith only [hdelta1, h011, h340, ht013b, ht123b, hbg2, hbg0a, ht234b]
                          ·
                            linarith only [hdelta1, h021, h340, hbg3a, hbg2]
                          ·
                            linarith only [hdelta1, h030, h121, ht012b, hbg2, hbg0a]
                          ·
                            linarith only [hdelta1, ht012a, ht014b, ht034c, ht124b, hbg2, hbg0a]
                          ·
                            linarith only [hdelta1, ht012a, h121, h340, ht034c, hbg0c, hbg2c, ht234b]
                          ·
                            linarith only [hdelta1, h121, h340, ht012b, ht013b, ht123b, hbg2c, hbg0a, ht234b]
                          ·
                            linarith only [hdelta1, ht012a, ht013b, ht123b, hbg2c, hbg0a]
                          ·
                            linarith only [hdelta1, h121, h340, hbg3a, hbg2c]
                          ·
                            linarith only [hdelta1, ht012a, ht034c, ht234c, hbg0c, hbg2c]
                          ·
                            linarith only [hdelta1, ht012b, ht014b, ht034c, ht124b, hbg2c, hbg0a]
                        ·
                          linarith only [hdelta1, ht013a, ht034c, ht123b, hbg0c, hbg3c]
                      ·
                        linarith only [hdelta1, ht012a, h121, h230, ht013c, hbg3c]
                      ·
                        linarith only [hdelta1, ht013b, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, ht123b, ht234a, hbg3c]
  ·
    rcases m.triangle 0 1 3 (by decide) (by decide) with ⟨ht013a,ht013b,ht013c,ht013d,ht013e⟩ | ⟨ht013a,ht013b,ht013c,ht013d,ht013e⟩
    ·
      rcases m.triangle 0 1 4 (by decide) (by decide) with ⟨ht014a,ht014b,ht014c,ht014d,ht014e⟩ | ⟨ht014a,ht014b,ht014c,ht014d,ht014e⟩
      ·
        rcases m.triangle 0 2 3 (by decide) (by decide) with ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩ | ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb3 := m.budget 3 (by decide) 0 1 2 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc30, hc31, hc32] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht012a, ht013b, ht123d, hbg3]
                      ·
                        linarith only [hdelta1, h120, h341, ht012a, ht013a, ht234a, hbg3]
                      ·
                        linarith only [hdelta1, h120, h341, ht012a, ht013a, ht123c, hbg3]
                      ·
                        have hb4 := m.budget 4 (by decide) 0 1 2 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc40, hc41, hc42, hc43] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, ht012a, ht013b, ht034b, ht124d, hbg4]
                        ·
                          linarith only [hdelta1, h120, h241, ht012a, ht014a, hbg4]
                        ·
                          linarith only [hn, hdelta1, ht034b, ht024c, hbg4, hbg3]
                        ·
                          have hb0 := m.budget 0 (by decide) 2 1 3 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                          ·
                            linarith only [hdelta1, h020, h341, ht013a, ht123c, ht234a, hbg0]
                          ·
                            linarith only [hdelta1, h120, h341, ht012a, ht013c, ht123c, ht234a, hbg0]
                          ·
                            linarith only [hdelta1, ht012a, ht013b, ht014c, ht124d, hbg0]
                          ·
                            have hb2 := m.budget 2 (by decide) 1 0 3 4 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc21, hc20] at hb2
                            rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                              ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                              ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                            ·
                              linarith only [hdelta1, h120, h341, ht012c, ht013a, ht123c, ht234a, hbg2]
                            ·
                              linarith only [hn, hdelta1, ht034b, ht234a, hbg3, hbg0, hbg2]
                            ·
                              linarith only [hn, hdelta1, ht023a, ht034b, ht234c, hbg3, hbg0, hbg2]
                            ·
                              linarith only [hdelta1, ht012a, ht013a, ht124c, ht134b, hbg2]
                            ·
                              linarith only [hdelta1, ht034b, ht234a, hbg2b, hbg3, hbg0]
                            ·
                              linarith only [hdelta1, ht023c, ht234c, hbg2b, hbg3]
                            ·
                              linarith only [hdelta1, ht012c, ht013a, ht124c, ht134b, hbg2c]
                            ·
                              linarith only [hdelta1, ht023c, ht234c, hbg3, hbg2b]
                            ·
                              linarith only [hdelta1, ht034b, ht234a, hbg2a, hbg3, hbg0]
                            ·
                              linarith only [hdelta1, ht023a, ht034b, ht234c, hbg2a, hbg3, hbg0]
                          ·
                            linarith only [hdelta1, ht023d, hbg0c]
                          ·
                            linarith only [hdelta1, ht014c, ht124c, ht234c, hbg3, hbg0b]
                          ·
                            linarith only [hdelta1, ht013a, ht034b, ht134a, hbg0c, hbg3]
                          ·
                            linarith only [hdelta1, ht024c, ht234c, hbg0b, hbg3]
                          ·
                            have hb2 := m.budget 2 (by decide) 1 0 3 4 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc21, hc20] at hb2
                            rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                              ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                              ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                            ·
                              linarith only [hdelta1, h120, h341, ht012c, ht013c, ht123c, hbg2, ht234a, hbg0a]
                            ·
                              linarith only [hdelta1, ht034b, hbg2, ht234a, hbg0b, hbg3]
                            ·
                              linarith only [hdelta1, h120, h241, ht012a, ht023a, ht034b, hbg2, hbg0c]
                            ·
                              linarith only [hdelta1, ht012a, ht024a, ht034b, hbg2, hbg0c]
                            ·
                              linarith only [hdelta1, h120, h341, ht234a, hbg2c]
                            ·
                              linarith only [hdelta1, ht013c, ht123c, ht234c, hbg3, hbg2b]
                            ·
                              linarith only [hdelta1, ht012c, ht014c, ht034b, ht124c, hbg2c, hbg0a]
                            ·
                              linarith only [hdelta1, ht013c, ht123c, ht234c, hbg2b, hbg3]
                            ·
                              linarith only [hdelta1, ht012a, ht034b, ht234b, hbg2c, hbg0c]
                            ·
                              linarith only [hdelta1, ht013c, ht123c, ht234c, hbg2a, hbg3]
                          ·
                            linarith only [hdelta1, ht034c, hbg3, hbg0a]
                        ·
                          linarith only [hdelta1, ht034b, ht134c, hbg4a, hbg3]
                        ·
                          linarith only [hdelta1, ht034b, ht134c, hbg4a, hbg3]
                        ·
                          linarith only [hdelta1, ht034b, ht134c, hbg4a, hbg3]
                        ·
                          linarith only [hdelta1, ht014c, ht034b, hbg4a, hbg3, hbg4b]
                        ·
                          linarith only [hdelta1, ht014c, ht034b, ht234c, hbg4a, hbg3]
                        ·
                          linarith only [hdelta1, ht034b, ht024c, hbg4a, hbg3]
                      ·
                        linarith only [hdelta1, h120, h341, ht012a, ht013b, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, h120, h341, ht012a, ht013b, ht123c, hbg3c]
                      ·
                        linarith only [hdelta1, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, h120, h341, ht012a, ht013a, hbg3c]
                      ·
                        linarith only [hdelta1, ht013c, ht234a, hbg3c]
                      ·
                        have hb0 := m.budget 0 (by decide) 2 1 3 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                        ·
                          linarith only [hdelta1, ht012b, ht013a, ht123d, hbg0]
                        ·
                          linarith only [hdelta1, h120, h341, ht012a, ht013c, ht123c, hbg0, hbg3a]
                        ·
                          linarith only [hdelta1, ht012a, ht013b, ht014c, ht124d, hbg0]
                        ·
                          have hb2 := m.budget 2 (by decide) 1 0 3 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc21, hc20] at hb2
                          rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                          ·
                            linarith only [hdelta1, ht012c, ht013a, ht123d, hbg2]
                          ·
                            linarith only [hdelta1, h020, h341, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, h120, h341, ht012a, ht013a, ht123c, hbg2, ht234c]
                          ·
                            linarith only [hdelta1, ht012a, ht014a, ht124c, hbg2]
                          ·
                            linarith only [hdelta1, ht034b, hbg0, hbg3c, hbg2b]
                          ·
                            linarith only [hdelta1, h120, h241, ht012c, ht013a, ht123c, hbg2c]
                          ·
                            linarith only [hdelta1, ht012c, ht014a, ht124c, hbg2c]
                          ·
                            linarith only [hdelta1, ht034b, hbg0, hbg3c, hbg2a]
                          ·
                            linarith only [hdelta1, ht034b, hbg0, hbg3c, hbg2a]
                          ·
                            linarith only [hdelta1, ht012b, ht023a, hbg2c]
                        ·
                          linarith only [hdelta1, h020, h341, ht013c, ht123c, hbg3a, hbg0c]
                        ·
                          linarith only [hdelta1, ht012b, ht013b, ht014c, ht124d, hbg0c]
                        ·
                          linarith only [hdelta1, ht013a, ht034b, ht123c, hbg3c, hbg0c]
                        ·
                          linarith only [hdelta1, ht012a, ht014c, ht124d, hbg0c]
                        ·
                          have hb2 := m.budget 2 (by decide) 1 0 3 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc21, hc20] at hb2
                          rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                          ·
                            linarith only [hdelta1, h031, h120, ht012c, hbg2, hbg0a]
                          ·
                            linarith only [hdelta1, h020, h341, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, h120, h241, ht012a, ht013c, ht123c, hbg2, hbg0a]
                          ·
                            linarith only [hdelta1, ht012a, ht024a, ht034b, hbg2, hbg0c]
                          ·
                            linarith only [hdelta1, h120, h341, hbg3a, hbg2c]
                          ·
                            linarith only [hdelta1, h120, h341, ht012c, ht013c, ht123c, ht234c, hbg2c, hbg0a]
                          ·
                            linarith only [hdelta1, ht024a, hbg2c]
                          ·
                            linarith only [hdelta1, h120, h341, ht012a, ht034b, ht234c, hbg2c, hbg0c]
                          ·
                            linarith only [hdelta1, ht012a, ht034b, ht234b, hbg2c, hbg0c]
                          ·
                            linarith only [hdelta1, ht012a, ht013c, ht123c, hbg2c, hbg0a]
                        ·
                          linarith only [hdelta1, ht012c, ht013a, ht123c, hbg3c, hbg0c]
                    ·
                      have hb3 := m.budget 3 (by decide) 0 1 4 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc30, hc31, hc32] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, h120, h341, ht012a, ht013b, hbg3, ht134a]
                      ·
                        linarith only [hdelta1, h120, h231, ht012a, ht013a, hbg3, ht234a]
                      ·
                        linarith only [hdelta1, h120, h231, ht012a, ht013a, hbg3, ht134a]
                      ·
                        linarith only [hdelta1, ht013c, hbg3, ht134a, ht234a]
                      ·
                        linarith only [hdelta1, h120, h231, ht012a, ht013b, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, h120, h231, ht012a, ht013b, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht134a, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, h120, h231, ht012a, ht013a, hbg3c]
                      ·
                        linarith only [hdelta1, ht013c, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, hbg3c]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht123c, ht234a, ht134a]
                    ·
                      have hb3 := m.budget 3 (by decide) 0 4 1 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc30, hc31, hc32] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, h120, h131, ht012a, ht013b, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht012a, ht013b, ht034a, ht123d, hbg3]
                      ·
                        linarith only [hdelta1, h010, h231, ht013b, ht034a, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht034a, ht123c, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht012a, ht013b, ht123d, hbg3c]
                      ·
                        linarith only [hdelta1, h120, h231, ht012a, ht013b, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht123c, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, h120, h231, ht012a, ht014b, ht034c, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht123c, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht134a, hbg3c]
                ·
                  linarith only [ht012b, ht024a, ht124a]
              ·
                linarith only [ht012b, ht023a, ht123a]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht034a, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht013c, ht123c, ht034a, ht234a]
                    ·
                      have hb0 := m.budget 0 (by decide) 2 1 4 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                      ·
                        linarith only [hdelta1, ht012b, ht013a, ht123d, hbg0]
                      ·
                        linarith only [hdelta1, ht012a, ht014c, ht123d, ht134c, hbg0]
                      ·
                        linarith only [hdelta1, ht012a, ht014b, ht013c, ht123d, hbg0]
                      ·
                        have hb2 := m.budget 2 (by decide) 1 0 4 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc21, hc20] at hb2
                        rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                        ·
                          linarith only [hdelta1, ht012c, ht013a, ht123d, hbg2]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc31, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, ht234d, hbg2, hbg0, hbg3]
                          ·
                            linarith only [hdelta1, ht012a, ht013b, ht123d, hbg3]
                          ·
                            linarith only [hdelta1, h120, h231, ht012a, ht013a, hbg3]
                          ·
                            linarith only [hn, hdelta1, ht034a, ht234c, hbg2, hbg0, hbg3]
                          ·
                            linarith only [hdelta1, hbg3a, ht234d, hbg2, hbg0]
                          ·
                            linarith only [hdelta1, hbg3a, ht234d, hbg2, hbg0]
                          ·
                            linarith only [hdelta1, hbg3a, ht234d, hbg2, hbg0]
                          ·
                            linarith only [hdelta1, h120, h231, ht012a, ht014b, hbg3c, ht034c]
                          ·
                            linarith only [hdelta1, ht034a, ht234c, hbg2, hbg0, hbg3b]
                          ·
                            linarith only [hdelta1, ht034a, ht234c, hbg2, hbg0, hbg3b]
                        ·
                          linarith only [hdelta1, h120, h231, ht012a, ht014a, ht124c, hbg2]
                        ·
                          linarith only [hdelta1, ht012a, ht013a, ht123c, hbg2]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc31, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, hbg2b, ht234d, hbg0, hbg3]
                          ·
                            linarith only [hdelta1, ht012c, ht013b, ht123d, hbg2a, hbg3]
                          ·
                            linarith only [hdelta1, h120, h231, ht012c, ht013a, hbg2a, hbg3]
                          ·
                            linarith only [hdelta1, ht013c, ht123d, ht034a, ht234c, hbg2c, hbg3]
                          ·
                            linarith only [hdelta1, ht123d, ht234d, hbg2c, hbg3c]
                          ·
                            linarith only [hdelta1, h120, h231, ht013c, ht234d, hbg2c, hbg3c]
                          ·
                            linarith only [hdelta1, hbg2b, ht234c, hbg0, hbg3c]
                          ·
                            linarith only [hdelta1, h120, h231, ht012c, ht014b, hbg2a, ht034c, hbg3c]
                          ·
                            linarith only [hdelta1, h120, h131, ht034a, ht234c, hbg2c, hbg3c]
                          ·
                            linarith only [hdelta1, ht013c, ht034a, hbg3c]
                        ·
                          linarith only [hdelta1, h120, h231, ht012c, ht014a, ht124c, hbg2c]
                        ·
                          linarith only [hdelta1, ht023a, hbg2c]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc31, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, h231, h340, hbg3, hbg0, hbg2c]
                          ·
                            linarith only [hdelta1, ht012a, ht013b, ht123d, hbg3]
                          ·
                            linarith only [hdelta1, h120, h231, ht012a, ht013a, hbg3]
                          ·
                            linarith only [hdelta1, ht023d, ht034a, hbg3, hbg2c]
                          ·
                            linarith only [hdelta1, h231, h340, hbg3a, hbg0, hbg2c]
                          ·
                            linarith only [hdelta1, h231, h340, hbg3a, hbg0, hbg2c]
                          ·
                            linarith only [hdelta1, h231, h340, hbg3a, hbg0, hbg2c]
                          ·
                            linarith only [hdelta1, h120, h231, ht012a, ht013b, hbg3c]
                          ·
                            linarith only [hdelta1, ht034a, hbg0, hbg2c, hbg3b]
                          ·
                            linarith only [hdelta1, ht034a, hbg0, hbg2c, hbg3b]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc31, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht234d, hbg0, hbg3, hbg2a]
                          ·
                            linarith only [hdelta1, ht012a, ht014b, ht123c, ht034c, hbg3, hbg2b]
                          ·
                            linarith only [hdelta1, ht012a, ht013a, hbg3, hbg2b]
                          ·
                            linarith only [hdelta1, ht034a, ht234c, hbg0, hbg3, hbg2a]
                          ·
                            linarith only [hdelta1, ht012b, ht123c, ht234d, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht012b, ht013c, ht234d, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht234c, hbg3c, hbg0, hbg2a]
                          ·
                            linarith only [hdelta1, h120, h231, ht012a, ht014b, hbg3c, ht034c]
                          ·
                            linarith only [hdelta1, ht123c, ht034a, hbg3c]
                          ·
                            linarith only [hdelta1, ht013c, ht034a, hbg3c]
                        ·
                          linarith only [hdelta1, ht012b, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012b, ht013c, ht123d, ht034c, hbg0c]
                      ·
                        linarith only [hdelta1, ht012b, ht014b, ht013c, ht123d, hbg0c]
                      ·
                        have hb4 := m.budget 4 (by decide) 3 0 1 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc43, hc40, hc41, hc42] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, ht014a, ht124c, ht234d, ht034c, hbg4, hbg0c]
                        ·
                          linarith only [hdelta1, h020, h231, ht014b, ht123c, ht134c, hbg4, hbg0a]
                        ·
                          linarith only [hdelta1, h120, h241, ht012b, ht014a, hbg4, hbg0a]
                        ·
                          linarith only [hdelta1, ht014a, ht124c, ht034a, hbg4, hbg0c]
                        ·
                          linarith only [hdelta1, ht134d, hbg4c]
                        ·
                          linarith only [hdelta1, ht014c, ht234d, hbg4c]
                        ·
                          linarith only [hdelta1, ht014a, ht124c, ht034c, hbg0c, hbg4c]
                        ·
                          linarith only [hdelta1, h020, h231, ht014b, ht234c, hbg0a, hbg4c]
                        ·
                          linarith only [hdelta1, ht014b, ht124c, ht034a, hbg0c, hbg4c]
                        ·
                          linarith only [hdelta1, ht014a, ht034a, hbg0c, hbg4c]
                      ·
                        linarith only [hdelta1, h031, h120, ht012a, hbg0c]
                      ·
                        have hb2 := m.budget 2 (by decide) 1 0 4 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc21, hc20] at hb2
                        rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                        ·
                          linarith only [hdelta1, h041, h120, ht012c, hbg2, hbg0a]
                        ·
                          have hb4 := m.budget 4 (by decide) 3 0 1 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc43, hc40, hc41, hc42] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, hbg2, ht234d, hbg4, ht034c, hbg0b]
                          ·
                            linarith only [hdelta1, h120, h141, ht012a, hbg4, hbg0a]
                          ·
                            linarith only [hdelta1, h120, h241, ht012a, ht014c, hbg4, hbg0a]
                          ·
                            linarith only [hdelta1, hbg2, ht034a, hbg4, hbg0b]
                          ·
                            linarith only [hdelta1, ht134d, hbg4c]
                          ·
                            linarith only [hdelta1, ht014c, ht234d, hbg4c]
                          ·
                            linarith only [hdelta1, hbg2, hbg4c, ht034c, hbg0b]
                          ·
                            linarith only [hdelta1, h120, h231, ht012a, ht234c, hbg4c, hbg0a]
                          ·
                            linarith only [hdelta1, ht012c, ht124c, ht034a, hbg4c, hbg0c]
                          ·
                            linarith only [hdelta1, ht012c, ht014c, ht034a, hbg4c, hbg0c]
                        ·
                          linarith only [hdelta1, h120, h231, ht012a, ht024c, hbg2, hbg0a]
                        ·
                          linarith only [hdelta1, ht012a, ht023c, hbg2, ht034c, hbg0a]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc31, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht013c, ht123d, ht234d, hbg3, hbg2c]
                          ·
                            linarith only [hdelta1, ht012c, ht013b, ht123d, hbg3, hbg2a]
                          ·
                            linarith only [hdelta1, h010, h231, ht013c, hbg3, ht034c, hbg0a]
                          ·
                            linarith only [hdelta1, ht013c, ht123d, ht034a, ht234c, hbg3, hbg2c]
                          ·
                            linarith only [hdelta1, h231, h340, ht123d, ht234c, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, h120, h231, ht013c, ht234d, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht013c, ht123d, ht234c, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, h120, h231, ht012c, ht034c, hbg0a, hbg3c, hbg2a]
                          ·
                            linarith only [hdelta1, ht123c, ht034a, hbg3c]
                          ·
                            linarith only [hdelta1, ht013c, ht034a, hbg3c]
                        ·
                          linarith only [hdelta1, h120, h231, ht024a, hbg2c]
                        ·
                          linarith only [hdelta1, ht023a, hbg2c]
                        ·
                          linarith only [hdelta1, h120, h231, ht012a, ht034c, hbg0c, hbg2c]
                        ·
                          linarith only [hdelta1, ht012a, ht234c, ht034c, hbg0c, hbg2c]
                        ·
                          linarith only [hdelta1, ht012a, ht014c, ht124c, hbg0a, hbg2c]
                      ·
                        have hb2 := m.budget 2 (by decide) 1 0 4 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc21, hc20] at hb2
                        rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                        ·
                          linarith only [hdelta1, ht012c, ht013a, ht123d, hbg2]
                        ·
                          have hb4 := m.budget 4 (by decide) 3 0 1 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc43, hc40, hc41, hc42] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hn, hdelta1, h231, h340, ht234c, hbg2, hbg0c, hbg4]
                          ·
                            linarith only [hdelta1, ht012a, ht014b, ht124d, hbg4]
                          ·
                            linarith only [hdelta1, h120, h231, ht012a, ht014a, ht234c, hbg4]
                          ·
                            linarith only [hdelta1, ht034b, hbg0b, hbg0a, hbg2, hbg4]
                          ·
                            linarith only [hdelta1, ht234d, hbg4a, hbg2, hbg0c]
                          ·
                            linarith only [hdelta1, ht234d, hbg4a, hbg2, hbg0c]
                          ·
                            linarith only [hdelta1, hbg4a, hbg2, hbg4b, hbg0c]
                          ·
                            linarith only [hdelta1, h120, h231, ht012a, ht014b, ht234c, hbg4c]
                          ·
                            linarith only [hdelta1, ht034b, hbg4b, hbg2, hbg0c]
                          ·
                            linarith only [hdelta1, ht034b, hbg4b, hbg2, hbg0c]
                        ·
                          linarith only [hdelta1, h120, h231, ht012a, ht014b, ht024a, hbg2, hbg0c]
                        ·
                          linarith only [hdelta1, ht012a, ht014b, ht023c, hbg0a, hbg2]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc30, hc31, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht013c, ht123d, ht234d, hbg2c, hbg3]
                          ·
                            linarith only [hdelta1, ht012c, ht013b, ht123d, hbg2a, hbg3]
                          ·
                            linarith only [hdelta1, h120, h231, ht012c, ht013a, hbg2a, hbg3]
                          ·
                            linarith only [hdelta1, ht023c, ht034b, hbg0a, hbg3]
                          ·
                            linarith only [hdelta1, h231, h340, ht123d, ht234c, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, h120, h231, ht013c, ht234d, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht013c, ht123d, ht234c, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, h120, h231, ht012c, ht014b, hbg2a, hbg0a, hbg3c]
                          ·
                            linarith only [hdelta1, ht034b, ht123c, hbg0a, hbg3c]
                          ·
                            linarith only [hdelta1, ht034b, ht013c, hbg0a, hbg3c]
                        ·
                          linarith only [hdelta1, h120, h231, ht024a, hbg2c]
                        ·
                          linarith only [hdelta1, ht023a, hbg2c]
                        ·
                          linarith only [hdelta1, h120, h231, ht012a, ht014b, hbg2c, hbg0c]
                        ·
                          linarith only [hdelta1, ht012a, ht014b, ht234c, hbg2c, hbg0c]
                        ·
                          linarith only [hdelta1, ht012a, ht014a, ht124c, hbg2c]
                ·
                  linarith only [ht012b, ht024a, ht124a]
              ·
                linarith only [ht012b, ht023a, ht123a]
          ·
            linarith only [ht012c, ht014b, ht024c]
        ·
          linarith only [ht012c, ht013b, ht023c]
      ·
        rcases m.triangle 0 2 3 (by decide) (by decide) with ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩ | ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              linarith only [ht013b, ht014c, ht034b]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht034a, ht013c, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht013a, ht014a, ht123c, ht234a, ht134b]
                    ·
                      have hb0 := m.budget 0 (by decide) 2 4 1 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                      ·
                        linarith only [hdelta1, ht012b, ht013a, ht014c, ht123d, hbg0]
                      ·
                        linarith only [hdelta1, ht012b, ht013a, ht024b, ht123d, hbg0]
                      ·
                        linarith only [hdelta1, ht012a, ht013c, ht123d, hbg0]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc30, hc31, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          have hb2 := m.budget 2 (by decide) 1 0 4 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc21, hc20] at hb2
                          rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                          ·
                            linarith only [hdelta1, ht013a, ht014c, ht024b, ht123d, hbg2]
                          ·
                            linarith only [hn, hdelta1, hbg2, ht234d, hbg0, hbg3]
                          ·
                            linarith only [hn, hdelta1, h231, h340, ht024a, hbg2, hbg0, hbg3]
                          ·
                            linarith only [hdelta1, ht013a, ht014a, ht123c, hbg2, ht124b]
                          ·
                            linarith only [hdelta1, ht234d, hbg2b, hbg0, hbg3]
                          ·
                            linarith only [hdelta1, h231, h340, ht024a, hbg2b, hbg0, hbg3]
                          ·
                            linarith only [hdelta1, ht013a, ht014c, ht024b, ht123c, hbg2c]
                          ·
                            linarith only [hdelta1, h231, h340, hbg2b, hbg2a, hbg0, hbg3]
                          ·
                            linarith only [hdelta1, ht234d, hbg2a, hbg0, hbg3]
                          ·
                            linarith only [hdelta1, h231, h340, ht024a, hbg2a, hbg0, hbg3]
                        ·
                          linarith only [hdelta1, ht012a, ht013b, ht123d, hbg3]
                        ·
                          linarith only [hdelta1, h120, h231, ht013a, ht014a, hbg3, ht124b]
                        ·
                          linarith only [hdelta1, ht013a, ht014a, ht123c, hbg3, ht134b]
                        ·
                          have hb2 := m.budget 2 (by decide) 1 0 4 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc21, hc20] at hb2
                          rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                          ·
                            linarith only [hdelta1, ht012c, ht013a, ht123d, hbg2]
                          ·
                            linarith only [hdelta1, ht012b, ht123d, hbg3c, hbg2, ht234d]
                          ·
                            linarith only [hdelta1, h231, h340, ht012b, ht024a, ht123d, hbg3c, hbg2]
                          ·
                            linarith only [hdelta1, ht013a, ht014a, ht123c, hbg2, ht124b]
                          ·
                            linarith only [hdelta1, ht123d, hbg3c, ht234d, hbg2c]
                          ·
                            linarith only [hdelta1, h231, h340, ht024a, ht123d, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht013b, ht014c, ht024b, ht123c, hbg3b, hbg2c]
                          ·
                            linarith only [hdelta1, h231, h340, ht012b, ht123d, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht012b, ht123c, hbg3c, ht234d, hbg2c]
                          ·
                            linarith only [hdelta1, ht012b, ht024a, hbg2c]
                        ·
                          have hb2 := m.budget 2 (by decide) 1 0 4 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc21, hc20] at hb2
                          rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                          ·
                            linarith only [hdelta1, h120, h231, ht013a, ht014c, ht024b, hbg2, hbg3b]
                          ·
                            linarith only [hdelta1, hbg3a, hbg2, ht234d, hbg0]
                          ·
                            linarith only [hdelta1, h231, h340, ht024a, hbg3a, hbg2, hbg0]
                          ·
                            linarith only [hdelta1, ht013a, ht014a, hbg2, ht124b, hbg3b]
                          ·
                            linarith only [hdelta1, h120, h231, ht013c, ht234d, hbg2c, hbg3c]
                          ·
                            linarith only [hdelta1, h120, h231, ht024a, hbg2c]
                          ·
                            linarith only [hdelta1, ht013a, ht014c, ht024b, hbg2c, hbg3b]
                          ·
                            linarith only [hdelta1, h231, h340, hbg3a, hbg0, hbg2c]
                          ·
                            linarith only [hdelta1, ht013a, ht014a, ht234d, hbg0, hbg2c, hbg3c, ht124b]
                          ·
                            linarith only [hdelta1, h231, h340, ht013a, ht024a, ht014a, hbg0, hbg2c, hbg3c, ht124b]
                        ·
                          have hb2 := m.budget 2 (by decide) 1 0 4 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc21, hc20] at hb2
                          rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                          ·
                            linarith only [hdelta1, ht013a, ht014c, ht024b, ht123d, hbg2]
                          ·
                            linarith only [hn, hdelta1, ht234c, hbg2, hbg0, hbg3c]
                          ·
                            linarith only [hdelta1, ht024a, hbg2, hbg3b, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, ht013a, ht014a, ht123c, hbg2, ht124b]
                          ·
                            linarith only [hdelta1, ht234c, hbg2b, hbg0, hbg3c]
                          ·
                            linarith only [hdelta1, ht024a, hbg2b, hbg0, hbg3c]
                          ·
                            linarith only [hdelta1, ht012c, ht013a, ht123c, hbg2c]
                          ·
                            linarith only [hdelta1, hbg2a, hbg2b, hbg0, hbg3c]
                          ·
                            linarith only [hdelta1, ht234c, hbg2a, hbg0, hbg3c]
                          ·
                            linarith only [hdelta1, ht024a, hbg2a, hbg0, hbg3c]
                        ·
                          linarith only [hdelta1, h231, h340, ht013b, ht014a, ht134b, hbg3c]
                        ·
                          linarith only [hdelta1, ht013b, ht014a, ht123c, ht134b, hbg3c]
                        ·
                          linarith only [hdelta1, ht013a, ht014a, ht134b, hbg3c]
                      ·
                        linarith only [hdelta1, h120, h131, ht012b, ht013a, hbg0c]
                      ·
                        linarith only [hdelta1, ht014c, ht023d, hbg0c]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc30, hc31, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          have hb4 := m.budget 4 (by decide) 3 1 0 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc43, hc41, hc40, hc42] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h131, h340, ht013a, ht014a, hbg4]
                          ·
                            linarith only [hdelta1, ht013a, ht014c, ht123d, hbg4, ht124b]
                          ·
                            linarith only [hdelta1, h241, h340, hbg0b, hbg3, hbg0a, hbg4]
                          ·
                            linarith only [hdelta1, ht024a, hbg0b, hbg3, hbg4]
                          ·
                            linarith only [hdelta1, h231, h340, ht013a, ht014c, ht123c, hbg4c]
                          ·
                            linarith only [hdelta1, hbg0c, ht234d, hbg4b, hbg3]
                          ·
                            linarith only [hdelta1, ht024c, hbg0c, hbg4b, hbg3]
                          ·
                            linarith only [hdelta1, h241, h340, hbg0c, hbg4b, hbg3]
                          ·
                            linarith only [hdelta1, ht024c, hbg0c, hbg4b, hbg3]
                          ·
                            linarith only [hdelta1, hbg4a, hbg0c, hbg4b, hbg3]
                        ·
                          linarith only [hdelta1, ht012a, ht013b, ht123d, hbg3]
                        ·
                          linarith only [hdelta1, h120, h231, ht012a, ht013a, hbg3]
                        ·
                          linarith only [hdelta1, ht013a, ht014a, ht123c, hbg3, ht134b]
                        ·
                          have hb2 := m.budget 2 (by decide) 1 0 4 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc21, hc20] at hb2
                          rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                          ·
                            linarith only [hdelta1, h041, h120, hbg0a, hbg2]
                          ·
                            linarith only [hdelta1, ht012b, ht123d, ht234d, hbg3c, hbg2]
                          ·
                            linarith only [hdelta1, h231, h340, ht012b, ht024a, ht123d, hbg3c, hbg2]
                          ·
                            linarith only [hdelta1, ht012b, ht013b, ht014c, ht023c, hbg0a, hbg2]
                          ·
                            linarith only [hdelta1, h241, h340, ht123d, hbg2c, hbg3c]
                          ·
                            linarith only [hdelta1, h231, h340, ht024a, ht123d, hbg2c, hbg3c]
                          ·
                            linarith only [hdelta1, ht013b, ht014c, ht123c, hbg3b, hbg2c, hbg0a]
                          ·
                            linarith only [hdelta1, h231, h340, ht012b, ht123d, hbg2c, hbg3c]
                          ·
                            linarith only [hdelta1, ht012b, ht123c, ht234d, hbg2c, hbg3c]
                          ·
                            linarith only [hdelta1, ht012b, ht024a, hbg2c]
                        ·
                          linarith only [hdelta1, h231, h340, ht013a, ht014c, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, ht013a, ht014c, ht123c, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, h020, h231, ht013b, ht014c, hbg3c, hbg0a]
                        ·
                          linarith only [hdelta1, ht034a, ht123c, hbg3c]
                        ·
                          linarith only [hdelta1, ht013a, ht014a, hbg3c, ht134b]
                      ·
                        linarith only [hdelta1, ht023d, ht024b, hbg0c]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 0 1 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc30, hc31, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          have hb4 := m.budget 4 (by decide) 3 1 0 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc43, hc41, hc40, hc42] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h231, h340, ht013a, ht014a, ht123c, hbg4]
                          ·
                            linarith only [hdelta1, h140, h231, ht013a, ht123c, hbg0a, hbg4]
                          ·
                            linarith only [hdelta1, ht024b, ht234d, hbg4, hbg3, hbg0b]
                          ·
                            linarith only [hdelta1, ht024a, hbg4, hbg3, hbg0b]
                          ·
                            linarith only [hdelta1, h231, h340, ht013a, ht123c, hbg0a, hbg4c]
                          ·
                            linarith only [hdelta1, ht014b, ht234d, hbg4c]
                          ·
                            linarith only [hdelta1, ht013b, ht014b, ht024a, hbg4c, hbg0c]
                          ·
                            linarith only [hdelta1, ht124e, hbg4c]
                          ·
                            linarith only [hdelta1, ht013a, ht024a, ht123d, hbg4c, hbg0c, hbg3, ht124b]
                          ·
                            linarith only [hdelta1, ht024b, hbg4c, hbg3, hbg0b]
                        ·
                          linarith only [hdelta1, ht012a, ht013b, ht123d, hbg3]
                        ·
                          linarith only [hdelta1, h120, h231, ht012b, ht013a, ht024b, hbg0a, hbg3]
                        ·
                          linarith only [hdelta1, ht013b, ht023c, ht034b, hbg0a, hbg3]
                        ·
                          have hb2 := m.budget 2 (by decide) 1 0 4 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc21, hc20] at hb2
                          rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                          ·
                            linarith only [hdelta1, ht012c, ht013b, ht123d, hbg3b, hbg2]
                          ·
                            linarith only [hdelta1, ht012b, ht123d, hbg2, ht234d, hbg3c]
                          ·
                            linarith only [hdelta1, h231, h340, ht012b, ht024a, ht123d, hbg2, hbg3c]
                          ·
                            linarith only [hdelta1, ht013b, ht014b, ht023c, hbg2, hbg0a, ht124b]
                          ·
                            linarith only [hdelta1, h241, h340, ht123d, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, h231, h340, ht024a, ht123d, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht013b, ht024b, ht123c, hbg3b, hbg0a, hbg2c]
                          ·
                            linarith only [hdelta1, h231, h340, ht012b, ht123d, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht012b, ht123c, ht234d, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht012b, ht024a, hbg2c]
                        ·
                          linarith only [hdelta1, h231, h340, ht013a, ht024b, hbg3c, hbg0c]
                        ·
                          linarith only [hdelta1, ht013a, ht024b, ht123c, hbg3c, hbg0c]
                        ·
                          linarith only [hdelta1, h120, h231, ht012a, ht013b, hbg3c]
                        ·
                          linarith only [hdelta1, ht013b, ht014b, ht123c, hbg3c, hbg0a, ht134b]
                        ·
                          linarith only [hdelta1, ht013a, ht014b, hbg3c, hbg0a, ht134b]
                      ·
                        have hb4 := m.budget 4 (by decide) 3 1 0 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc43, hc41, hc40, hc42] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, h231, h340, ht014a, ht013c, ht123c, hbg4, hbg0a]
                        ·
                          linarith only [hdelta1, h140, h231, ht014c, ht013c, ht123c, hbg4, hbg0a]
                        ·
                          linarith only [hdelta1, ht024b, ht014a, hbg4, ht234d, hbg0c, ht134b]
                        ·
                          linarith only [hdelta1, ht024a, ht014a, hbg4, hbg0c, ht134b]
                        ·
                          linarith only [hdelta1, h231, h340, ht014c, ht013c, ht123c, hbg0a, hbg4c]
                        ·
                          linarith only [hdelta1, ht014b, ht234d, hbg4c]
                        ·
                          linarith only [hdelta1, ht024a, ht014a, hbg0c, hbg4c]
                        ·
                          linarith only [hdelta1, ht124e, hbg4c]
                        ·
                          linarith only [hdelta1, ht014c, ht024a, hbg0c, ht134b, hbg4c]
                        ·
                          linarith only [hdelta1, ht024b, ht014a, hbg0c, ht134b, hbg4c]
                ·
                  linarith only [ht012b, ht024a, ht124a]
              ·
                linarith only [ht012b, ht023a, ht123a]
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              linarith only [ht012c, ht013b, ht034b, ht024c]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013a, ht014c, ht034b, ht134a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht013a, ht014a, ht134b, ht234a, ht123c]
                    ·
                      have hb2 := m.budget 2 (by decide) 1 4 0 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, ht012c, ht013a, ht123d, ht024a, hbg2]
                      ·
                        linarith only [hdelta1, ht012c, ht013a, ht124a, ht123d, hbg2]
                      ·
                        linarith only [hdelta1, h120, h231, ht124a, ht024a, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht124a, ht024a, hbg2]
                      ·
                        linarith only [hdelta1, ht012c, ht013a, ht123d, hbg2c]
                      ·
                        linarith only [hdelta1, h120, h231, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012c, ht013a, ht024a, hbg2c, ht123c]
                      ·
                        linarith only [hdelta1, h120, h231, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht124a, ht024a, hbg2c]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht013c, ht134a, ht034a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht013a, ht014a, ht134b, ht234a, ht123c]
                    ·
                      have hb2 := m.budget 2 (by decide) 4 1 0 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, ht012a, ht013a, hbg2, ht234e, ht123c]
                      ·
                        linarith only [hdelta1, ht012c, ht013a, ht123d, hbg2]
                      ·
                        linarith only [hdelta1, ht012b, ht124a, hbg2, ht234e]
                      ·
                        linarith only [hdelta1, ht012a, ht013a, ht124a, hbg2, ht123c]
                      ·
                        linarith only [hdelta1, ht012c, ht013a, hbg2c, ht234e, ht123c]
                      ·
                        linarith only [hdelta1, ht012b, hbg2c, ht234e]
                      ·
                        linarith only [hdelta1, ht012b, ht023a, hbg2c]
                      ·
                        linarith only [hdelta1, h231, h340, ht124a, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012b, ht124a, hbg2c]
              ·
                linarith only [ht012b, ht023a, ht123a]
        ·
          linarith only [ht012c, ht013b, ht023c]
    ·
      rcases m.triangle 0 1 4 (by decide) (by decide) with ⟨ht014a,ht014b,ht014c,ht014d,ht014e⟩ | ⟨ht014a,ht014b,ht014c,ht014d,ht014e⟩
      ·
        rcases m.triangle 0 2 3 (by decide) (by decide) with ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩ | ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb0 := m.budget 0 (by decide) 2 3 1 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                      ·
                        linarith only [hdelta1, ht012b, ht013c, ht014a, hbg0, ht124d]
                      ·
                        linarith only [hdelta1, ht013b, ht014a, ht123b, hbg0, ht124d]
                      ·
                        linarith only [hdelta1, ht012a, ht014c, hbg0, ht124d]
                      ·
                        have hb2 := m.budget 2 (by decide) 1 0 3 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc21, hc20] at hb2
                        rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                        ·
                          linarith only [hdelta1, ht013c, ht014a, ht023b, hbg2, ht124d]
                        ·
                          have hb4 := m.budget 4 (by decide) 0 1 2 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc40, hc41, hc42, hc43] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, ht013a, ht014b, ht123b, ht124d, hbg4]
                          ·
                            linarith only [hdelta1, h120, h241, ht013a, ht014a, ht123b, hbg4]
                          ·
                            linarith only [hdelta1, h120, h341, ht013a, ht014a, ht123b, ht124c, hbg4]
                          ·
                            linarith only [hn, hdelta1, hbg0, hbg2, ht234a, hbg4]
                          ·
                            linarith only [hdelta1, h120, h341, ht013a, ht014b, ht123b, ht234c, hbg4c]
                          ·
                            linarith only [hdelta1, h020, h341, hbg4b, ht234b, hbg2]
                          ·
                            linarith only [hdelta1, hbg4b, hbg0, hbg2, ht234a]
                          ·
                            linarith only [hdelta1, h120, h341, ht012b, hbg4b, ht234b, hbg2]
                          ·
                            linarith only [hdelta1, hbg4b, hbg0, hbg2, ht234a]
                          ·
                            linarith only [hdelta1, hbg4b, hbg0, hbg2, ht234a]
                        ·
                          have hb4 := m.budget 4 (by decide) 0 1 2 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc40, hc41, hc42, hc43] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, ht013a, ht014b, ht123b, hbg4, ht124d]
                          ·
                            linarith only [hdelta1, h120, h341, ht013a, ht014a, ht123b, ht234c, hbg4]
                          ·
                            linarith only [hdelta1, h120, h341, ht013a, ht014a, ht123b, ht124c, hbg4]
                          ·
                            linarith only [hn, hdelta1, ht023a, ht234c, hbg4, hbg0, hbg2]
                          ·
                            linarith only [hdelta1, h120, h341, ht013a, ht014b, ht123b, ht234c, hbg4c]
                          ·
                            linarith only [hdelta1, h120, h341, ht012b, ht023a, hbg2, hbg4b]
                          ·
                            linarith only [hdelta1, ht023a, ht234c, hbg0, hbg2, hbg4b]
                          ·
                            linarith only [hdelta1, h120, h341, ht012b, ht023a, hbg2, hbg4b]
                          ·
                            linarith only [hdelta1, ht023a, ht234c, hbg0, hbg2, hbg4b]
                          ·
                            linarith only [hdelta1, ht023a, hbg0, hbg4a, hbg2, hbg4b]
                        ·
                          linarith only [hdelta1, ht013a, ht014a, ht123b, ht124c, hbg2]
                        ·
                          linarith only [hdelta1, h120, h341, hbg2c, ht234a]
                        ·
                          linarith only [hdelta1, h120, h341, ht023a, ht234c, hbg2c]
                        ·
                          linarith only [hdelta1, ht024a, hbg2c]
                        ·
                          have hb4 := m.budget 4 (by decide) 0 1 2 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc40, hc41, hc42, hc43] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, ht012a, ht014b, hbg4, ht124d]
                          ·
                            linarith only [hdelta1, h120, h341, ht013a, ht014a, ht123b, ht234c, hbg4]
                          ·
                            linarith only [hdelta1, h120, h341, ht012b, hbg2a, hbg2b, hbg4]
                          ·
                            linarith only [hdelta1, ht234c, hbg2a, hbg0, hbg2b, hbg4]
                          ·
                            linarith only [hdelta1, h120, h341, ht013a, ht014b, ht123b, ht234c, hbg4c]
                          ·
                            linarith only [hdelta1, h120, h341, ht012b, hbg4b, hbg2c]
                          ·
                            linarith only [hdelta1, ht234c, hbg4b, hbg0, hbg2c]
                          ·
                            linarith only [hdelta1, h120, h341, ht012b, hbg4b, hbg2c]
                          ·
                            linarith only [hdelta1, ht234c, hbg4b, hbg0, hbg2c]
                          ·
                            linarith only [hdelta1, hbg4b, hbg0, hbg2c, hbg4a]
                        ·
                          have hb4 := m.budget 4 (by decide) 0 1 2 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc40, hc41, hc42, hc43] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, ht013a, ht014b, ht123b, hbg4, ht124d]
                          ·
                            linarith only [hdelta1, ht013a, ht014a, ht123b, hbg2b, hbg4]
                          ·
                            linarith only [hdelta1, h120, h341, ht013a, ht014a, ht123b, ht124c, hbg4]
                          ·
                            linarith only [hdelta1, hbg0, hbg2a, hbg4, ht234a]
                          ·
                            linarith only [hdelta1, ht013a, ht014b, ht123b, hbg2b, hbg4c]
                          ·
                            linarith only [hdelta1, h120, h341, ht013a, ht014b, ht123b, ht124c, hbg4c]
                          ·
                            linarith only [hdelta1, ht012b, ht124c, hbg4c, hbg2c, ht234a]
                          ·
                            linarith only [hdelta1, h120, h341, ht013a, ht014a, ht123b, hbg4c]
                          ·
                            linarith only [hdelta1, ht013a, ht014a, ht123b, hbg4c, hbg0, hbg2c, ht234a]
                          ·
                            linarith only [hdelta1, ht234b, hbg4c, hbg0, hbg2a]
                        ·
                          linarith only [hdelta1, ht012b, ht023a, hbg2c]
                      ·
                        linarith only [hdelta1, h120, h141, ht012b, ht014a, hbg0c]
                      ·
                        linarith only [hdelta1, ht012b, ht013c, ht014c, hbg0c, ht124d]
                      ·
                        have hb3 := m.budget 3 (by decide) 1 0 2 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc31, hc30, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, ht013c, ht014a, ht123b, hbg3, ht124d]
                        ·
                          linarith only [hdelta1, h020, h231, hbg3, hbg0a]
                        ·
                          linarith only [hdelta1, h120, h341, ht012b, ht023c, hbg3, hbg0a]
                        ·
                          linarith only [hdelta1, ht013a, ht014a, ht234c, hbg3, ht124c]
                        ·
                          linarith only [hdelta1, h130, h341, hbg3c, ht234a]
                        ·
                          have hb4 := m.budget 4 (by decide) 0 1 2 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc40, hc41, hc42, hc43] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h120, h241, ht013c, ht014b, ht123b, hbg4, ht124c, hbg3a]
                          ·
                            linarith only [hdelta1, h120, h241, ht013c, ht014a, ht123b, hbg4, hbg3a]
                          ·
                            linarith only [hdelta1, h120, h341, ht013c, ht014b, ht024c, ht123b, hbg4, hbg3a]
                          ·
                            linarith only [hdelta1, ht023c, hbg4, hbg0c, hbg3b]
                          ·
                            linarith only [hdelta1, h120, h341, ht013c, ht014b, ht123b, ht234c, hbg3a, hbg4c]
                          ·
                            linarith only [hdelta1, h120, h341, ht013c, ht014b, ht123b, ht124c, hbg3a, hbg4c]
                          ·
                            linarith only [hdelta1, ht123b, ht023c, hbg3c, ht124d, hbg4c]
                          ·
                            linarith only [hdelta1, h120, h341, ht013c, ht014a, ht123b, hbg3a, hbg4c]
                          ·
                            linarith only [hdelta1, ht013c, ht014a, ht234c, hbg0c, hbg4c]
                          ·
                            linarith only [hdelta1, ht013c, ht014a, hbg0c, ht124c, hbg4c]
                        ·
                          linarith only [hdelta1, ht034a, hbg3c]
                        ·
                          linarith only [hdelta1, h020, h341, hbg0a, hbg3c]
                        ·
                          linarith only [hdelta1, ht013a, ht014b, hbg0c, ht234a, hbg3c]
                        ·
                          linarith only [hdelta1, ht013a, ht014b, ht023c, hbg0c, hbg3c]
                      ·
                        linarith only [hdelta1, ht012b, ht014c, ht023b, hbg0c, ht124d]
                      ·
                        have hb4 := m.budget 4 (by decide) 0 1 2 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc40, hc41, hc42, hc43] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, h120, h141, ht012b, ht014b, ht023b, hbg0a, hbg4]
                        ·
                          linarith only [hdelta1, h120, h341, ht012b, ht014a, ht023b, hbg0a, ht234c, hbg4]
                        ·
                          linarith only [hdelta1, h120, h341, ht012b, ht014b, ht023b, ht024c, hbg0a, hbg4]
                        ·
                          have hb3 := m.budget 3 (by decide) 1 0 2 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc30, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h041, h130, ht014b, hbg0a, hbg3]
                          ·
                            linarith only [hdelta1, ht023b, hbg3, hbg4, hbg0b, ht234a]
                          ·
                            linarith only [hdelta1, ht023a, hbg3, hbg4, hbg0b]
                          ·
                            linarith only [hdelta1, ht013b, ht014b, ht034c, hbg0a, hbg3]
                          ·
                            linarith only [hdelta1, ht123e, hbg3c]
                          ·
                            linarith only [hdelta1, h120, h341, ht014b, ht023a, ht123b, hbg0c, hbg3c]
                          ·
                            linarith only [hdelta1, ht014b, ht024a, ht234c, hbg0c, hbg3c]
                          ·
                            linarith only [hdelta1, ht023b, hbg4, hbg0b, hbg3c]
                          ·
                            linarith only [hdelta1, ht013b, ht234a, hbg3c]
                          ·
                            linarith only [hdelta1, ht013b, ht014b, ht023a, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, h120, h341, ht012b, ht014b, ht023b, hbg0a, ht234c, hbg4c]
                        ·
                          linarith only [hdelta1, h120, h341, ht012b, ht014b, ht023b, hbg0a, ht124c, hbg4c]
                        ·
                          have hb2 := m.budget 2 (by decide) 1 0 3 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc21, hc20] at hb2
                          rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                          ·
                            linarith only [hdelta1, ht012c, ht014b, hbg2, hbg4a, ht124d]
                          ·
                            linarith only [hdelta1, ht012b, hbg2, hbg4c, ht124d, ht234a]
                          ·
                            linarith only [hdelta1, ht012b, ht023a, ht234c, hbg2, hbg4c, ht124d]
                          ·
                            linarith only [hdelta1, ht012b, ht014b, ht023b, ht024c, hbg0a, hbg2]
                          ·
                            linarith only [hdelta1, hbg4c, hbg2c, ht124d, ht234a]
                          ·
                            linarith only [hdelta1, h120, h241, ht023a, hbg2c]
                          ·
                            linarith only [hdelta1, ht014b, ht023b, hbg0a, ht124c, hbg2c, hbg4a]
                          ·
                            linarith only [hdelta1, ht012b, ht234c, hbg4c, hbg2c, ht124d]
                          ·
                            linarith only [hdelta1, ht012b, ht124c, hbg4c, hbg2c, ht234a]
                          ·
                            linarith only [hdelta1, ht012b, ht023a, hbg2c]
                        ·
                          linarith only [hdelta1, h120, h341, ht012b, ht014a, ht023b, hbg0a, hbg4c]
                        ·
                          linarith only [hdelta1, ht014a, ht023b, ht234c, hbg0c, hbg4c]
                        ·
                          linarith only [hdelta1, ht014a, ht023b, hbg0c, ht124c, hbg4c]
                      ·
                        have hb2 := m.budget 2 (by decide) 1 0 3 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc21, hc20] at hb2
                        rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                        ·
                          linarith only [hdelta1, h041, h120, ht012c, hbg2, hbg0a]
                        ·
                          linarith only [hdelta1, h120, h341, ht013a, ht123b, hbg2, hbg0c, ht234a]
                        ·
                          linarith only [hdelta1, h120, h241, ht013a, ht023a, ht123b, hbg2, hbg0c]
                        ·
                          linarith only [hdelta1, ht013a, ht024c, ht123b, hbg2, hbg0a]
                        ·
                          linarith only [hdelta1, h120, h341, hbg2c, ht234a]
                        ·
                          linarith only [hdelta1, h120, h241, ht023a, hbg2c]
                        ·
                          linarith only [hdelta1, ht013c, ht014c, ht023b, ht124c, hbg0a, hbg2c]
                        ·
                          linarith only [hdelta1, h120, h341, ht013a, ht123b, ht234c, hbg0c, hbg2c]
                        ·
                          linarith only [hdelta1, ht013a, ht123b, hbg0c, ht234b, hbg2c]
                        ·
                          linarith only [hdelta1, ht013a, ht023a, ht123b, hbg0c, hbg2c]
                    ·
                      have hb3 := m.budget 3 (by decide) 1 0 4 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc31, hc30, hc32] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht013c, ht014a, ht123e, ht234c, ht124c, hbg3]
                      ·
                        linarith only [hdelta1, ht013b, ht123e, ht234a, hbg3]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, ht123e, ht134c, hbg3]
                      ·
                        linarith only [hdelta1, ht013a, ht014a, ht234a, ht134c, hbg3]
                      ·
                        linarith only [hdelta1, ht123e, hbg3c, ht234a]
                      ·
                        linarith only [hdelta1, ht034a, ht123e, hbg3c]
                      ·
                        linarith only [hdelta1, ht013c, ht014a, hbg3c, ht234a, ht134c]
                      ·
                        linarith only [hdelta1, ht023e, hbg3c]
                      ·
                        linarith only [hdelta1, ht013b, hbg3c, ht234a]
                      ·
                        linarith only [hdelta1, ht013b, ht034a, hbg3c]
                  ·
                    linarith only [ht013a, ht014b, ht034c, ht134a]
                ·
                  linarith only [ht012b, ht024a, ht124a]
              ·
                linarith only [ht012b, ht023a, ht123a]
            ·
              linarith only [ht013c, ht014b, ht034c]
          ·
            linarith only [ht013c, ht014b, ht023b, ht024c]
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 1 3 0 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h120, h141, ht012c, ht014a, ht023a, hbg2]
                      ·
                        linarith only [hdelta1, ht012c, ht014a, ht123a, ht124d, hbg2]
                      ·
                        linarith only [hdelta1, h120, h241, ht023a, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, ht012c, ht014a, ht124d, hbg2c]
                      ·
                        linarith only [hdelta1, h120, h341, ht023a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, h120, h341, ht123a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht123a, hbg2c]
                    ·
                      linarith only [ht023b, ht034a, ht234a]
                  ·
                    linarith only [ht012c, ht014b, ht023a, ht034c, ht123c, ht134a]
                ·
                  linarith only [ht023a, ht024a, ht123a, ht124a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 3 1 0 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h141, h230, ht012a, ht014a, hbg2]
                      ·
                        linarith only [hdelta1, ht012c, ht014a, ht123a, ht124c, ht234d, hbg2]
                      ·
                        linarith only [hdelta1, ht012b, ht123a, ht234d, hbg2]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, ht123a, ht124c, hbg2]
                      ·
                        linarith only [hdelta1, h230, h341, ht012c, ht014a, ht124c, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht012b, ht234d, hbg2c]
                      ·
                        linarith only [hdelta1, ht012a, ht014a, ht124c, hbg2c]
                      ·
                        linarith only [hdelta1, h230, h341, ht123a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht012c, ht014a, ht123a, ht124c, hbg2c]
                      ·
                        linarith only [hdelta1, ht012b, ht123a, hbg2c]
                    ·
                      linarith only [ht013b, ht034a, ht123b, ht234a]
                  ·
                    linarith only [ht013a, ht014b, ht034c, ht134a]
                ·
                  linarith only [ht012b, ht024a, ht124a]
            ·
              linarith only [ht012c, ht014b, ht023c, ht034c]
          ·
            linarith only [ht012c, ht014b, ht024c]
      ·
        rcases m.triangle 0 2 3 (by decide) (by decide) with ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩ | ⟨ht023a,ht023b,ht023c,ht023d,ht023e⟩
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 1 0 3 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h120, h341, ht023a, ht234a, hbg2]
                      ·
                        have hb3 := m.budget 3 (by decide) 1 0 2 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc31, hc30, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          have hb4 := m.budget 4 (by decide) 1 0 2 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc41, hc40, hc42, hc43] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, ht012e, ht014c, ht234a, hbg4, hbg2, ht134e]
                          ·
                            linarith only [hn, hdelta1, h120, h341, ht034b, ht123b, ht234c, hbg4, hbg3]
                          ·
                            linarith only [hn, hdelta1, h120, h341, ht024c, ht034b, ht123b, hbg4, hbg3]
                          ·
                            linarith only [hdelta1, ht012e, ht014a, ht234a, hbg4, hbg2]
                          ·
                            linarith only [hdelta1, h120, h241, ht034b, ht123b, hbg3, hbg4b]
                          ·
                            linarith only [hdelta1, h120, h341, ht024c, ht034b, ht123b, hbg3, hbg4b]
                          ·
                            linarith only [hdelta1, ht012e, ht014c, ht234a, hbg4c, hbg2]
                          ·
                            linarith only [hdelta1, h120, h341, ht012b, hbg2, hbg4b, ht234b]
                          ·
                            linarith only [hdelta1, h120, h241, ht034b, ht123b, hbg3, hbg4a]
                          ·
                            linarith only [hdelta1, h120, h341, ht024c, ht034b, ht123b, hbg3, hbg4a]
                        ·
                          have hb0 := m.budget 0 (by decide) 2 3 4 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                          ·
                            linarith only [hn, hdelta1, h120, h231, ht012b, hbg3, hbg0]
                          ·
                            have hb4 := m.budget 4 (by decide) 1 0 2 3 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc41, hc40, hc42, hc43] at hb4
                            rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                            ·
                              linarith only [hdelta1, ht012e, ht014c, ht234a, hbg2, ht134e, hbg4]
                            ·
                              linarith only [hn, hdelta1, h120, h341, ht012b, ht023b, ht234c, hbg0, hbg4]
                            ·
                              linarith only [hn, hdelta1, h120, h341, ht012b, ht023b, ht024c, hbg0, hbg4]
                            ·
                              linarith only [hdelta1, ht012e, ht014a, ht023b, ht234a, hbg3, hbg4]
                            ·
                              linarith only [hdelta1, h120, h241, ht012b, ht023b, hbg0, hbg4b]
                            ·
                              linarith only [hdelta1, h120, h341, ht012b, ht023b, hbg3, ht234b, hbg4b]
                            ·
                              linarith only [hdelta1, ht012e, ht014c, ht234a, hbg2, hbg4c]
                            ·
                              linarith only [hdelta1, h120, h341, ht012b, ht023b, hbg3, hbg4b, ht234b]
                            ·
                              linarith only [hdelta1, h120, h241, ht012b, ht023b, hbg0, hbg4a]
                            ·
                              linarith only [hdelta1, h120, h341, ht012b, ht023b, ht024c, hbg0, hbg4a]
                          ·
                            linarith only [hdelta1, ht012e, ht014b, ht234a, hbg2, hbg0, ht134e]
                          ·
                            linarith only [hdelta1, ht014a, ht023b, ht234a, hbg3, hbg0, ht134e]
                          ·
                            linarith only [hdelta1, h120, h231, ht012b, hbg3, hbg0a]
                          ·
                            linarith only [hdelta1, h120, h231, ht012b, hbg3, hbg0a]
                          ·
                            linarith only [hdelta1, h120, h231, ht012b, hbg3, hbg0a]
                          ·
                            linarith only [hdelta1, ht013e, hbg0c]
                          ·
                            have hb4 := m.budget 4 (by decide) 1 0 2 3 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc41, hc40, hc42, hc43] at hb4
                            rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                            ·
                              linarith only [hdelta1, h140, h341, ht014c, ht023b, ht234a, hbg4, hbg3, hbg0b]
                            ·
                              linarith only [hdelta1, h020, h241, ht023b, hbg4, hbg0a]
                            ·
                              linarith only [hdelta1, h120, h341, ht012b, ht023b, ht024c, hbg4, hbg0a]
                            ·
                              linarith only [hdelta1, ht014a, ht023b, ht234a, hbg4, hbg3, hbg0b]
                            ·
                              linarith only [hdelta1, ht234c, hbg4c, ht134e]
                            ·
                              linarith only [hdelta1, h120, h341, ht012b, ht023b, hbg3, hbg4b, ht234b]
                            ·
                              linarith only [hdelta1, ht014c, ht234a, hbg2, hbg0b, hbg4c]
                            ·
                              linarith only [hdelta1, h020, h341, ht023b, hbg3, hbg4b, ht234b]
                            ·
                              linarith only [hdelta1, ht014a, ht023b, ht234c, hbg0c, hbg4c]
                            ·
                              linarith only [hdelta1, h020, h341, ht023b, hbg3, hbg4a, ht234b]
                          ·
                            linarith only [hdelta1, ht014b, ht023b, ht234a, hbg3, ht134e, hbg0c]
                        ·
                          linarith only [hn, hdelta1, h120, h341, ht012b, hbg2, hbg3]
                        ·
                          linarith only [hdelta1, ht012e, ht014a, ht234a, hbg2, ht134b, hbg3]
                        ·
                          linarith only [hdelta1, h120, h341, ht234a, ht123b, hbg3c]
                        ·
                          linarith only [hdelta1, h120, h341, ht012b, hbg2, hbg3b]
                        ·
                          linarith only [hdelta1, ht012e, ht014c, ht034b, ht234a, hbg2, hbg3c]
                        ·
                          linarith only [hdelta1, h120, h341, ht012b, hbg2, hbg3b]
                        ·
                          linarith only [hdelta1, ht013b, ht234a, hbg3c]
                        ·
                          linarith only [hdelta1, h020, h341, hbg2, hbg3a]
                      ·
                        have hb3 := m.budget 3 (by decide) 1 0 2 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc31, hc30, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hn, hdelta1, h120, h341, ht023c, ht123b, ht234c, hbg2, hbg3]
                        ·
                          linarith only [hn, hdelta1, h030, h341, ht234c, hbg2, hbg3]
                        ·
                          have hb0 := m.budget 0 (by decide) 2 3 4 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                          ·
                            linarith only [hn, hdelta1, h120, h341, ht012b, ht023c, ht234c, hbg2, hbg0]
                          ·
                            have hb4 := m.budget 4 (by decide) 1 0 2 3 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc41, hc40, hc42, hc43] at hb4
                            rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                            ·
                              linarith only [hdelta1, ht012e, ht014c, ht023a, hbg2, ht124e, hbg4]
                            ·
                              linarith only [hn, hdelta1, h020, h341, ht023b, ht234c, hbg0, hbg4]
                            ·
                              linarith only [hn, hdelta1, h230, h341, hbg2, hbg4]
                            ·
                              linarith only [hdelta1, ht012e, ht014a, ht023a, ht234c, hbg2, hbg4]
                            ·
                              linarith only [hdelta1, h120, h241, ht012b, ht023b, hbg0, hbg4b]
                            ·
                              linarith only [hdelta1, h120, h341, ht012b, ht023b, ht024c, hbg0, hbg4b]
                            ·
                              linarith only [hdelta1, ht012e, ht014c, ht023a, ht234c, hbg2, hbg4c]
                            ·
                              linarith only [hdelta1, h120, h341, ht012b, ht023a, hbg2, hbg4b]
                            ·
                              linarith only [hdelta1, h120, h241, ht012b, ht023b, hbg0, hbg4a]
                            ·
                              linarith only [hdelta1, h120, h341, ht012b, ht023b, ht024c, hbg0, hbg4a]
                          ·
                            linarith only [hdelta1, ht012e, ht023a, ht024e, hbg2, hbg0]
                          ·
                            linarith only [hdelta1, ht014a, ht023a, ht234c, hbg2, hbg0, ht134e]
                          ·
                            linarith only [hdelta1, h120, h241, ht012b, ht023c, hbg2, hbg0a]
                          ·
                            linarith only [hdelta1, h120, h241, ht012b, ht023c, hbg2, hbg0a]
                          ·
                            linarith only [hdelta1, h120, h241, ht012b, ht023c, hbg2, hbg0a]
                          ·
                            linarith only [hdelta1, ht012e, ht023b, hbg0c]
                          ·
                            have hb4 := m.budget 4 (by decide) 1 0 2 3 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc41, hc40, hc42, hc43] at hb4
                            rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                              ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                            ·
                              linarith only [hdelta1, ht014c, ht023a, ht234c, hbg2, ht134e, hbg4, hbg0b]
                            ·
                              linarith only [hdelta1, h120, h241, ht012b, ht023b, hbg4, hbg0a]
                            ·
                              linarith only [hdelta1, h120, h341, ht012b, ht023b, ht024c, hbg4, hbg0a]
                            ·
                              linarith only [hdelta1, ht014a, ht023a, ht234c, hbg2, hbg4, hbg0b]
                            ·
                              linarith only [hdelta1, ht234c, hbg4c, ht134e]
                            ·
                              linarith only [hdelta1, h120, h341, ht012b, ht023a, hbg2, hbg4b]
                            ·
                              linarith only [hdelta1, ht014c, ht023a, ht234c, hbg2, hbg0b, hbg4c]
                            ·
                              linarith only [hdelta1, h020, h341, ht023a, hbg2, hbg4b]
                            ·
                              linarith only [hdelta1, ht014a, ht023b, ht234c, hbg4c, hbg0c]
                            ·
                              linarith only [hdelta1, h020, h341, ht023a, hbg2, hbg4a]
                          ·
                            linarith only [hdelta1, ht023a, ht024e, hbg2, hbg0c]
                        ·
                          linarith only [hdelta1, ht012e, ht013a, ht023a, ht234c, hbg2, hbg3]
                        ·
                          linarith only [hdelta1, h130, h241, hbg2, hbg3a, hbg3b]
                        ·
                          linarith only [hdelta1, h130, h341, ht023c, ht234c, hbg2, hbg3a]
                        ·
                          linarith only [hdelta1, h130, h341, ht023c, ht234c, hbg2, hbg3a]
                        ·
                          linarith only [hdelta1, h030, h341, ht234c, hbg2, hbg3a]
                        ·
                          linarith only [hdelta1, h030, h341, ht234c, hbg2, hbg3a]
                        ·
                          linarith only [hdelta1, ht013b, ht023c, ht234c, hbg2, hbg3b]
                      ·
                        have hb0 := m.budget 0 (by decide) 2 3 4 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                        ·
                          linarith only [hn, hdelta1, ht012b, ht024c, ht034b, hbg2, hbg0]
                        ·
                          linarith only [hn, hdelta1, ht012b, ht023b, ht024c, hbg2, hbg0]
                        ·
                          have hb3 := m.budget 3 (by decide) 1 0 2 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc30, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, ht023c, ht123b, hbg3, hbg2, ht234b]
                          ·
                            linarith only [hn, hdelta1, ht013b, ht123b, hbg3, hbg2, ht234b]
                          ·
                            linarith only [hdelta1, ht012e, ht023a, ht034e, hbg3, hbg0]
                          ·
                            linarith only [hdelta1, ht012e, ht013b, ht023a, ht034b, ht234a, hbg3, hbg0]
                          ·
                            linarith only [hdelta1, ht012b, ht023b, hbg2, ht234b, hbg3b]
                          ·
                            linarith only [hdelta1, h011, h130, ht034b, hbg3a, hbg0]
                          ·
                            linarith only [hdelta1, h011, h130, ht034b, hbg3a, hbg0]
                          ·
                            linarith only [hdelta1, ht012b, ht013e, ht024b, hbg2, hbg3a, hbg0, ht234b]
                          ·
                            linarith only [hdelta1, ht012b, ht013e, ht024b, hbg2, hbg3a, hbg0, ht234b]
                          ·
                            linarith only [hdelta1, ht012e, ht013b, ht023a, ht034b, hbg3c, hbg0]
                        ·
                          have hb3 := m.budget 3 (by decide) 1 0 2 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc30, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, ht023c, ht123b, hbg2, hbg3, ht234b]
                          ·
                            linarith only [hn, hdelta1, ht013b, ht123b, hbg2, hbg3, ht234b]
                          ·
                            linarith only [hdelta1, ht014a, ht023a, hbg0, ht134e, hbg3]
                          ·
                            linarith only [hdelta1, ht014a, ht023a, ht234a, ht134b, hbg0, hbg3]
                          ·
                            linarith only [hdelta1, ht013c, ht024a, ht123b, hbg2, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, ht013c, ht024a, ht123b, hbg2, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, ht013c, ht024a, ht123b, hbg2, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, ht012b, ht023b, hbg2, hbg3a, ht234b]
                          ·
                            linarith only [hdelta1, ht012b, ht023b, hbg2, hbg3a, ht234b]
                          ·
                            linarith only [hdelta1, ht014a, ht023a, ht134b, hbg0, hbg3c]
                        ·
                          linarith only [hdelta1, ht012b, ht024c, hbg0b, hbg2, hbg0a]
                        ·
                          linarith only [hdelta1, ht012b, ht024c, ht034b, hbg2, hbg0a]
                        ·
                          linarith only [hdelta1, ht012b, ht024c, ht034b, hbg2, hbg0a]
                        ·
                          linarith only [hdelta1, ht012b, ht023b, ht024c, hbg2, hbg0a]
                        ·
                          linarith only [hdelta1, ht012b, ht023b, ht024c, hbg2, hbg0a]
                        ·
                          have hb3 := m.budget 3 (by decide) 1 0 2 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc30, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h011, h130, ht034b, hbg3, hbg0a]
                          ·
                            linarith only [hdelta1, ht023b, ht034e, ht234a, hbg3, hbg0c]
                          ·
                            linarith only [hdelta1, ht014b, ht023a, hbg3, ht134e, hbg0c]
                          ·
                            linarith only [hdelta1, ht013b, ht023a, ht034b, ht234a, hbg3, hbg0c]
                          ·
                            linarith only [hdelta1, ht034b, ht024a, ht123b, hbg2, hbg0c, hbg3a]
                          ·
                            linarith only [hdelta1, ht034b, ht024a, ht123b, hbg2, hbg0c, hbg3a]
                          ·
                            linarith only [hdelta1, ht034b, ht024a, ht123b, hbg2, hbg0c, hbg3a]
                          ·
                            linarith only [hdelta1, ht013b, ht123b, hbg2, ht234b, hbg3a]
                          ·
                            linarith only [hdelta1, ht013b, ht123b, hbg2, ht234b, hbg3a]
                          ·
                            linarith only [hdelta1, ht013b, ht023a, ht034b, hbg3c, hbg0c]
                      ·
                        linarith only [hdelta1, h120, h341, ht234a, hbg2c]
                      ·
                        linarith only [hdelta1, h120, h341, ht023a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, hbg2c]
                      ·
                        have hb4 := m.budget 4 (by decide) 1 0 2 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc41, hc40, hc42, hc43] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, ht012e, ht014c, hbg4, ht124e, hbg2c]
                        ·
                          have hb0 := m.budget 0 (by decide) 2 3 4 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                          ·
                            linarith only [hn, hdelta1, h120, h341, ht012b, ht034b, hbg4, ht234c, hbg0]
                          ·
                            linarith only [hdelta1, h030, h120, h341, ht012b, hbg4, ht234c, hbg2b, hbg0, hbg2a]
                          ·
                            linarith only [hdelta1, ht012e, ht014b, ht234c, ht134e, hbg0, hbg2c]
                          ·
                            linarith only [hdelta1, ht014a, ht234c, ht134e, hbg0, hbg2c]
                          ·
                            linarith only [hdelta1, h120, h241, ht012b, hbg4, hbg0a, hbg0b]
                          ·
                            linarith only [hdelta1, h120, h341, ht012b, ht034b, hbg4, ht234c, hbg0a]
                          ·
                            linarith only [hdelta1, h120, h341, ht012b, ht034b, hbg4, ht234c, hbg0a]
                          ·
                            linarith only [hdelta1, h030, h341, hbg4, ht234c, hbg0a]
                          ·
                            linarith only [hdelta1, h030, h341, hbg4, ht234c, hbg0a]
                          ·
                            linarith only [hdelta1, ht014b, ht234c, ht134e, hbg0c, hbg2c]
                        ·
                          linarith only [hdelta1, h120, h341, ht012b, hbg4, hbg2b, hbg2a]
                        ·
                          linarith only [hdelta1, ht012e, ht014a, hbg4, ht234c, hbg2c]
                        ·
                          linarith only [hdelta1, ht234c, ht134e, hbg4c]
                        ·
                          linarith only [hdelta1, h120, h341, ht012b, hbg4b, hbg2c]
                        ·
                          linarith only [hdelta1, ht012e, ht014c, ht234c, hbg4c, hbg2c]
                        ·
                          linarith only [hdelta1, h120, h341, ht012b, hbg4b, hbg2c]
                        ·
                          have hb0 := m.budget 0 (by decide) 2 3 4 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                          ·
                            linarith only [hdelta1, h020, h341, ht023c, ht234c, hbg2b, hbg0]
                          ·
                            linarith only [hdelta1, h030, h341, ht234c, hbg4a, hbg0]
                          ·
                            linarith only [hdelta1, ht012e, ht014b, ht234c, hbg4b, hbg2c, hbg0]
                          ·
                            linarith only [hdelta1, ht014a, ht234c, hbg4b, hbg2c, hbg0]
                          ·
                            linarith only [hdelta1, ht012e, ht014c, hbg0c]
                          ·
                            linarith only [hdelta1, ht012e, ht034b, hbg0c]
                          ·
                            linarith only [hdelta1, ht014a, ht034b, ht234c, hbg0c, hbg4c]
                          ·
                            linarith only [hdelta1, ht012e, ht023b, hbg0c]
                          ·
                            linarith only [hdelta1, ht014a, ht023b, ht234c, hbg0c, hbg4c]
                          ·
                            linarith only [hdelta1, ht014b, ht234c, hbg0c, hbg4b, hbg2c]
                        ·
                          linarith only [hdelta1, h120, h341, ht012b, hbg2c, hbg4a]
                      ·
                        have hb4 := m.budget 4 (by decide) 1 0 2 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc41, hc40, hc42, hc43] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, ht024c, ht124b, hbg2b, hbg4]
                        ·
                          linarith only [hdelta1, ht014b, ht123b, ht134b, hbg2b, hbg4]
                        ·
                          linarith only [hdelta1, h020, h341, hbg2a, hbg4, ht234b]
                        ·
                          have hb0 := m.budget 0 (by decide) 2 3 4 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                          ·
                            linarith only [hdelta1, ht012b, ht014b, ht024c, ht034a, hbg0, hbg2b, hbg4]
                          ·
                            linarith only [hdelta1, ht012b, ht023b, ht024c, hbg0, hbg2b]
                          ·
                            linarith only [hdelta1, ht012e, ht014b, ht234a, hbg0, hbg2a, hbg4]
                          ·
                            linarith only [hdelta1, ht014a, ht234a, hbg0, hbg2a, hbg4]
                          ·
                            linarith only [hdelta1, ht012b, ht024c, hbg0c, hbg2b]
                          ·
                            linarith only [hdelta1, ht012e, ht014b, ht023c, ht234a, hbg0c, hbg4]
                          ·
                            linarith only [hdelta1, ht014a, ht034a, hbg0c, hbg4]
                          ·
                            linarith only [hdelta1, ht013e, hbg0c]
                          ·
                            have hb3 := m.budget 3 (by decide) 1 0 2 4 (by decide)
                              (by linarith)
                              (by linarith)
                              (by linarith)
                            simp only [hc31, hc30, hc32] at hb3
                            rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                              ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                              ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                            ·
                              linarith only [hdelta1, h011, h130, ht012b, ht014a, ht024c, ht234a, hbg0c, hbg3, hbg2a, hbg4, hbg2c]
                            ·
                              linarith only [hdelta1, ht013e, ht014a, ht234a, hbg3, hbg4]
                            ·
                              linarith only [hdelta1, ht014a, hbg3, hbg0b, hbg2a, hbg4]
                            ·
                              linarith only [hdelta1, ht012b, ht013b, ht014a, ht024c, ht234a, hbg0c, hbg3, hbg2a, hbg4, hbg2c]
                            ·
                              linarith only [hdelta1, ht014c, ht123b, hbg0c, hbg2c, ht234b, hbg3a]
                            ·
                              linarith only [hdelta1, ht014c, ht123b, hbg0c, hbg2c, ht234b, hbg3a]
                            ·
                              linarith only [hdelta1, ht014c, ht123b, hbg0c, hbg2c, ht234b, hbg3a]
                            ·
                              linarith only [hdelta1, ht012b, ht014b, ht024c, hbg3b, hbg4, hbg2c]
                            ·
                              linarith only [hdelta1, ht013b, ht234a, hbg3c]
                            ·
                              linarith only [hdelta1, ht012b, ht014a, ht023b, ht024c, hbg3a, hbg0c, hbg4, hbg2c]
                          ·
                            linarith only [hdelta1, ht014b, ht234a, hbg0c, hbg2a, hbg4]
                        ·
                          linarith only [hdelta1, h120, h341, ht012b, ht234a, ht123b, ht134b, hbg4c, hbg2c]
                        ·
                          linarith only [hdelta1, ht024c, hbg4c, ht134e]
                        ·
                          linarith only [hdelta1, ht012b, ht024c, ht234a, hbg4c, hbg2c]
                        ·
                          linarith only [hdelta1, ht014b, hbg4c, ht134e]
                        ·
                          linarith only [hdelta1, ht012b, ht014b, ht234a, hbg4c, hbg2c]
                        ·
                          have hb0 := m.budget 0 (by decide) 2 3 4 1 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                            ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                          ·
                            linarith only [hdelta1, h120, h341, ht012b, ht023c, hbg4a, hbg0, ht234b]
                          ·
                            linarith only [hdelta1, h030, h341, ht024c, hbg4a, hbg0]
                          ·
                            linarith only [hdelta1, ht012e, ht014b, hbg4c, hbg2a, hbg0, ht234b]
                          ·
                            linarith only [hdelta1, ht014a, hbg4c, hbg2a, hbg0, ht234b]
                          ·
                            linarith only [hdelta1, h120, h341, ht012b, ht024c, hbg4a, hbg0c]
                          ·
                            linarith only [hdelta1, ht012e, ht034b, hbg0c]
                          ·
                            linarith only [hdelta1, ht014a, ht024c, ht034b, hbg4c, hbg0c]
                          ·
                            linarith only [hdelta1, ht013e, hbg0c]
                          ·
                            linarith only [hdelta1, ht014a, ht023b, ht024c, hbg4c, hbg0c]
                          ·
                            linarith only [hdelta1, ht014b, ht024a, hbg4c, hbg0c]
                      ·
                        linarith only [hdelta1, ht012b, ht023a, hbg2c]
                    ·
                      have hb3 := m.budget 3 (by decide) 1 0 4 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc31, hc30, hc32] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht034a, ht123e, ht234a, hbg3]
                      ·
                        linarith only [hdelta1, ht013b, ht123e, ht234a, hbg3]
                      ·
                        linarith only [hdelta1, ht013b, ht034a, ht123e, hbg3]
                      ·
                        linarith only [hdelta1, ht013b, ht034a, ht234a, hbg3]
                      ·
                        linarith only [hdelta1, ht123e, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht123e, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, ht023e, hbg3c]
                      ·
                        linarith only [hdelta1, ht013b, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, ht013b, ht034a, hbg3c]
                  ·
                    linarith only [ht013b, ht034a, ht134a]
                ·
                  linarith only [ht012b, ht024a, ht124a]
              ·
                linarith only [ht012b, ht023a, ht123a]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht023c, ht034a, ht234a]
                    ·
                      have hb3 := m.budget 3 (by decide) 1 4 0 2 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc31, hc30, hc32] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht013d, ht034a, hbg3]
                      ·
                        linarith only [hdelta1, ht023c, ht123e, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht034a, ht123e, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht023c, ht034a, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht023c, ht123e, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht123e, hbg3c]
                      ·
                        linarith only [hdelta1, ht023c, ht034a, hbg3c]
                      ·
                        linarith only [hdelta1, ht123e, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht023c, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht134a, hbg3c]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht013b, ht023c, ht234a, ht134a]
                    ·
                      have hb0 := m.budget 0 (by decide) 2 4 3 1 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                        ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                      ·
                        have hb3 := m.budget 3 (by decide) 4 1 0 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc31, hc30, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, ht012e, ht013a, ht034d, hbg0, hbg3]
                        ·
                          linarith only [hdelta1, ht012e, ht013c, ht024c, ht134a, ht234d, hbg0, hbg3]
                        ·
                          linarith only [hn, hdelta1, h020, h231, ht034c, hbg0, hbg3]
                        ·
                          linarith only [hdelta1, ht012e, ht013a, ht023c, ht034c, ht134a, hbg0, hbg3]
                        ·
                          linarith only [hdelta1, ht012e, ht013c, ht024c, ht234d, hbg0, hbg3c]
                        ·
                          linarith only [hdelta1, h120, h231, ht012b, ht034c, hbg3b, hbg0]
                        ·
                          linarith only [hdelta1, ht012e, ht013a, ht023c, ht034c, hbg3c, hbg0]
                        ·
                          linarith only [hdelta1, h120, h231, ht012b, ht034c, hbg0, hbg3b]
                        ·
                          linarith only [hdelta1, ht023c, ht134a, hbg3c]
                        ·
                          linarith only [hdelta1, h020, h231, ht034c, hbg0, hbg3a]
                      ·
                        have hb2 := m.budget 2 (by decide) 1 0 4 3 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc21, hc20] at hb2
                        rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                          ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                        ·
                          linarith only [hn, hdelta1, h011, h120, ht013c, ht024b, hbg0, hbg2]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 1 0 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc30, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012e, ht013a, ht234d, hbg2, hbg3]
                          ·
                            linarith only [hdelta1, ht012e, ht013c, ht134a, ht234d, hbg2, hbg3]
                          ·
                            linarith only [hn, hdelta1, h120, h231, ht012b, ht024b, hbg0, hbg3]
                          ·
                            linarith only [hdelta1, ht012e, ht013a, ht023c, ht024b, ht134a, hbg0, hbg3]
                          ·
                            linarith only [hdelta1, ht012e, ht013c, hbg3c, ht234d, hbg2]
                          ·
                            linarith only [hdelta1, h020, h231, ht024b, hbg0, hbg3b]
                          ·
                            linarith only [hdelta1, ht023c, ht034b, hbg0, hbg3b]
                          ·
                            linarith only [hdelta1, h120, h231, ht012b, ht024b, hbg0, hbg3b]
                          ·
                            linarith only [hdelta1, ht014b, ht023c, ht134b, hbg0, hbg3b]
                          ·
                            linarith only [hdelta1, h120, h231, ht012b, ht024b, hbg3a, hbg0]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 1 0 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc30, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h231, h340, ht012e, ht013a, ht024a, hbg3, hbg2]
                          ·
                            linarith only [hdelta1, ht012e, ht013c, ht024a, ht123e, hbg3, hbg2]
                          ·
                            linarith only [hn, hdelta1, h020, h231, ht024b, hbg3, hbg0]
                          ·
                            linarith only [hdelta1, ht012e, ht013a, ht023c, ht024b, ht134a, hbg3, hbg0]
                          ·
                            linarith only [hdelta1, h231, h340, ht012e, ht013c, ht024a, hbg3c, hbg2]
                          ·
                            linarith only [hdelta1, h020, h231, ht024b, hbg3b, hbg0]
                          ·
                            linarith only [hdelta1, ht012e, ht013c, ht034b, ht024a, hbg3b, hbg0, hbg2]
                          ·
                            linarith only [hdelta1, h040, h231, hbg3b, hbg0]
                          ·
                            linarith only [hdelta1, ht014b, ht023c, hbg3b, ht134b, hbg0]
                          ·
                            linarith only [hdelta1, h120, h231, ht014b, ht124b, hbg3a, hbg0]
                        ·
                          linarith only [hn, hdelta1, ht014b, ht023c, ht124b, hbg0, hbg2]
                        ·
                          linarith only [hdelta1, h011, h120, ht013c, ht024b, hbg2a, hbg0]
                        ·
                          linarith only [hdelta1, h011, h120, ht013c, ht024b, hbg2a, hbg0]
                        ·
                          linarith only [hdelta1, h011, h120, ht013c, ht024b, hbg2a, hbg0]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 1 0 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc31, hc30, hc32] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h231, h340, ht012e, ht013a, hbg2c, hbg3]
                          ·
                            linarith only [hdelta1, ht012e, ht013c, ht123e, hbg2c, hbg3]
                          ·
                            linarith only [hn, hdelta1, h020, h231, ht024b, hbg0, hbg3]
                          ·
                            linarith only [hdelta1, ht012e, ht013c, ht014b, hbg2b, hbg2a, ht134b, hbg0, hbg3]
                          ·
                            linarith only [hdelta1, h231, h340, ht012e, ht013c, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, h040, h231, hbg0, hbg3b]
                          ·
                            linarith only [hdelta1, ht023c, ht034b, hbg0, hbg3b]
                          ·
                            linarith only [hdelta1, h120, h231, ht012b, ht024b, hbg0, hbg3b]
                          ·
                            linarith only [hdelta1, ht014b, ht023c, ht134b, hbg0, hbg3b]
                          ·
                            linarith only [hdelta1, h120, h231, ht012b, ht024b, hbg3a, hbg0]
                        ·
                          linarith only [hdelta1, ht012b, ht023c, ht024b, hbg0, hbg2b]
                        ·
                          linarith only [hdelta1, ht012b, ht023c, ht024b, hbg0, hbg2b]
                      ·
                        have hb4 := m.budget 4 (by decide) 3 1 0 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc43, hc41, hc40, hc42] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hn, hdelta1, h011, h340, ht014b, ht034c, hbg0, hbg4]
                        ·
                          linarith only [hn, hdelta1, h011, h140, ht034c, hbg0, hbg4]
                        ·
                          linarith only [hdelta1, ht012e, ht034a, ht024b, ht234d, hbg0, hbg4]
                        ·
                          linarith only [hdelta1, ht012e, ht013b, ht024a, ht134a, hbg0, hbg4]
                        ·
                          linarith only [hdelta1, h011, h120, ht034c, ht124b, hbg0, hbg4b]
                        ·
                          linarith only [hdelta1, h011, h340, ht014b, ht034c, hbg4a, hbg0]
                        ·
                          linarith only [hdelta1, h011, h340, ht014b, ht034c, hbg4a, hbg0]
                        ·
                          linarith only [hdelta1, h011, h140, ht034c, hbg4a, hbg0]
                        ·
                          linarith only [hdelta1, h011, h140, ht034c, hbg4a, hbg0]
                        ·
                          linarith only [hdelta1, ht012e, ht013b, ht024b, ht134a, hbg4c, hbg0]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 1 0 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc31, hc30, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, ht013a, ht024a, ht234d, hbg0, hbg3]
                        ·
                          linarith only [hdelta1, ht013c, ht024a, ht134a, ht234d, hbg0, hbg3]
                        ·
                          have hb2 := m.budget 2 (by decide) 1 0 4 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc21, hc20] at hb2
                          rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                          ·
                            linarith only [hn, hdelta1, h120, h231, ht023b, hbg2, hbg3]
                          ·
                            linarith only [hdelta1, ht013a, ht134a, ht234d, hbg0, hbg2]
                          ·
                            linarith only [hdelta1, h231, h340, ht013a, ht024a, ht134a, hbg0, hbg2]
                          ·
                            linarith only [hn, hdelta1, ht014b, ht034c, ht124b, hbg2, hbg3]
                          ·
                            linarith only [hdelta1, h120, h231, ht023b, hbg2a, hbg3]
                          ·
                            linarith only [hdelta1, h120, h231, ht023b, hbg2a, hbg3]
                          ·
                            linarith only [hdelta1, h120, h231, ht023b, hbg2a, hbg3]
                          ·
                            linarith only [hdelta1, h231, h340, ht013a, ht134a, hbg2c, hbg0]
                          ·
                            linarith only [hdelta1, ht014b, ht034c, ht124b, hbg2b, hbg3]
                          ·
                            linarith only [hdelta1, ht014b, ht034c, ht124b, hbg2b, hbg3]
                        ·
                          linarith only [hdelta1, ht013a, ht024a, ht134a, ht234c, hbg0, hbg3]
                        ·
                          linarith only [hdelta1, ht013c, ht024a, hbg3c, ht234d, hbg0]
                        ·
                          have hb2 := m.budget 2 (by decide) 1 0 4 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc21, hc20] at hb2
                          rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                          ·
                            linarith only [hdelta1, h120, h231, ht023b, hbg3b, hbg2]
                          ·
                            linarith only [hdelta1, h241, h340, ht013a, hbg2, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, h231, h340, ht013a, ht024a, hbg2, hbg0, hbg3a]
                          ·
                            linarith only [hdelta1, ht012b, ht023b, hbg3b, hbg2]
                          ·
                            linarith only [hdelta1, h120, h231, ht013b, hbg3c, hbg2c, ht234d]
                          ·
                            linarith only [hdelta1, h120, h231, ht024a, hbg2c]
                          ·
                            linarith only [hdelta1, h241, h340, ht013b, ht024a, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht013a, ht123e, hbg2c, hbg0]
                          ·
                            linarith only [hdelta1, ht012b, ht013b, hbg3c, hbg2c, ht234d]
                          ·
                            linarith only [hdelta1, ht012b, ht024a, hbg2c]
                        ·
                          linarith only [hdelta1, ht013a, ht023a, hbg3c, hbg0]
                        ·
                          linarith only [hdelta1, h231, h340, ht134a, hbg3c]
                        ·
                          linarith only [hdelta1, ht013c, ht023a, ht134a, hbg3c, hbg0]
                        ·
                          linarith only [hdelta1, ht013b, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht012e, ht013c, hbg0c]
                      ·
                        linarith only [hdelta1, ht012e, ht034c, hbg0c]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 1 0 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc31, hc30, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, ht013a, ht034d, hbg0c, hbg3]
                        ·
                          linarith only [hdelta1, ht013c, ht034d, ht134a, hbg0c, hbg3]
                        ·
                          linarith only [hdelta1, h020, h231, ht034c, hbg0a, hbg3]
                        ·
                          linarith only [hdelta1, ht013a, ht023c, ht034c, ht134a, hbg0c, hbg3]
                        ·
                          linarith only [hdelta1, ht013c, ht024c, hbg0c, ht234d, hbg3c]
                        ·
                          linarith only [hdelta1, h231, h340, ht013a, ht034c, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, ht013a, ht023c, ht034c, hbg0c, hbg3c]
                        ·
                          linarith only [hdelta1, ht123e, hbg3c]
                        ·
                          linarith only [hdelta1, ht023c, ht134a, hbg3c]
                        ·
                          linarith only [hdelta1, ht013b, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht012e, ht024b, hbg0c]
                      ·
                        have hb3 := m.budget 3 (by decide) 4 1 0 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc31, hc30, hc32] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          have hb4 := m.budget 4 (by decide) 3 1 0 2 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc43, hc41, hc40, hc42] at hb4
                          rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                            ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                          ·
                            linarith only [hdelta1, h011, h340, ht013c, ht014b, hbg0a, hbg4]
                          ·
                            linarith only [hdelta1, h011, h140, ht013c, hbg0a, hbg4]
                          ·
                            linarith only [hdelta1, ht013a, ht024b, ht234d, hbg0b, hbg4, hbg3]
                          ·
                            linarith only [hdelta1, ht013a, ht024a, hbg0b, hbg4, hbg3]
                          ·
                            linarith only [hdelta1, h011, h340, ht013c, hbg0a, hbg4c]
                          ·
                            linarith only [hdelta1, ht014b, hbg4c, ht234d]
                          ·
                            linarith only [hdelta1, ht013c, ht014b, ht024a, hbg0c, hbg4c]
                          ·
                            linarith only [hdelta1, ht124e, hbg4c]
                          ·
                            linarith only [hdelta1, ht013c, ht024a, ht134b, hbg0c, hbg4c]
                          ·
                            linarith only [hdelta1, ht013a, ht024b, hbg4c, hbg0b, hbg3]
                        ·
                          have hb2 := m.budget 2 (by decide) 1 0 4 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc21, hc20] at hb2
                          rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                          ·
                            linarith only [hdelta1, h011, h120, ht013c, ht024b, hbg0a, hbg2]
                          ·
                            linarith only [hdelta1, ht013c, ht134a, ht234d, hbg0b, hbg2, hbg3]
                          ·
                            linarith only [hdelta1, h130, h231, ht013c, ht024a, hbg0b, hbg2, hbg3]
                          ·
                            linarith only [hdelta1, ht012b, ht023c, ht024b, hbg0a, hbg2]
                          ·
                            linarith only [hdelta1, h011, h120, ht013c, ht134a, hbg2c, ht234d, hbg3]
                          ·
                            linarith only [hdelta1, h120, h231, ht024a, hbg2c]
                          ·
                            linarith only [hdelta1, ht023c, ht123b, hbg3, hbg2b]
                          ·
                            linarith only [hdelta1, h231, h340, ht013c, ht134a, hbg2c, hbg0b, hbg3]
                          ·
                            linarith only [hdelta1, ht023c, ht124b, hbg2b, ht134c, hbg3]
                          ·
                            linarith only [hdelta1, ht023c, ht124b, hbg2b, ht134c, hbg3]
                        ·
                          linarith only [hdelta1, h120, h231, ht012b, ht024b, hbg0a, hbg3]
                        ·
                          linarith only [hdelta1, ht023c, ht034b, hbg0a, hbg3]
                        ·
                          have hb2 := m.budget 2 (by decide) 1 0 4 3 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc21, hc20] at hb2
                          rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                            ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                          ·
                            linarith only [hdelta1, h011, h120, ht013c, ht024b, hbg0a, hbg2]
                          ·
                            linarith only [hdelta1, ht013c, ht234d, hbg0b, hbg2, hbg3c]
                          ·
                            linarith only [hdelta1, h231, h340, ht013c, ht024a, hbg0b, hbg2, hbg3c]
                          ·
                            linarith only [hdelta1, ht014b, ht023c, ht124b, hbg0a, hbg2]
                          ·
                            linarith only [hdelta1, h011, h120, ht013c, hbg2c, ht234d, hbg3c]
                          ·
                            linarith only [hdelta1, h120, h231, ht024a, hbg2c]
                          ·
                            linarith only [hdelta1, ht023a, hbg2c]
                          ·
                            linarith only [hdelta1, h231, h340, ht013c, hbg2c, hbg0b, hbg3c]
                          ·
                            linarith only [hdelta1, ht012b, ht023c, hbg2c, ht234d, hbg3c]
                          ·
                            linarith only [hdelta1, ht012b, ht024a, hbg2c]
                        ·
                          linarith only [hdelta1, h231, h340, ht013a, ht024b, hbg3c, hbg0c]
                        ·
                          linarith only [hdelta1, ht013a, ht023c, ht024b, hbg3c, hbg0c]
                        ·
                          linarith only [hdelta1, ht123e, hbg3c]
                        ·
                          linarith only [hdelta1, ht023c, ht134a, hbg3c]
                        ·
                          linarith only [hdelta1, ht013b, ht134a, hbg3c]
                      ·
                        have hb4 := m.budget 4 (by decide) 3 1 0 2 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc43, hc41, hc40, hc42] at hb4
                        rcases hb4 with hbg4 | hbg4 | hbg4 | hbg4 |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ |
                          ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩ | ⟨hbg4a,hbg4b,hbg4c⟩
                        ·
                          linarith only [hdelta1, h011, h340, ht014b, ht034c, hbg0a, hbg4]
                        ·
                          linarith only [hdelta1, h011, h140, ht034c, hbg0a, hbg4]
                        ·
                          linarith only [hdelta1, ht013b, ht024b, ht134a, hbg0c, ht234d, hbg4]
                        ·
                          linarith only [hdelta1, ht013b, ht024a, ht134a, hbg0c, hbg4]
                        ·
                          linarith only [hdelta1, h011, h340, ht034c, hbg0a, hbg4c]
                        ·
                          linarith only [hdelta1, ht014b, hbg4c, ht234d]
                        ·
                          linarith only [hdelta1, ht014b, ht034c, ht024a, hbg0c, hbg4c]
                        ·
                          linarith only [hdelta1, ht124e, hbg4c]
                        ·
                          linarith only [hdelta1, ht034c, ht024a, ht134b, hbg0c, hbg4c]
                        ·
                          linarith only [hdelta1, ht034a, ht024b, hbg0c, hbg4c]
                ·
                  linarith only [ht012b, ht024a, ht124a]
              ·
                linarith only [ht012b, ht023a, ht123a]
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              linarith only [ht023b, ht034b, ht024c]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht023c, ht234a, ht034a]
                    ·
                      have hb2 := m.budget 2 (by decide) 1 4 0 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h120, h231, ht023a, ht024a, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht123e, ht134a, hbg2, ht234b]
                      ·
                        linarith only [hdelta1, ht024a, ht123e, ht134a, hbg2, ht234b]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, ht134a, ht123b, hbg2, ht234b]
                      ·
                        linarith only [hdelta1, h120, h231, ht023a, hbg2c]
                      ·
                        linarith only [hdelta1, h120, h231, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, h130, h231, ht134a, hbg2c, ht234b]
                      ·
                        linarith only [hdelta1, ht023a, ht134a, ht123b, hbg2c, ht234b]
                      ·
                        linarith only [hdelta1, ht024a, ht134a, ht123b, hbg2c, ht234b]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht013b, ht023c, ht134a, ht234a]
                    ·
                      have hb2 := m.budget 2 (by decide) 1 4 0 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h120, h231, ht023a, ht024a, hbg2]
                      ·
                        linarith only [hdelta1, h120, h231, ht023a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, h120, h231, ht024a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, h120, h231, ht023a, hbg2c]
                      ·
                        linarith only [hdelta1, h120, h231, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, h120, h231, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, ht124a, hbg2c]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht124c, ht134b, ht123b]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht013b, ht023c, ht234a, ht134a]
                    ·
                      have hb2 := m.budget 2 (by decide) 4 1 0 3 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, ht012b, ht023a, ht234e, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht124a, ht234e, hbg2]
                      ·
                        linarith only [hdelta1, ht012b, ht124a, ht234e, hbg2]
                      ·
                        linarith only [hdelta1, ht012b, ht023a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht234e, hbg2c]
                      ·
                        linarith only [hdelta1, ht012b, ht234e, hbg2c]
                      ·
                        linarith only [hdelta1, ht012b, ht023a, hbg2c]
                      ·
                        linarith only [hdelta1, h231, h340, ht124a, hbg2c, ht234b]
                      ·
                        linarith only [hdelta1, ht023a, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012b, ht124a, hbg2c]
              ·
                linarith only [ht012b, ht023a, ht123a]
        ·
          rcases m.triangle 0 2 4 (by decide) (by decide) with ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩ | ⟨ht024a,ht024b,ht024c,ht024d,ht024e⟩
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 1 3 0 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h120, h241, ht023a, ht024a, hbg2]
                      ·
                        linarith only [hdelta1, h120, h341, ht024a, ht123a, hbg2, ht234c]
                      ·
                        linarith only [hdelta1, h120, h341, ht023a, ht123a, hbg2, ht234c]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, h120, h341, ht024a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, h120, h341, ht023a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, h120, h341, ht123a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht123a, hbg2c]
                    ·
                      linarith only [ht023b, ht034a, ht234a]
                  ·
                    linarith only [ht023a, ht024b, ht034c, ht134a, ht123c]
                ·
                  linarith only [ht023a, ht024a, ht123a, ht124a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 3 1 0 4 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, ht012b, ht024a, hbg2, ht234d]
                      ·
                        linarith only [hdelta1, ht024a, ht123a, hbg2, ht234d]
                      ·
                        linarith only [hdelta1, ht012b, ht123a, hbg2, ht234d]
                      ·
                        linarith only [hdelta1, ht012b, ht024a, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, ht024a, ht234d, hbg2c]
                      ·
                        linarith only [hdelta1, ht012b, ht234d, hbg2c]
                      ·
                        linarith only [hdelta1, ht012b, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, h230, h341, ht123a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012b, ht123a, hbg2c]
                    ·
                      linarith only [ht013b, ht034a, ht123b, ht234a]
                  ·
                    linarith only [ht013b, ht024b, ht034c, ht023c, ht134a]
                ·
                  linarith only [ht012b, ht024a, ht124a]
            ·
              linarith only [ht024b, ht034c, ht023c]
          ·
            rcases m.triangle 0 3 4 (by decide) (by decide) with ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩ | ⟨ht034a,ht034b,ht034c,ht034d,ht034e⟩
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 1 3 4 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, ht012d, ht023a, hbg2]
                      ·
                        linarith only [hdelta1, ht012d, ht024a, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, ht012d, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht023a, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, ht012d, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012d, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, hbg2c]
                      ·
                        linarith only [hdelta1, h021, h120, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, ht124a, hbg2c]
                    ·
                      linarith only [ht023b, ht034a, ht234a]
                  ·
                    linarith only [ht013b, ht034a, ht134a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht123b, ht124c, ht134b]
                  ·
                    linarith only [ht013b, ht034a, ht134a]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 3 1 4 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h011, h230, ht012c, ht024a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht012d, ht024a, hbg2]
                      ·
                        linarith only [hdelta1, h011, h230, ht012c, ht123a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht024a, ht123a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, h011, h230, ht012c, ht024a, hbg2c]
                      ·
                        linarith only [hdelta1, h011, h230, ht012c, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012d, hbg2c]
                      ·
                        linarith only [hdelta1, ht024a, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, ht123a, ht124a, hbg2c]
                    ·
                      linarith only [ht013b, ht034a, ht234a, ht123b]
                  ·
                    linarith only [ht013b, ht034a, ht134a]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 3 4 1 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h011, h230, ht012a, ht124a, hbg2]
                      ·
                        have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc31, hc30] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h011, h230, ht012a, ht013b, ht034a, hbg3, hbg2, ht234e]
                        ·
                          linarith only [hdelta1, h011, h130, ht012a, ht034a, hbg3, hbg2, ht234e]
                        ·
                          linarith only [hdelta1, ht012a, ht013e, hbg3, hbg2, ht234e]
                        ·
                          linarith only [hdelta1, ht012a, ht013e, ht034a, hbg3, ht234b, hbg2]
                        ·
                          linarith only [hdelta1, h011, h230, ht012a, ht034a, hbg2, ht234e, hbg3c]
                        ·
                          linarith only [hdelta1, h011, h230, ht012a, ht013b, hbg2, ht234e, hbg3c]
                        ·
                          linarith only [hdelta1, ht013b, ht034a, hbg3c]
                        ·
                          linarith only [hdelta1, h011, h230, ht012a, ht123b, hbg2, ht234e, hbg3c]
                        ·
                          linarith only [hdelta1, ht034a, ht123b, hbg3c]
                        ·
                          linarith only [hdelta1, ht012a, ht013e, ht234b, hbg2, hbg3c]
                      ·
                        have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc31, hc30] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hn, hdelta1, h011, h230, ht012c, hbg3, ht123c, hbg2]
                        ·
                          linarith only [hdelta1, h011, h130, ht012c, ht034a, hbg3, ht124a, hbg2, ht234e]
                        ·
                          linarith only [hdelta1, ht012c, ht013e, hbg3, ht124a, hbg2, ht234e]
                        ·
                          linarith only [hdelta1, ht012c, ht013e, ht034a, ht123a, hbg3, hbg2]
                        ·
                          linarith only [hdelta1, h011, h230, ht012c, ht124c, ht134b, hbg2, hbg3a]
                        ·
                          linarith only [hdelta1, h011, h230, ht012c, ht124c, ht134b, hbg2, hbg3a]
                        ·
                          linarith only [hdelta1, h011, h230, ht012c, ht124c, ht134b, hbg2, hbg3a]
                        ·
                          linarith only [hdelta1, h011, h130, ht012c, ht124a, hbg2, hbg3c, ht234e]
                        ·
                          linarith only [hdelta1, ht034a, ht123b, hbg3c]
                        ·
                          linarith only [hdelta1, ht012c, ht013e, ht123a, hbg2, hbg3c]
                      ·
                        have hb0 := m.budget 0 (by decide) 3 4 2 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                        ·
                          linarith only [hn, hdelta1, ht013b, ht024c, ht123b, hbg2, hbg0]
                        ·
                          linarith only [hn, hdelta1, ht013b, ht123b, hbg2, ht034b, hbg0]
                        ·
                          have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc31, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, h011, h230, ht013b, ht023c, hbg3, hbg0]
                          ·
                            linarith only [hn, hdelta1, h011, h130, ht024c, hbg3, ht034b, hbg0]
                          ·
                            linarith only [hdelta1, ht012b, ht013e, ht124a, hbg3, ht234e, hbg0]
                          ·
                            linarith only [hdelta1, ht013e, ht023a, ht034a, hbg3, hbg0]
                          ·
                            linarith only [hdelta1, h011, h230, ht023c, hbg3a, hbg3b, hbg0]
                          ·
                            linarith only [hdelta1, h011, h230, ht013b, ht023c, hbg3a, hbg0]
                          ·
                            linarith only [hdelta1, h011, h230, ht013b, ht023c, hbg3a, hbg0]
                          ·
                            linarith only [hdelta1, h011, h130, ht023c, hbg3a, hbg0]
                          ·
                            linarith only [hdelta1, h011, h130, ht023c, hbg3a, hbg0]
                          ·
                            linarith only [hdelta1, ht012b, ht013e, ht234b, ht124a, hbg3c, hbg0]
                        ·
                          have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc31, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, ht013b, ht023c, hbg3, hbg2]
                          ·
                            linarith only [hn, hdelta1, ht024c, ht123b, hbg3, hbg2, ht034b]
                          ·
                            linarith only [hdelta1, ht012a, hbg3, ht124a, ht234e, hbg0]
                          ·
                            linarith only [hdelta1, ht012a, ht034a, ht234b, hbg3, ht124a, hbg0]
                          ·
                            linarith only [hdelta1, ht024c, hbg3a, hbg3b, hbg2, ht034b]
                          ·
                            linarith only [hdelta1, ht013b, ht024c, hbg3a, hbg2, ht034b]
                          ·
                            linarith only [hdelta1, ht013b, ht024c, hbg3a, hbg2, ht034b]
                          ·
                            linarith only [hdelta1, ht024c, ht123b, hbg3a, hbg2, ht034b]
                          ·
                            linarith only [hdelta1, ht024c, ht123b, hbg3a, hbg2, ht034b]
                          ·
                            linarith only [hdelta1, ht012a, ht234b, ht124a, hbg3c, hbg0]
                        ·
                          linarith only [hdelta1, ht013b, ht123b, hbg2, hbg0b, hbg0a]
                        ·
                          linarith only [hdelta1, ht013b, ht024c, ht123b, hbg2, hbg0a]
                        ·
                          linarith only [hdelta1, ht013b, ht024c, ht123b, hbg2, hbg0a]
                        ·
                          linarith only [hdelta1, ht013b, ht123b, hbg2, ht034b, hbg0a]
                        ·
                          linarith only [hdelta1, ht013b, ht123b, hbg2, ht034b, hbg0a]
                        ·
                          have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc31, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hn, hdelta1, ht013b, ht023c, hbg3, hbg2]
                          ·
                            linarith only [hn, hdelta1, ht023c, hbg3, ht123b, hbg2]
                          ·
                            linarith only [hdelta1, ht012b, hbg3, ht124a, ht234e, hbg0c]
                          ·
                            linarith only [hdelta1, ht012b, ht034a, hbg3, ht234b, ht124a, hbg0c]
                          ·
                            linarith only [hdelta1, ht014b, ht024c, ht134b, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, ht014b, ht024c, ht134b, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, ht014b, ht024c, ht134b, hbg2, hbg3a]
                          ·
                            linarith only [hdelta1, ht024c, ht123b, hbg2, ht034b, hbg3a]
                          ·
                            linarith only [hdelta1, ht024c, ht123b, hbg2, ht034b, hbg3a]
                          ·
                            linarith only [hdelta1, ht012b, ht234b, ht124a, hbg3c, hbg0c]
                      ·
                        linarith only [hdelta1, h011, h230, ht012a, hbg2c]
                      ·
                        linarith only [hdelta1, h011, h230, ht012c, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012b, ht124a, hbg2c]
                      ·
                        have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        simp only [hc32, hc31, hc30] at hb3
                        rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                          ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                        ·
                          linarith only [hdelta1, h011, h230, ht012c, hbg2b, ht123c, hbg3]
                        ·
                          linarith only [hdelta1, h011, h230, ht012c, ht034a, ht123b, hbg2c, ht234e, hbg3]
                        ·
                          linarith only [hdelta1, ht012c, ht013e, hbg2c, ht234e, hbg3]
                        ·
                          linarith only [hdelta1, ht012c, ht013e, ht034a, ht234b, hbg2c, hbg3]
                        ·
                          linarith only [hdelta1, h011, h230, ht012c, ht034a, hbg2c, ht234e, hbg3c]
                        ·
                          linarith only [hdelta1, h011, h230, ht012c, ht013b, hbg2c, ht234e, hbg3c]
                        ·
                          linarith only [hdelta1, ht013b, ht034a, hbg3c]
                        ·
                          linarith only [hdelta1, h011, h130, ht012c, hbg2c, ht234e, hbg3c]
                        ·
                          linarith only [hdelta1, ht034a, ht123b, hbg3c]
                        ·
                          linarith only [hdelta1, ht012c, ht013e, ht234b, hbg2c, hbg3c]
                      ·
                        have hb0 := m.budget 0 (by decide) 3 4 2 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                        ·
                          linarith only [hdelta1, ht013b, ht024c, ht123b, hbg2b, hbg0]
                        ·
                          linarith only [hdelta1, ht014b, ht124b, ht234b, hbg2b, hbg0]
                        ·
                          linarith only [hdelta1, h011, h230, ht012b, hbg2a, ht234b, hbg0]
                        ·
                          have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc31, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, ht012b, ht013b, ht034a, hbg3, hbg2c, ht234e]
                          ·
                            linarith only [hdelta1, ht024c, ht123b, hbg2b, hbg3, ht034b]
                          ·
                            linarith only [hdelta1, ht012a, hbg2a, hbg3, ht234e, hbg0]
                          ·
                            linarith only [hdelta1, ht012a, ht034a, hbg2a, ht234b, hbg3, hbg0]
                          ·
                            linarith only [hdelta1, ht024c, hbg3c, hbg2b, ht034b]
                          ·
                            linarith only [hdelta1, ht012b, ht013b, hbg3c, hbg2c, ht234e]
                          ·
                            linarith only [hdelta1, ht013b, ht034a, hbg3c]
                          ·
                            linarith only [hdelta1, ht012b, ht123b, hbg3c, hbg2c, ht234e]
                          ·
                            linarith only [hdelta1, ht034a, ht123b, hbg3c]
                          ·
                            linarith only [hdelta1, ht012a, ht123a, hbg3c, hbg0]
                        ·
                          linarith only [hdelta1, ht013b, ht123b, hbg2b, hbg0c]
                        ·
                          linarith only [hdelta1, ht013e, ht024c, hbg0c]
                        ·
                          linarith only [hdelta1, ht012a, ht024c, ht234b, hbg2c, hbg0c]
                        ·
                          linarith only [hdelta1, ht013e, ht034b, hbg0c]
                        ·
                          linarith only [hdelta1, ht012a, ht234b, hbg2c, ht034b, hbg0c]
                        ·
                          have hb3 := m.budget 3 (by decide) 2 1 0 4 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc31, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h011, h230, ht013b, ht023c, hbg0a, hbg3]
                          ·
                            linarith only [hdelta1, h011, h130, ht024c, hbg0a, hbg3, ht034b]
                          ·
                            linarith only [hdelta1, ht012b, hbg2a, hbg3, hbg0c, ht234e]
                          ·
                            linarith only [hdelta1, ht012b, ht034a, hbg2a, ht234b, hbg3, hbg0c]
                          ·
                            linarith only [hdelta1, h011, h230, ht024c, hbg0a, hbg3c, ht034b]
                          ·
                            linarith only [hdelta1, ht012b, ht013b, hbg3c, hbg2c, ht234e]
                          ·
                            linarith only [hdelta1, ht013b, ht034a, hbg3c]
                          ·
                            linarith only [hdelta1, ht012b, ht123b, hbg3c, hbg2c, ht234e]
                          ·
                            linarith only [hdelta1, ht034a, ht123b, hbg3c]
                          ·
                            linarith only [hdelta1, ht023a, hbg3c, hbg0c]
                      ·
                        linarith only [hdelta1, ht234b, ht124a, hbg2c]
                    ·
                      linarith only [ht013b, ht034a, ht123b, ht234a]
                  ·
                    linarith only [ht013b, ht034a, ht134a]
            ·
              rcases m.triangle 1 2 3 (by decide) (by decide) with ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩ | ⟨ht123a,ht123b,ht123c,ht123d,ht123e⟩
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 1 3 4 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, ht012d, ht023a, hbg2]
                      ·
                        linarith only [hdelta1, ht012d, ht034a, ht123a, ht023c, ht234c, hbg2]
                      ·
                        linarith only [hdelta1, ht012d, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht034a, ht123a, ht023c, ht234a, hbg2]
                      ·
                        linarith only [hdelta1, ht012d, ht034a, ht023c, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht012d, hbg2c, ht234b]
                      ·
                        linarith only [hdelta1, ht034a, ht023c, ht234a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012d, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, ht034a, ht123a, ht023c, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht124a, hbg2c]
                    ·
                      have hb2 := m.budget 2 (by decide) 1 4 3 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, ht012d, ht024a, hbg2]
                      ·
                        linarith only [hdelta1, ht012d, ht023a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht012d, ht234a, hbg2, ht123b, ht134a]
                      ·
                        linarith only [hdelta1, ht023a, ht234a, hbg2, ht123b, ht134a]
                      ·
                        linarith only [hdelta1, ht012d, ht023a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012d, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, h021, h120, ht123b, ht234b, ht134a, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht123b, ht234b, ht134a, hbg2c]
                      ·
                        linarith only [hdelta1, ht123a, hbg2c]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht123c, ht234a, ht134a]
                    ·
                      have hb2 := m.budget 2 (by decide) 1 4 3 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, ht012d, ht024a, hbg2]
                      ·
                        linarith only [hdelta1, ht012d, ht023a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht012d, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, ht024a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht012d, ht023a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012d, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht012d, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht123a, hbg2c]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    linarith only [ht124c, ht123b, ht134b]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      linarith only [ht123c, ht134a, ht234a]
                    ·
                      have hb2 := m.budget 2 (by decide) 4 1 3 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h011, h340, ht012c, ht023a, ht123a, hbg2, ht234b]
                      ·
                        linarith only [hdelta1, h011, h340, ht012c, ht023a, hbg2, ht124a, ht234b]
                      ·
                        linarith only [hdelta1, h011, h340, ht012c, ht123a, hbg2, ht124a, ht234b]
                      ·
                        linarith only [hdelta1, ht023a, ht123a, hbg2, ht124a]
                      ·
                        linarith only [hdelta1, h011, h340, ht012c, ht023a, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, h011, h340, ht012c, ht123a, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012d, hbg2c]
                      ·
                        linarith only [hdelta1, ht023a, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht123a, ht124a, hbg2c]
              ·
                rcases m.triangle 1 2 4 (by decide) (by decide) with ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩ | ⟨ht124a,ht124b,ht124c,ht124d,ht124e⟩
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb2 := m.budget 2 (by decide) 3 1 4 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h011, h230, ht012c, ht024a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht023d, ht034a, ht123a, ht234c, hbg2]
                      ·
                        linarith only [hdelta1, h011, h230, ht012c, ht123a, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht034a, ht123a, ht023c, ht234c, ht124a, hbg2]
                      ·
                        linarith only [hdelta1, ht023d, ht034a, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, h011, h230, ht012c, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht034a, ht023c, ht234c, ht124a, hbg2c]
                      ·
                        linarith only [hdelta1, ht012d, hbg2c]
                      ·
                        linarith only [hdelta1, ht034a, ht123a, ht023c, ht234c, hbg2c]
                      ·
                        linarith only [hdelta1, ht123a, ht124a, hbg2c]
                    ·
                      linarith only [ht123b, ht234a, ht134a]
                  ·
                    linarith only [ht123c, ht124b, ht134c]
                ·
                  rcases m.triangle 1 3 4 (by decide) (by decide) with ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩ | ⟨ht134a,ht134b,ht134c,ht134d,ht134e⟩
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb3 := m.budget 3 (by decide) 2 1 4 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc32, hc31, hc30] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, ht023d, ht034a, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, ht013d, ht034a, hbg3]
                      ·
                        linarith only [hdelta1, ht023d, ht134a, ht123b, hbg3]
                      ·
                        linarith only [hdelta1, ht034a, ht134a, ht123b, hbg3]
                      ·
                        linarith only [hdelta1, ht023d, ht034a, hbg3c]
                      ·
                        linarith only [hdelta1, ht023d, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht013d, hbg3c]
                      ·
                        linarith only [hdelta1, ht034a, ht123b, hbg3c]
                      ·
                        linarith only [hdelta1, ht134a, ht123b, hbg3c]
                    ·
                      linarith only [ht134a, ht123b, ht234a]
                  ·
                    rcases m.triangle 2 3 4 (by decide) (by decide) with ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩ | ⟨ht234a,ht234b,ht234c,ht234d,ht234e⟩
                    ·
                      have hb3 := m.budget 3 (by decide) 2 4 1 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc32, hc31, hc30] at hb3
                      rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                        ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                      ·
                        linarith only [hdelta1, h011, h230, ht012a, ht123c, ht134a, hbg3]
                      ·
                        linarith only [hdelta1, h011, h230, ht012a, ht123c, hbg3, ht234a]
                      ·
                        linarith only [hdelta1, ht023d, ht134a, hbg3, ht234a]
                      ·
                        linarith only [hdelta1, ht013b, ht134a, hbg3, ht234a]
                      ·
                        linarith only [hdelta1, h011, h230, ht012a, ht123c, hbg3c]
                      ·
                        linarith only [hdelta1, ht023d, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht013b, ht134a, hbg3c]
                      ·
                        linarith only [hdelta1, ht023d, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, ht013b, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, ht134a, ht234a, hbg3c]
                    ·
                      have hb2 := m.budget 2 (by decide) 4 3 1 0 (by decide)
                        (by linarith)
                        (by linarith)
                        (by linarith)
                      simp only [hc21, hc20] at hb2
                      rcases hb2 with hbg2 | hbg2 | hbg2 | hbg2 |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ |
                        ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩ | ⟨hbg2a,hbg2b,hbg2c⟩
                      ·
                        linarith only [hdelta1, h011, h240, ht012a, ht123a, hbg2]
                      ·
                        linarith only [hdelta1, h011, h340, ht012a, ht234a, hbg2]
                      ·
                        linarith only [hdelta1, h011, h340, ht012c, ht123a, ht234a, hbg2]
                      ·
                        have hb0 := m.budget 0 (by decide) 4 3 2 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                        ·
                          linarith only [hn, hdelta1, ht014b, ht023c, ht124b, hbg0, hbg2]
                        ·
                          linarith only [hdelta1, ht012a, ht013e, ht123a, ht234c, hbg0, hbg2]
                        ·
                          linarith only [hdelta1, h011, h340, ht012b, ht123a, ht234a, hbg0]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 2 1 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc31, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h011, h340, ht012a, ht123a, hbg3]
                          ·
                            linarith only [hn, hdelta1, ht012b, ht123c, ht234c, hbg3, hbg2]
                          ·
                            linarith only [hn, hdelta1, ht023c, ht123b, ht234c, hbg3, hbg2]
                          ·
                            linarith only [hdelta1, ht012a, ht034c, ht123a, ht234a, hbg3, hbg0]
                          ·
                            linarith only [hdelta1, ht013b, ht023c, ht234c, hbg3b, hbg2]
                          ·
                            linarith only [hdelta1, ht023c, ht134c, ht124b, hbg3b, hbg2]
                          ·
                            linarith only [hdelta1, ht012a, ht034c, ht123a, hbg0, hbg3c]
                          ·
                            linarith only [hdelta1, ht023c, ht134c, ht124b, hbg3b, hbg2]
                          ·
                            linarith only [hdelta1, ht013b, ht023c, ht234c, hbg3a, hbg2]
                          ·
                            linarith only [hdelta1, ht023c, ht123b, ht234c, hbg3a, hbg2]
                        ·
                          linarith only [hdelta1, ht023b, ht234c, hbg0b, hbg2]
                        ·
                          linarith only [hdelta1, ht014b, ht023c, ht124b, hbg0a, hbg2]
                        ·
                          linarith only [hdelta1, ht014b, ht023c, ht124b, hbg0a, hbg2]
                        ·
                          linarith only [hdelta1, ht023b, ht234c, hbg0a, hbg2]
                        ·
                          linarith only [hdelta1, ht023b, ht234c, hbg0a, hbg2]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 2 1 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc31, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h011, h340, ht013b, ht023c, ht123b, hbg3, hbg0a]
                          ·
                            linarith only [hdelta1, h011, h230, ht013b, ht023c, hbg3, hbg0a]
                          ·
                            linarith only [hdelta1, h011, h130, ht023c, hbg3, hbg0a]
                          ·
                            linarith only [hdelta1, ht012b, ht034c, ht123a, hbg3, ht234a, hbg0c]
                          ·
                            linarith only [hdelta1, ht013b, ht023c, ht234c, hbg3b, hbg2]
                          ·
                            linarith only [hdelta1, ht023c, ht134c, ht124b, hbg3b, hbg2]
                          ·
                            linarith only [hdelta1, ht023a, ht034c, hbg3c, hbg0c]
                          ·
                            linarith only [hdelta1, ht023c, ht134c, ht124b, hbg3b, hbg2]
                          ·
                            linarith only [hdelta1, ht013b, ht023c, ht234c, hbg3a, hbg2]
                          ·
                            linarith only [hdelta1, ht023c, ht123b, ht234c, hbg3a, hbg2]
                      ·
                        linarith only [hdelta1, h011, h340, ht012a, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, h011, h340, ht012c, ht123a, ht234b, hbg2c]
                      ·
                        linarith only [hdelta1, ht012b, ht123a, hbg2c]
                      ·
                        linarith only [hdelta1, h021, h340, ht234a, hbg2c]
                      ·
                        have hb0 := m.budget 0 (by decide) 4 3 2 1 (by decide)
                          (by linarith)
                          (by linarith)
                          (by linarith)
                        rcases hb0 with hbg0 | hbg0 | hbg0 | hbg0 |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ |
                          ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩ | ⟨hbg0a,hbg0b,hbg0c⟩
                        ·
                          linarith only [hdelta1, ht014b, ht023c, hbg2b, ht124b, hbg0]
                        ·
                          linarith only [hdelta1, ht023b, hbg2b, ht234c, hbg0]
                        ·
                          linarith only [hdelta1, h011, h340, ht023a, ht234a, hbg0]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 2 1 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc31, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h011, h340, ht012a, ht024a, hbg2c, hbg3]
                          ·
                            linarith only [hdelta1, h011, h340, ht013a, ht234a, hbg3]
                          ·
                            linarith only [hdelta1, ht023c, ht123b, hbg2b, ht234c, hbg3]
                          ·
                            linarith only [hdelta1, ht012a, ht034c, ht234a, hbg2a, hbg3, hbg0]
                          ·
                            linarith only [hdelta1, h011, h340, ht013a, hbg3c]
                          ·
                            linarith only [hdelta1, h011, h340, ht012a, ht023c, ht123b, ht234c, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht012a, ht034c, hbg3c, hbg2a, hbg0]
                          ·
                            linarith only [hdelta1, h011, h230, ht012a, ht023c, ht234c, hbg3c, hbg2c]
                          ·
                            linarith only [hdelta1, ht013b, ht234a, hbg3c]
                          ·
                            linarith only [hdelta1, ht123b, ht234a, hbg3c]
                        ·
                          linarith only [hdelta1, ht014b, hbg2b, ht124b, hbg0c]
                        ·
                          linarith only [hdelta1, h011, h340, ht012b, ht014b, ht023c, ht124b, ht234a, hbg0c, hbg2c]
                        ·
                          linarith only [hdelta1, ht012a, ht023c, ht234c, hbg0c, hbg2c]
                        ·
                          linarith only [hdelta1, h011, h340, ht013b, ht123b, ht234a, hbg0c]
                        ·
                          linarith only [hdelta1, ht012a, ht034c, ht234c, hbg0c, hbg2c]
                        ·
                          have hb3 := m.budget 3 (by decide) 4 2 1 0 (by decide)
                            (by linarith)
                            (by linarith)
                            (by linarith)
                          simp only [hc32, hc31, hc30] at hb3
                          rcases hb3 with hbg3 | hbg3 | hbg3 | hbg3 |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ |
                            ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩ | ⟨hbg3a,hbg3b,hbg3c⟩
                          ·
                            linarith only [hdelta1, h011, h340, ht012b, hbg3, hbg0a, hbg2a]
                          ·
                            linarith only [hdelta1, h011, h340, ht013b, ht023c, hbg3, ht234a, hbg0a]
                          ·
                            linarith only [hdelta1, h011, h130, ht023c, hbg3, hbg0a]
                          ·
                            linarith only [hdelta1, ht012b, ht034c, hbg3, ht234a, hbg0c, hbg2a]
                          ·
                            linarith only [hdelta1, h011, h340, ht013b, ht023c, hbg0a, hbg3c]
                          ·
                            linarith only [hdelta1, h011, h340, ht023c, ht123b, hbg0a, hbg3c]
                          ·
                            linarith only [hdelta1, ht012b, ht034c, hbg0c, hbg3c, hbg2a]
                          ·
                            linarith only [hdelta1, h011, h230, ht023c, hbg0a, hbg3c]
                          ·
                            linarith only [hdelta1, ht013b, ht234a, hbg3c]
                          ·
                            linarith only [hdelta1, ht123b, ht234a, hbg3c]
                      ·
                        linarith only [hdelta1, ht124a, hbg2c]

#print axioms model_impossible_1
end Jsp404.GlobalFiveLowTerminal
